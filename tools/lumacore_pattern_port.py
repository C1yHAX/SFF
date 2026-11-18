# SteaMidra - Steam game setup and manifest tool (SFF)
# Copyright (c) 2025-2026 Midrag (https://github.com/Midrags)
#
# This file is part of SteaMidra.
#
# SteaMidra is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
"""Port LumaCore pattern TOMLs onto a new Steam client build.

When Steam updates and no pattern TOML exists upstream for the new
steamclient64.dll / steamui.dll SHA-256, this re-locates every function
listed in a previous build's TOML inside the new DLL and writes
<out>/<new_sha>.toml, which is the LumaCore local pattern cache
(<Steam>/lumacore/pattern/).

Matching:
  * Candidates come from the old TOML signature and, when --old-dll is
    given, from 16-byte chunks of the old function body (so a changed
    prologue does not lose the function).
  * With --old-dll every candidate is scored by byte similarity against
    the old function body; the best one must clear a minimum score and
    beat the runner-up by a margin, otherwise the function is skipped.
  * Without --old-dll ambiguous hits are resolved by the RVA shift of
    neighbouring unique hits (less reliable).
  * If the old signature no longer matches at the new address, a new
    signature is built from the new bytes.

Unresolved functions are left out: LumaCore skips that hook instead of
hooking the wrong address.

Usage:
    python tools/lumacore_pattern_port.py --old OLD.toml --old-dll OLD.dll \
        --dll NEW.dll --out "C:/Program Files (x86)/Steam/lumacore/pattern"
"""
import argparse
import difflib
import hashlib
import re
import struct
import sys
from pathlib import Path

BODY = 256          # bytes of the old function compared against a candidate
CHUNK = 16          # chunk size for body-anchored candidate search
MIN_SCORE = 0.55    # min fraction of equal bytes for an accepted match
MIN_MARGIN = 0.12   # best must beat runner-up by this much
SIG_LEN = 24        # length of regenerated signatures
ALIGN_LEN = 128     # bytes compared by sequence alignment in the shift pass
SHIFT_WINDOW = 0x3000
SHIFT_MIN_SCORE = 0.70
SHIFT_MIN_MARGIN = 0.12
XREF_MIN_SCORE = 0.45
XREF_MIN_VOTES = 2
XREF_STRONG_VOTES = 5
CTX_BEFORE = 0x300
CTX_AFTER = 0x500
CTX_MIN_SCORE = 0.55
CTX_MIN_MARGIN = 0.05


def load_toml_entries(path: Path):
    entries, cur = [], None
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line.startswith("["):
            cur = {"key": line}
            entries.append(cur)
            continue
        m = re.match(r'(\w+)\s*=\s*"(.*)"', line)
        if m and cur is not None:
            cur[m.group(1)] = m.group(2)
    return [e for e in entries if {"name", "rva", "sig"} <= e.keys()]


class PE:
    def __init__(self, data: bytes):
        self.data = data
        pe = struct.unpack_from("<I", data, 0x3C)[0]
        if data[pe:pe + 4] != b"PE\0\0":
            raise ValueError("not a PE file")
        nsec = struct.unpack_from("<H", data, pe + 6)[0]
        opt = struct.unpack_from("<H", data, pe + 20)[0]
        self.sections = []
        for i in range(nsec):
            o = pe + 24 + opt + i * 40
            vsize, va, rawsize, rawptr = struct.unpack_from("<IIII", data, o + 8)
            chars = struct.unpack_from("<I", data, o + 36)[0]
            self.sections.append((va, vsize, rawptr, min(rawsize, vsize), bool(chars & 0x20000000)))

    def read(self, rva: int, n: int) -> bytes:
        for va, vsize, rawptr, rawsize, _ in self.sections:
            if va <= rva < va + rawsize:
                off = rawptr + rva - va
                return self.data[off:off + min(n, va + rawsize - rva)]
        return b""

    def exec_blobs(self):
        for va, vsize, rawptr, rawsize, ex in self.sections:
            if ex:
                yield va, self.data[rawptr:rawptr + rawsize]

    def search(self, rx: re.Pattern, limit=None):
        hits = []
        for va, blob in self.exec_blobs():
            for m in rx.finditer(blob) if rx.pattern else ():
                hits.append(va + m.start())
                if limit and len(hits) > limit:
                    return hits
        return hits


def sig_regex(sig: str) -> re.Pattern:
    parts = [b"." if t == "??" else re.escape(bytes([int(t, 16)])) for t in sig.replace(",", " ").split()]
    # lookahead so overlapping matches are reported
    return re.compile(b"(?=" + b"".join(parts) + b")", re.DOTALL)


def sig_matches(sig: str, blob: bytes) -> bool:
    toks = sig.replace(",", " ").split()
    if len(blob) < len(toks):
        return False
    return all(t == "??" or int(t, 16) == blob[i] for i, t in enumerate(toks))


def similarity(a: bytes, b: bytes) -> float:
    n = min(len(a), len(b))
    if n == 0:
        return 0.0
    return sum(1 for i in range(n) if a[i] == b[i]) / max(len(a), 1)


def build_sig(new: bytes, old: bytes | None, rva: int = 0) -> str:
    """Signature for the new function entry, built from the NEW bytes.

    Only fields that move with relocation are wildcarded: RIP-relative
    displacements and the rel8/rel32 targets of direct calls and jumps.
    Everything else stays concrete, so LumaCore's position-fixed byte check
    at the RVA keeps its meaning. Without capstone, bytes that differ from
    the old function are wildcarded instead (weaker)."""
    n = min(SIG_LEN, len(new))
    mask = [True] * n
    try:
        import capstone
        md = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
        md.detail = True
        for insn in md.disasm(new[:n + 16], rva):
            off = insn.address - rva
            if off >= n:
                break
            fields = []
            if insn.disp_size and "rip" in insn.op_str:
                fields.append((insn.disp_offset, insn.disp_size))
            is_branch = insn.group(capstone.CS_GRP_JUMP) or insn.group(capstone.CS_GRP_CALL)
            if is_branch and insn.imm_size and insn.op_str.startswith("0x"):
                fields.append((insn.imm_offset, insn.imm_size))
            for f_off, f_size in fields:
                for i in range(off + f_off, min(off + f_off + f_size, n)):
                    mask[i] = False
    except ImportError:
        for i in range(n):
            if old is not None and i < len(old) and old[i] != new[i]:
                mask[i] = False
    return " ".join(f"{new[i]:02X}" if mask[i] else "??" for i in range(n))


def port(old_toml: Path, new_pe: PE, old_pe: PE | None):
    entries = load_toml_entries(old_toml)
    try:
        old_funcs = Funcs(old_pe) if old_pe is not None else None
        new_funcs = Funcs(new_pe) if old_pe is not None else None
    except Exception:
        old_funcs = new_funcs = None
    sig_hits = {}
    for e in entries:
        e["old"] = int(e["rva"], 16)
        sig_hits[e["name"]] = new_pe.search(sig_regex(e["sig"]))

    anchors = sorted((e["old"], sig_hits[e["name"]][0] - e["old"])
                     for e in entries if len(sig_hits[e["name"]]) == 1)

    def near_shift(rva):
        return min(anchors, key=lambda a: abs(a[0] - rva))[1] if anchors else None

    results = []
    for e in entries:
        hits = sig_hits[e["name"]]
        new, how, old_body = None, "", None

        if old_pe is not None:
            old_body = old_pe.read(e["old"], BODY)
            if not sig_matches(e["sig"], old_body):
                e["old_body"] = None
                results.append([e, None, "old TOML sig does not match old DLL"])
                continue
            cands = set(hits)
            for k in range(0, min(len(old_body), 160) - CHUNK + 1, 8):
                rx = re.compile(b"(?=" + re.escape(old_body[k:k + CHUNK]) + b")", re.DOTALL)
                found = new_pe.search(rx, limit=4)
                if 0 < len(found) <= 4:
                    cands.update(f - k for f in found)
            if new_funcs is not None and old_funcs is not None and e["old"] in old_funcs.starts:
                # a real function entry must map onto a real function entry
                cands = {c for c in cands if c in new_funcs.starts}
            scored = sorted(((similarity(old_body, new_pe.read(c, BODY)), c) for c in cands), reverse=True)
            if not scored:
                how = "no candidates"
            else:
                best, c = scored[0]
                second = scored[1][0] if len(scored) > 1 else 0.0
                if best >= MIN_SCORE and best - second >= MIN_MARGIN:
                    new, how = c, f"score {best:.2f} (next {second:.2f}, {len(scored)} cand)"
                else:
                    how = f"rejected: best {best:.2f}, next {second:.2f}, {len(scored)} cand"
        else:
            if len(hits) == 1:
                new, how = hits[0], "unique sig"
            elif hits and near_shift(e["old"]) is not None:
                target = e["old"] + near_shift(e["old"])
                c = min(hits, key=lambda h: abs(h - target))
                if abs(c - target) <= 0x40000:
                    new, how = c, f"nearest of {len(hits)}"
                else:
                    how = f"ambiguous ({len(hits)} hits)"
            else:
                how = f"ambiguous ({len(hits)} hits)" if hits else "sig not found"

        e["old_body"] = old_body
        e["_old_pe"] = old_pe
        e["_old_funcs"] = old_funcs
        e["_new_funcs"] = new_funcs
        results.append([e, new, how])

    if old_pe is not None:
        _shift_pass(results, new_pe)
        _xref_pass(results, old_pe, new_pe)

    _drop_conflicts(results)

    for r in results:
        e, new = r[0], r[1]
        if new is None:
            continue
        new_bytes = new_pe.read(new, BODY)
        if sig_matches(e["sig"], new_bytes):
            e["new_sig"] = e["sig"]
        else:
            e["new_sig"] = build_sig(new_bytes, e["old_body"], new)
            r[2] += ", new sig"
    return results


def _drop_conflicts(results):
    """Two different old functions must never land on one new address."""
    by_new = {}
    for r in results:
        if r[1] is not None:
            by_new.setdefault(r[1], []).append(r)
    for new, rs in by_new.items():
        olds = {r[0]["old"] for r in rs}
        if len(olds) <= 1:
            continue
        # keep the first-pass (signature) match if exactly one exists
        keep = [r for r in rs if r[2].startswith("score")]
        for r in rs:
            if len(keep) == 1 and r is keep[0]:
                continue
            r[1] = None
            r[2] += f"; dropped: {new:#x} also claimed by another function"


def _align_score(old: bytes, new: bytes) -> float:
    return difflib.SequenceMatcher(None, old[:ALIGN_LEN], new[:ALIGN_LEN], autojunk=False).ratio()


def _shift_pass(results, new_pe: PE):
    """Second pass: locate unresolved functions via the RVA shift of the
    nearest confidently resolved neighbours. Code inside one region of the
    DLL moves as a block between builds, so the old RVA plus the local
    shift lands on or very near the function."""
    anchors = sorted((e["old"], new - e["old"]) for e, new, _ in results if new is not None)
    if not anchors:
        return
    for r in results:
        e, new, how = r
        if new is not None or e["old_body"] is None or how.startswith("old TOML"):
            continue
        left = [a for a in anchors if a[0] <= e["old"]]
        right = [a for a in anchors if a[0] > e["old"]]
        shifts = {s for s in ((left[-1][1] if left else None), (right[0][1] if right else None)) if s is not None}
        expected = sorted(e["old"] + s for s in shifts)
        if not expected:
            continue
        cands = set()
        for x in expected:
            base = (x - SHIFT_WINDOW) & ~0xF
            cands.update(range(base, x + SHIFT_WINDOW, 0x10))
            cands.add(x)
        ofn_, nfn_ = e.get("_old_funcs"), e.get("_new_funcs")
        if ofn_ is not None and nfn_ is not None and e["old"] in ofn_.starts:
            cands = {c for c in cands if c in nfn_.starts}
        scored = []
        for c in cands:
            nb = new_pe.read(c, ALIGN_LEN)
            if len(nb) < ALIGN_LEN or nb[0] != e["old_body"][0]:
                continue  # first opcode byte nearly always survives a rebuild
            scored.append((_align_score(e["old_body"], nb), c))
        scored.sort(reverse=True)
        if not scored:
            r[2] = how + "; shift pass: no candidates"
            continue
        best, c = scored[0]
        second = scored[1][0] if len(scored) > 1 else 0.0
        dist = min(abs(c - x) for x in expected)
        if (best >= SHIFT_MIN_SCORE and best - second >= SHIFT_MIN_MARGIN) or                 (best >= 0.6 and best - second >= 0.25):
            r[1] = c
            r[2] = f"shift pass: align {best:.2f} (next {second:.2f}), {dist:#x} from expected"
            continue
        # Twins: the neighbouring look-alike functions keep their relative
        # layout across builds. Pick the candidate whose surroundings
        # reproduce the old twin offsets.
        if best >= SHIFT_MIN_SCORE and e.get("_old_funcs") is not None:
            ofn, body = e["_old_funcs"], e["old_body"]
            old_tw = [x for x in ofn.starts if x != e["old"] and abs(x - e["old"]) <= SHIFT_WINDOW
                      and _align_score(body, e["_old_pe"].read(x, ALIGN_LEN)) >= 0.7]
            new_tw = [c for s_, c in scored if s_ >= 0.7]
            tied = [c for s_, c in scored if s_ >= best - 0.06]
            if old_tw and len(tied) > 1:
                def layout(c):
                    return sum(1 for x in old_tw
                               if any(abs((y - c) - (x - e["old"])) <= 0x40 for y in new_tw))
                lay = sorted(((layout(c), c) for c in tied), reverse=True)
                if lay[0][0] >= 2 and lay[0][0] >= len(old_tw) * 0.6 and lay[0][0] > lay[1][0]:
                    r[1] = lay[0][1]
                    r[2] = (f"shift pass: align {best:.2f}, twin layout {lay[0][0]}/{len(old_tw)} "
                            f"(next {lay[1][0]})")
                    continue
                how += f"; twin layout {lay[0][0]} vs {lay[1][0]} of {len(old_tw)}"
        # Near-identical twins (same template, sibling wrappers): compare a
        # wider window that includes the neighbouring functions.
        if best >= SHIFT_MIN_SCORE:
            tied = [c for s, c in scored[:8] if s >= best - 0.06]
            ctx = sorted(((_context_score(e["_old_pe"], e["old"], new_pe, c), c) for c in tied), reverse=True)
            if len(ctx) > 1 and ctx[0][0] >= CTX_MIN_SCORE and ctx[0][0] - ctx[1][0] >= CTX_MIN_MARGIN:
                r[1] = ctx[0][1]
                r[2] = (f"shift pass: align {best:.2f}, context {ctx[0][0]:.2f} vs {ctx[1][0]:.2f} "
                        f"({len(tied)} twins)")
                continue
            if ctx:
                how += f"; context {ctx[0][0]:.2f} vs {ctx[1][0] if len(ctx) > 1 else 0:.2f}"
        r[2] = how + f"; shift pass rejected: align {best:.2f}, next {second:.2f}"


def _context_score(old_pe: PE, old_rva: int, new_pe: PE, new_rva: int) -> float:
    ob = old_pe.read(old_rva - CTX_BEFORE, CTX_BEFORE + CTX_AFTER)
    nb = new_pe.read(new_rva - CTX_BEFORE, CTX_BEFORE + CTX_AFTER)
    return difflib.SequenceMatcher(None, ob, nb, autojunk=False).ratio()


# ── Xref pass (needs capstone) ───────────────────────────────────────────

_RIP_RE = re.compile(r"\[rip ([+-]) (0x[0-9a-f]+|\d+)\]")
_LEA_RIP = re.compile(rb"(?=[\x48\x4c]\x8d[\x05\x0d\x15\x1d\x25\x2d\x35\x3d])", re.DOTALL)
_CALL = re.compile(rb"(?=\xe8)", re.DOTALL)


class Code:
    """Thin capstone wrapper plus raw call / rip-lea indexes for a PE."""

    def __init__(self, pe: PE):
        import capstone
        self.pe = pe
        self.md = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
        self._callers = None
        self._lea_refs = None
        self._feat_cache = {}

    def features(self, rva: int, maxlen: int = 0x2000):
        """Ordered (kind, offset_in_func, target) for call / rip refs."""
        if rva in self._feat_cache:
            return self._feat_cache[rva]
        blob = self.pe.read(rva, maxlen)
        feats = []
        for addr, size, mnem, ops in self.md.disasm_lite(blob, rva):
            if mnem == "int3":
                break
            if mnem in ("call", "jmp") and ops.startswith("0x"):
                feats.append(("call" if mnem == "call" else "jmp", addr - rva, int(ops, 16)))
            else:
                m = _RIP_RE.search(ops)
                if m:
                    disp = int(m.group(2), 0) * (1 if m.group(1) == "+" else -1)
                    feats.append(("rip", addr - rva, addr + size + disp))
            if mnem == "ret":
                nxt = blob[addr - rva + size: addr - rva + size + 1]
                if nxt in (b"\xcc", b""):
                    break
        self._feat_cache[rva] = feats
        return feats

    def _index(self):
        callers, leas = {}, {}
        for va, blob in self.pe.exec_blobs():
            n = len(blob)
            for m in _CALL.finditer(blob):
                p = m.start()
                if p + 5 <= n:
                    t = va + p + 5 + struct.unpack_from("<i", blob, p + 1)[0]
                    callers.setdefault(t, []).append(va + p)
            for m in _LEA_RIP.finditer(blob):
                p = m.start()
                if p + 7 <= n:
                    t = va + p + 7 + struct.unpack_from("<i", blob, p + 3)[0]
                    leas.setdefault(t, []).append(va + p)
        self._callers, self._lea_refs = callers, leas

    def callers(self, t):
        if self._callers is None:
            self._index()
        return self._callers.get(t, [])

    def lea_refs(self, t):
        if self._lea_refs is None:
            self._index()
        return self._lea_refs.get(t, [])

    def cstring(self, rva: int):
        b = self.pe.read(rva, 256)
        end = b.find(b"\0")
        if end < 6:
            return None
        s = b[:end]
        if all(32 <= c < 127 for c in s):
            return s + b"\0"
        return None


def _find_data(pe: PE, needle: bytes):
    hits = []
    for va, vsize, rawptr, rawsize, ex in pe.sections:
        if ex:
            continue
        blob = pe.data[rawptr:rawptr + rawsize]
        i = blob.find(needle)
        while i != -1:
            hits.append(va + i)
            if len(hits) > 3:
                return hits
            i = blob.find(needle, i + 1)
    return hits


def _build_func_map(results, oc: Code, nc: Code, old_pe: PE, new_pe: PE, ofn=None, nfn=None, rounds=5):
    """old function rva -> new rva, grown from the resolved anchors by
    pairing the call lists of matched functions (callees) and by matching
    the functions that call a matched function (callers)."""
    fmap = {e["old"]: new for e, new, _ in results if new is not None}
    frontier = dict(fmap)
    for _ in range(rounds):
        added = {}
        for o, n in frontier.items():
            for _off, to, tn in _pair_calls(oc, nc, old_pe, new_pe, o, n):
                if to not in fmap and to not in added:
                    added[to] = tn
            if ofn is None:
                continue
            po = {ofn.func_of(x) for x in oc.callers(o)} - {None}
            pn = {nfn.func_of(x) for x in nc.callers(n)} - {None}
            if not po or not pn or len(po) > 6 or len(pn) > 6:
                continue
            for p_old in po:
                if p_old in fmap or p_old in added:
                    continue
                ob = old_pe.read(p_old, ALIGN_LEN)
                sc = sorted(((_align_score(ob, new_pe.read(c, ALIGN_LEN)), c) for c in pn), reverse=True)
                if sc and sc[0][0] >= 0.6 and (len(sc) == 1 or sc[0][0] - sc[1][0] >= 0.15):
                    added[p_old] = sc[0][1]
        fmap.update(added)
        frontier = added
        if not added:
            break
    return fmap


def _image_base(pe: PE) -> int:
    off = struct.unpack_from("<I", pe.data, 0x3C)[0]
    return struct.unpack_from("<Q", pe.data, off + 24 + 24)[0]


def _qword_hits(pe: PE, value: int, limit=6):
    needle = struct.pack("<Q", value)
    hits = []
    for va, vsize, rawptr, rawsize, ex in pe.sections:
        if ex:
            continue
        blob = pe.data[rawptr:rawptr + rawsize]
        i = blob.find(needle)
        while i != -1:
            if i % 8 == 0:
                hits.append(va + i)
                if len(hits) > limit:
                    return hits
            i = blob.find(needle, i + 1)
    return hits


def _read_q(pe: PE, rva: int):
    b = pe.read(rva, 8)
    return struct.unpack("<Q", b)[0] if len(b) == 8 else None


def _vtable_votes(old_rva: int, fmap: dict, old_pe: PE, new_pe: PE, span=24):
    """Map a function through the pointer tables that hold it: find a
    neighbouring slot whose function is already mapped, locate that new
    pointer in the new image, and read the corresponding slot there."""
    ob, nb = _image_base(old_pe), _image_base(new_pe)
    votes = {}
    for loc in _qword_hits(old_pe, ob + old_rva):
        seen = set()
        for k in range(-span, span + 1):
            if k == 0:
                continue
            p = _read_q(old_pe, loc + 8 * k)
            if p is None or not ob <= p < ob + 0x8000000:
                continue
            mapped = fmap.get(p - ob)
            if mapped is None:
                continue
            # shared stubs (purecall, nullsubs) sit in many tables: useless
            if len(_qword_hits(old_pe, p, limit=2)) > 2:
                continue
            nhits = _qword_hits(new_pe, nb + mapped, limit=2)
            if len(nhits) > 2:
                continue
            for nloc in nhits:
                slot = nloc - 8 * k
                q = _read_q(new_pe, slot)
                if q is None or not nb <= q < nb + 0x8000000 or slot in seen:
                    continue
                seen.add(slot)
                votes[q - nb] = votes.get(q - nb, 0) + 1
    return votes


def _rtti_name(pe: PE, col_rva: int):
    """Class name from an x64 MSVC CompleteObjectLocator (signature 1)."""
    hdr = pe.read(col_rva, 24)
    if len(hdr) < 24:
        return None, None
    sig, offset, _cd, td, _chd, self_rva = struct.unpack("<IIIIII", hdr)
    if sig != 1 or self_rva != col_rva:
        return None, None
    name = pe.read(td + 16, 256)
    end = name.find(b"\0")
    if end <= 4 or not name.startswith(b".?A"):
        return None, None
    return name[:end + 1], offset


def _rtti_votes(old_rva: int, old_pe: PE, new_pe: PE):
    """Find the vtables holding old_rva, identify their class through RTTI,
    and read the same slot of that class's vtable in the new image."""
    ob, nb = _image_base(old_pe), _image_base(new_pe)
    votes = {}
    for loc in _qword_hits(old_pe, ob + old_rva):
        start = loc
        for _ in range(512):   # walk back to the first slot (preceded by the COL)
            q = _read_q(old_pe, start - 8)
            name, offset = (_rtti_name(old_pe, q - ob) if q and q > ob else (None, None))
            if name:
                break
            start -= 8
        else:
            continue
        if not name:
            continue
        slot = (loc - start) // 8
        for nloc in _find_data(new_pe, name):
            td = nloc - 16
            needle = struct.pack("<I", td)
            for va, vsize, rawptr, rawsize, ex in new_pe.sections:
                if ex:
                    continue
                blob = new_pe.data[rawptr:rawptr + rawsize]
                i = blob.find(needle)
                while i != -1:
                    col = va + i - 12
                    nname, noff = _rtti_name(new_pe, col)
                    if nname == name and noff == offset:
                        for vt in _qword_hits(new_pe, nb + col):
                            q = _read_q(new_pe, vt + 8 + slot * 8)
                            if q and nb <= q < nb + 0x8000000:
                                votes[q - nb] = votes.get(q - nb, 0) + 5
                    i = blob.find(needle, i + 1)
    return votes


class Funcs:
    """Function boundaries from the x64 exception directory (.pdata).
    Chained unwind entries are folded into their primary function."""

    def __init__(self, pe: PE):
        import bisect
        self._bisect = bisect
        d = pe.data
        off = struct.unpack_from("<I", d, 0x3C)[0]
        opt = off + 24
        exc_rva, exc_size = struct.unpack_from("<II", d, opt + 112 + 3 * 8)
        raw = pe.read(exc_rva, exc_size)
        entries = []
        for i in range(0, len(raw) - 11, 12):
            b, e, u = struct.unpack_from("<III", raw, i)
            if b:
                entries.append((b, e, u))
        primary = {}
        by_begin = {b: (b, e, u) for b, e, u in entries}
        for b, e, u in entries:
            root, seen = b, 0
            cur_u = u
            while seen < 16:
                hdr = pe.read(cur_u & ~1, 4)
                if len(hdr) < 4 or not (hdr[0] >> 3) & 0x4:   # UNW_FLAG_CHAININFO
                    break
                n = hdr[2]
                chain = pe.read((cur_u & ~1) + 4 + ((n + 1) & ~1) * 2, 12)
                if len(chain) < 12:
                    break
                root, _, cur_u = struct.unpack("<III", chain)
                seen += 1
            primary[b] = root
        self.begins = sorted(primary)
        self.primary = primary
        self.starts = set(primary.values())

    def func_of(self, rva: int):
        i = self._bisect.bisect_right(self.begins, rva) - 1
        if i < 0:
            return None
        return self.primary[self.begins[i]]


def _pair_calls(oc: Code, nc: Code, old_pe: PE, new_pe: PE, o: int, n: int):
    """Pair the call targets of old function o with those of new function n."""
    fo = [f for f in oc.features(o) if f[0] in ("call", "jmp")]
    fn = [f for f in nc.features(n) if f[0] in ("call", "jmp")]
    if not fo or not fn:
        return []
    ko = [old_pe.read(f[2], 8) for f in fo]
    kn = [new_pe.read(f[2], 8) for f in fn]
    sm = difflib.SequenceMatcher(None, ko, kn, autojunk=False)
    out = []
    for a, b, size in sm.get_matching_blocks():
        for i in range(size):
            out.append((fo[a + i][1], fo[a + i][2], fn[b + i][2]))
    return out


def _map_by_shift(old_rva, fmap_sorted, old_pe: PE, new_pe: PE, nfn, window=0x1000):
    """Map an arbitrary old function through the shift of its closest
    already-mapped neighbour plus an alignment check."""
    import bisect
    if not fmap_sorted:
        return None
    keys = [k for k, _ in fmap_sorted]
    i = bisect.bisect_left(keys, old_rva)
    near = [fmap_sorted[j] for j in (i - 1, i) if 0 <= j < len(fmap_sorted)]
    o, n = min(near, key=lambda kv: abs(kv[0] - old_rva))
    expected = old_rva + (n - o)
    body = old_pe.read(old_rva, ALIGN_LEN)
    lo = bisect.bisect_left(nfn.begins, expected - window)
    hi = bisect.bisect_right(nfn.begins, expected + window)
    cands = {nfn.primary[b] for b in nfn.begins[lo:hi]}
    sc = sorted(((_align_score(body, new_pe.read(c, ALIGN_LEN)), c) for c in cands), reverse=True)
    if sc and sc[0][0] >= 0.75 and (len(sc) == 1 or sc[0][0] - sc[1][0] >= 0.1):
        return sc[0][1]
    return None


def _xref_pass(results, old_pe: PE, new_pe: PE):
    try:
        oc, nc = Code(old_pe), Code(new_pe)
    except ImportError:
        return
    ofn, nfn = Funcs(old_pe), Funcs(new_pe)
    fmap = _build_func_map(results, oc, nc, old_pe, new_pe, ofn, nfn)
    fmap_sorted = sorted(fmap.items())
    for r in results:
        e, new, how = r
        if new is not None or e["old_body"] is None or how.startswith("old TOML"):
            continue
        votes = {}

        def vote(c, w, why):
            if c is None or c not in nfn.starts:
                return
            votes.setdefault(c, [0, set()])
            votes[c][0] += w
            votes[c][1].add(why)

        # 1) a matched function calls this one at the same position
        if e["old"] in fmap:
            vote(fmap[e["old"]], 3, "callee-map")
        # 2) vtable / function-pointer tables
        for c, v in _vtable_votes(e["old"], fmap, old_pe, new_pe).items():
            vote(c, v, "vtable")
        for c, v in _rtti_votes(e["old"], old_pe, new_pe).items():
            vote(c, v, "rtti")
        # 3) old callers -> their new counterpart -> call at same position
        for site in oc.callers(e["old"])[:16]:
            po = ofn.func_of(site)
            if po is None or po == e["old"]:
                continue
            pn = fmap.get(po)
            if pn is None:
                pn = _map_by_shift(po, fmap_sorted, old_pe, new_pe, nfn)
            if pn is None:
                continue
            paired = [tn for off, to, tn in _pair_calls(oc, nc, old_pe, new_pe, po, pn) if to == e["old"]]
            if not paired:
                # prologue of the target changed, so the key-based pairing
                # missed it: fall back to the call at the same offset
                site_off = site - po
                ocalls = [f for f in oc.features(po) if f[0] == "call"]
                ncalls = [f for f in nc.features(pn) if f[0] == "call"]
                idx = [i for i, f in enumerate(ocalls) if f[1] == site_off]
                if idx and len(ocalls) == len(ncalls):
                    nf_ = ncalls[idx[0]]
                    if abs(nf_[1] - site_off) <= 0x20:
                        paired = [nf_[2]]
            for tn in paired:
                vote(tn, 2, "caller")
        # 4) what the old function references: unique strings, mapped callees
        for kind, off, tgt in oc.features(e["old"]):
            weight = 1
            if kind == "rip":
                s = oc.cstring(tgt)
                if s is None:
                    continue
                locs = _find_data(new_pe, s)
                if len(locs) != 1:
                    continue
                sites = nc.lea_refs(locs[0])
                why = "string"
                old_locs = _find_data(old_pe, s)
                old_sites = oc.lea_refs(old_locs[0]) if len(old_locs) == 1 else []
                old_funcs = {ofn.func_of(x) for x in old_sites}
                new_funcs = {nfn.func_of(x) for x in sites}
                if old_funcs == {e["old"]} and len(new_funcs) == 1:
                    weight, why = 5, "unique-string"   # string used only by this function
            elif kind == "call" and tgt in fmap:
                sites = nc.callers(fmap[tgt])
                why = "callee"
            else:
                continue
            if len(sites) > 6:
                # busy callee/string: keep only sites at the same offset in their function
                sites = [x for x in sites if nfn.func_of(x) is not None
                         and abs((x - nfn.func_of(x)) - off) <= 0x10]
                why += "@offset"
            if not sites or len(sites) > 6:
                continue
            for c in {nfn.func_of(x) for x in sites}:
                vote(c, weight, why)

        if not votes:
            r[2] = how + "; xref: no evidence"
            continue
        ranked = sorted(votes.items(), key=lambda kv: -kv[1][0])
        (c, (top, whys)) = ranked[0]
        second = ranked[1][1][0] if len(ranked) > 1 else 0
        score = _align_score(e["old_body"], new_pe.read(c, ALIGN_LEN))
        if top >= XREF_MIN_VOTES and top >= 2 * second and (score >= XREF_MIN_SCORE or top >= XREF_STRONG_VOTES):
            r[1] = c
            r[2] = f"xref pass: {top} votes ({'+'.join(sorted(whys))}), next {second}, align {score:.2f}"
        else:
            r[2] = how + f"; xref rejected: {top} votes vs {second}, align {score:.2f}"


def write_toml(path: Path, results, source: str):
    lines = [f"# ported by tools/lumacore_pattern_port.py from {source}", ""]
    for e, new, _ in sorted((r for r in results if r[1] is not None), key=lambda r: r[0]["name"]):
        lines += [e["key"], f'name = "{e["name"]}"', f'rva = "0x{new:X}"', f'sig = "{e["new_sig"]}"', ""]
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".toml.tmp")
    tmp.write_text("\n".join(lines), encoding="utf-8", newline="\n")
    tmp.replace(path)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--old", required=True, type=Path, help="previous build's pattern TOML")
    ap.add_argument("--old-dll", type=Path, help="DLL the old TOML belongs to (strongly recommended)")
    ap.add_argument("--dll", required=True, type=Path, help="new steamclient64.dll or steamui.dll")
    ap.add_argument("--out", type=Path, help="output dir, e.g. <Steam>/lumacore/pattern")
    args = ap.parse_args()

    new_data = args.dll.read_bytes()
    sha = hashlib.sha256(new_data).hexdigest()
    old_pe = PE(args.old_dll.read_bytes()) if args.old_dll else None
    results = port(args.old, PE(new_data), old_pe)

    ok = 0
    for e, new, how in results:
        ok += new is not None
        tag = "OK  " if new is not None else "MISS"
        print(f"  {tag} {e['name']:40s} {e['old']:#10x} -> {(f'{new:#x}' if new is not None else '-'):>10s}  {how}")
    print(f"{args.dll.name}: {ok}/{len(results)} resolved, sha256={sha}")

    if args.out and ok:
        dest = args.out / f"{sha}.toml"
        write_toml(dest, results, args.old.name)
        print(f"wrote {dest}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
