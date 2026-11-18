# SteaMidra - Steam game setup and manifest tool (SFF)
# Copyright (c) 2025-2026 Midrag (https://github.com/Midrags)
#
# This file is part of SteaMidra.
#
# SteaMidra is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
"""Port a LumaCore IPC spec (lumacore/pattern/steamclientipc/<sha>.toml) onto
a new steamclient64.dll.

Valve re-hashes IPC methods between client builds, so the funcHash / fencepost
in the spec go stale. For each method this reads the current values back out of
the DLL two independent ways and requires both to agree:

  name route : the method-name string -> the function that references it and
               serialises the IPC call (stores funcHash, the arguments, then
               the fencepost); its stored hash must also be compared in a
               dispatcher.
  vtable route: that function must sit at the derived slot of the method's
               I<Interface>Map vtable (located via RTTI).

With --old-spec/--old-dll it first reproduces the known old values as a
self-test and aborts on any mismatch, so a rule that has drifted is caught
before the new file is written. Needs the `capstone` package.

Only the interfaces LumaCore actually resolves through the spec are emitted
(IClientUser, IClientUtils). IClientRemoteStorage is intentionally omitted:
its hooks use compile-time hashes and are never looked up through the spec.

Usage:
    python tools/lumacore_ipc_port.py --old-spec OLD.toml --old-dll OLD/steamclient64.dll \\
        --dll "<Steam>/steamclient64.dll" --out "<Steam>/lumacore/pattern/steamclientipc"
"""
import argparse
import hashlib
import re
import struct
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lumacore_pattern_port as L  # noqa: E402

NUL = bytes([0])
_STORE = re.compile(r"^(?:dword ptr \[[^\]]+\]), (0x[0-9a-f]+)$")

# interface id, RTTI map-class core, methods LumaCore resolves through the spec
INTERFACES = [
    (1, "IClientUser", "IClientUserMap",
     ["GetSteamID", "GetAppOwnershipTicketExtendedData",
      "RequestEncryptedAppTicket", "GetEncryptedAppTicket"]),
    (4, "IClientUtils", "IClientUtilsMap",
     ["GetAppID", "GetAPICallResult"]),
]


class Image:
    def __init__(self, data: bytes):
        import capstone
        self.pe = L.PE(data)
        self.code = L.Code(self.pe)
        self.funcs = L.Funcs(self.pe)
        self.base = L._image_base(self.pe)
        self.md = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
        d = self.pe.data
        off = struct.unpack_from("<I", d, 0x3C)[0]
        exc_rva, exc_size = struct.unpack_from("<II", d, off + 24 + 112 + 3 * 8)
        raw = self.pe.read(exc_rva, exc_size)
        self._ranges = {}
        for i in range(0, len(raw) - 11, 12):
            b, e, _u = struct.unpack_from("<III", raw, i)
            if b:
                self._ranges.setdefault(self.funcs.primary.get(b, b), []).append((b, e))
        self._ic = {}

    def insns(self, func):
        if func in self._ic:
            return self._ic[func]
        out = []
        for b, e in sorted(self._ranges.get(func, []) or [(func, func + 0x1200)]):
            out += list(self.md.disasm_lite(self.pe.read(b, e - b), b))
        out.sort()
        self._ic[func] = out
        return out

    def name_ref_funcs(self, name):
        needle = NUL + name.encode() + NUL
        out = set()
        for loc in (x + 1 for x in L._find_data(self.pe, needle)):
            for site in self.code.lea_refs(loc):
                f = self.funcs.func_of(site)
                if f is not None:
                    out.add(f)
        return out

    def cmp_funcs(self, value):
        needle = struct.pack("<I", value)
        out = set()
        for va, blob in self.pe.exec_blobs():
            i = blob.find(needle)
            while i != -1:
                f = self.funcs.func_of(va + i)
                if f is not None:
                    for a, s, m, o in self.insns(f):
                        if a <= va + i < a + s and m == "cmp" and o.endswith(f"{value:#x}"):
                            out.add(f)
                            break
                i = blob.find(needle, i + 1)
        return out

    def rtti_classes(self, func):
        out = []
        for loc in L._qword_hits(self.pe, self.base + func, limit=16):
            start = loc
            for _ in range(4096):
                q = L._read_q(self.pe, start - 8)
                if q and q > self.base:
                    cn, off = L._rtti_name(self.pe, q - self.base)
                    if cn:
                        out.append((cn[:-1].decode(errors="replace"), (loc - start) // 8))
                        break
                start -= 8
        return out

    def class_primary_vtables(self, cls_core):
        needle = cls_core.encode()
        out, seen = [], set()
        for va, _vs, rp, rs, ex in self.pe.sections:
            if ex:
                continue
            blob = self.pe.data[rp:rp + rs]
            i = blob.find(b".?AV")
            while i != -1:
                nm = blob[i:blob.find(NUL, i)]
                if needle in nm and nm not in seen:
                    seen.add(nm)
                    nd = struct.pack("<I", va + i - 16)
                    for va2, _v2, rp2, rs2, ex2 in self.pe.sections:
                        if ex2:
                            continue
                        b2 = self.pe.data[rp2:rp2 + rs2]
                        j = b2.find(nd)
                        while j != -1:
                            col = va2 + j - 12
                            cn, coff = L._rtti_name(self.pe, col)
                            if cn == nm + NUL and coff == 0:
                                out += [vt + 8 for vt in L._qword_hits(self.pe, self.base + col)]
                            j = b2.find(nd, j + 1)
                i = blob.find(b".?AV", i + 1)
        return sorted(set(out))

    def slot_func(self, vt, slot):
        q = L._read_q(self.pe, vt + 8 * slot)
        return (q - self.base) if q and q > self.base else None


def wrapper_values(img, func, cls_core):
    stores, calls = [], []
    for k, (_a, _s, m, o) in enumerate(img.insns(func)):
        if m == "mov":
            mm = _STORE.match(o)
            if mm and int(mm.group(1), 16) >= 0x10000:
                stores.append((k, int(mm.group(1), 16)))
        elif m == "call":
            calls.append(k)
    if len(stores) < 2:
        return None
    hk, func_hash = stores[0]
    fk, fencepost = stores[1]
    argc = max(0, sum(1 for c in calls if hk < c < fk) - 1)
    idx = None
    for cn, slot in img.rtti_classes(func):
        if cls_core in cn:
            idx = slot
    return {"wrapper": func, "funcHash": func_hash, "fencepost": fencepost, "argc": argc, "slot": idx}


def derive(img, cls_core, method):
    """Return the single cross-checked record for method, or (None, reason)."""
    cands = []
    for f in sorted(img.name_ref_funcs(method)):
        classes = {c for c, _ in img.rtti_classes(f)}
        if not any(cls_core in c for c in classes):
            continue
        v = wrapper_values(img, f, cls_core)
        if v and img.cmp_funcs(v["funcHash"]):
            cands.append(v)
    if len(cands) != 1:
        return None, f"name route: {len(cands)} wrapper candidates"
    rec = cands[0]
    vts = img.class_primary_vtables(cls_core)
    if not any(img.slot_func(vt, rec["slot"]) == rec["wrapper"] for vt in vts):
        return None, f"vtable route disagrees (slot {rec['slot']})"
    rec["vtable"] = vts[0] if vts else None
    return rec, None


def load_spec_hashes(path):
    data = tomllib.loads(path.read_text(encoding="utf-8"))
    out = {}
    for iface, tbl in data.items():
        if isinstance(tbl, dict):
            for meth, mv in tbl.items():
                if isinstance(mv, dict) and "funcHash" in mv:
                    out[(iface, meth)] = int(mv["funcHash"], 16)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--old-spec", type=Path, help="previous steamclientipc TOML (for the self-test)")
    ap.add_argument("--old-dll", type=Path, help="steamclient64.dll the old spec belongs to")
    ap.add_argument("--dll", required=True, type=Path, help="new steamclient64.dll")
    ap.add_argument("--out", type=Path, help="output dir, e.g. <Steam>/lumacore/pattern/steamclientipc")
    args = ap.parse_args()

    old = Image(args.old_dll.read_bytes()) if args.old_dll else None
    old_hashes = load_spec_hashes(args.old_spec) if args.old_spec else {}
    new_data = args.dll.read_bytes()
    new = Image(new_data)
    sha = hashlib.sha256(new_data).hexdigest()

    ok, out = True, []
    for iface_id, iface, cls_core, methods in INTERFACES:
        emitted = []
        for method in methods:
            if old is not None:
                od, err = derive(old, cls_core, method)
                if err:
                    print(f"  SELFTEST FAIL {iface}.{method}: {err}")
                    ok = False
                    continue
                want = old_hashes.get((iface, method))
                if want is not None and od["funcHash"] != want:
                    print(f"  SELFTEST FAIL {iface}.{method}: derived {od['funcHash']:#010x} "
                          f"!= spec {want:#010x}")
                    ok = False
                    continue
            nd, err = derive(new, cls_core, method)
            if err:
                print(f"  FAIL {iface}.{method}: {err}")
                ok = False
                continue
            extra = ""
            if old is not None and not err:
                extra = f" (old {od['funcHash']:#010x}, argc {od['argc']}->{nd['argc']})"
                if od["argc"] != nd["argc"]:
                    print(f"  FAIL {iface}.{method}: argc changed {od['argc']} -> {nd['argc']}")
                    ok = False
                    continue
            print(f"  OK   {iface}.{method}: funcHash={nd['funcHash']:#010x} "
                  f"fencepost={nd['fencepost']:#010x} argc={nd['argc']} slot={nd['slot']} "
                  f"wrapper={nd['wrapper']:#x}{extra}")
            emitted.append((method, nd))
        if emitted:
            out.append((iface_id, iface, emitted))

    if not ok:
        print("aborted: at least one method failed, nothing written")
        return 1

    lines = [f"# ported by tools/lumacore_ipc_port.py from {args.dll.name}", ""]
    for iface_id, iface, emitted in out:
        vt = emitted[0][1]["vtable"]
        lines += [f"[{iface}]", f"interface_id = {iface_id}", f'vtable_rva = "0x{vt:X}"', ""]
        for method, nd in emitted:
            lines += [f"[{iface}.{method}]", f"method_index = {nd['slot']}",
                      f'funcHash = "0x{nd["funcHash"]:08X}"', f'wrapper_rva = "0x{nd["wrapper"]:X}"',
                      f'fencepost = "0x{nd["fencepost"]:08X}"', f"argc = {nd['argc']}", ""]
    body = "\n".join(lines)
    tomllib.loads(body)  # must parse
    nmeth = sum(len(e) for _i, _n, e in out)
    print(f"{args.dll.name}: {nmeth} methods across {len(out)} interfaces, sha256={sha}")
    if args.out:
        args.out.mkdir(parents=True, exist_ok=True)
        dest = args.out / f"{sha}.toml"
        tmp = dest.with_suffix(".toml.tmp")
        tmp.write_text(body, encoding="utf-8", newline="\n")
        tmp.replace(dest)
        print(f"wrote {dest}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
