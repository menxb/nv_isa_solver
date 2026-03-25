#!/usr/bin/env python3
"""列出 cache 中有、但 isa.json 中未出现的助记符（含 opcode），用于排查被漏输的指令。"""

import json
import os
import sys

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if PROJECT_ROOT not in sys.path:
    sys.path.insert(0, PROJECT_ROOT)

from nv_isa_solver.disasm_utils import Disassembler, get_bit_range  # noqa: E402
from nv_isa_solver.parser import InstructionParser  # noqa: E402


def main():
    import argparse
    p = argparse.ArgumentParser(description="Compare cache mnemonics vs isa.json")
    p.add_argument("--cache", default="disasm_cache_sm100a.merged.txt", help="Cache file")
    p.add_argument("--isa", default="isa.json", help="isa.json path")
    p.add_argument("--arch", default="SM100a", help="Architecture")
    args = p.parse_args()

    cache_path = args.cache
    isa_path = args.isa
    if not os.path.exists(cache_path):
        print(f"Cache not found: {cache_path}", file=sys.stderr)
        sys.exit(1)

    dis = Disassembler(args.arch)
    dis.load_cache(cache_path)

    # (opcode, mnemonic) present in cache (from find_uniques keys)
    uniques = dis.find_uniques_from_cache()
    cache_set = set()
    for full_key in uniques:
        if "." in full_key:
            opcode_str, rest = full_key.split(".", 1)
            try:
                opcode = int(opcode_str)
            except ValueError:
                continue
            mnemonic = rest.split("_")[0] if "_" in rest else rest
            cache_set.add((opcode, mnemonic))

    # (opcode, mnemonic) present in isa.json
    isa_set = set()
    if os.path.exists(isa_path):
        try:
            with open(isa_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            for item in (data if isinstance(data, list) else data.get("instructions", [])):
                key = item.get("key") or item.get("analysis_key") or ""
                if "." in key:
                    opcode_str, rest = key.split(".", 1)
                    try:
                        opcode = int(opcode_str)
                    except ValueError:
                        continue
                    mnemonic = rest.split("_")[0] if "_" in rest else rest
                    isa_set.add((opcode, mnemonic))
        except Exception as e:
            print(f"Warning: could not load {isa_path}: {e}", file=sys.stderr)

    missing = sorted(cache_set - isa_set, key=lambda x: (x[1], x[0]))
    if missing:
        print("In cache but NOT in isa.json (opcode, mnemonic):")
        for opcode, mnemonic in missing:
            print(f"  {opcode}.{mnemonic}")
        print(f"Total: {len(missing)}")
    else:
        print("All cache mnemonics (by find_uniques) appear in isa.json.")


if __name__ == "__main__":
    main()
