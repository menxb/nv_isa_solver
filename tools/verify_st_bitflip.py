#!/usr/bin/env python3
"""位翻转+反汇编验证 ST 指令：逐位翻转后检查 key 是否一致，定位问题位。"""
import os
import sys

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if PROJECT_ROOT not in sys.path:
    sys.path.insert(0, PROJECT_ROOT)

from nv_isa_solver.disasm_utils import Disassembler
from nv_isa_solver.parser import InstructionParser

CACHE = "disasm_cache_sm100a.merged.txt"
ARCH = "SM100a"


def main():
    d = Disassembler(ARCH, nvdisasm="nvdisasm")
    d.load_cache(CACHE)
    d.find_uniques_from_cache()

    st_keys = ["ST_RURI_R", "ST_RUR_R", "ST_desc[UR][RI]_R", "ST_desc[UR][R]_R", "ST_I_R", "ST_RI_R", "ST_R_R"]
    for key in st_keys:
        cands = d.get_cache_candidates(key)
        if not cands:
            print(f"[SKIP] {key}: no cache candidates")
            continue

        inst = bytes(d.distill_instruction(cands[0][0]))
        base_asm = d.disassemble(inst)
        try:
            base_parsed = InstructionParser.parseInstruction(
                [l for l in base_asm.splitlines() if l.strip()][-1]
            )
            base_key = base_parsed.get_key()
        except Exception as e:
            print(f"[ERR] {key}: parse failed: {e}")
            continue

        if base_key != key:
            print(f"[WARN] {key}: distilled key={base_key}")

        # 位翻转验证
        mutations = d.mutate_inst(inst, end=min(128, len(inst) * 8))
        key_changes = []
        invalid_count = 0
        for i_bit, mut_inst, mut_asm in mutations:
            if not mut_asm or not mut_asm.strip():
                invalid_count += 1
                continue
            lines = [l for l in mut_asm.splitlines() if l.strip()]
            if not lines:
                invalid_count += 1
                continue
            try:
                mut_parsed = InstructionParser.parseInstruction(lines[-1])
                mut_key = mut_parsed.get_key()
                if mut_key != base_key:
                    key_changes.append((i_bit, mut_key, lines[-1][:80]))
            except Exception:
                invalid_count += 1

        print(f"\n=== {key} ===")
        print(f"  inst_hex: {inst.hex()}")
        print(f"  base_asm: {[l for l in base_asm.splitlines() if l.strip()][-1][:80]}")
        print(f"  key_changes (bit -> new_key): {len(key_changes)}")
        for i_bit, new_key, asm in key_changes[:10]:
            print(f"    bit {i_bit} -> {new_key}: {asm}...")
        if len(key_changes) > 10:
            print(f"    ... and {len(key_changes) - 10} more")
        print(f"  invalid/empty disasm: {invalid_count}")


if __name__ == "__main__":
    main()
