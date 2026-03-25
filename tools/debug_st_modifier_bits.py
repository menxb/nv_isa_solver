#!/usr/bin/env python3
"""Debug ST modifier_bits: 检查 mutation 分析后 modifier_bits 是否为空。"""
import os
import sys

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if PROJECT_ROOT not in sys.path:
    sys.path.insert(0, PROJECT_ROOT)

from nv_isa_solver.disasm_utils import Disassembler
from nv_isa_solver.parser import InstructionParser
from nv_isa_solver.instruction_solver import (
    InstructionMutationSet,
    analysis_run_fixedpoint,
    analysis_disambiguate_flags,
    analysis_promote_known_flags,
    analysis_operand_fix,
    analysis_disambiguate_operand_flags,
    analysis_fimm_bridge_constants,
    analysis_extend_modifiers,
    analysis_modifier_splitting,
)

CACHE = "disasm_cache_sm100a.merged.txt"
ARCH = "SM100a"


def main():
    d = Disassembler(ARCH, nvdisasm="nvdisasm")
    d.load_cache(CACHE)
    d.find_uniques_from_cache()

    for key in ["ST_RURI_R", "ST_R_R", "ST_desc[UR][RI]_R", "ST_desc[UR][R]_R"]:
        cands = d.get_cache_candidates(key)
        if not cands:
            print(f"[SKIP] {key}")
            continue

        # 用第一个候选
        inst = bytes(cands[0][0])
        asm = d.disassemble(inst)
        mutations = d.mutate_inst(inst, end=128)
        mset = InstructionMutationSet(inst, asm, mutations, d)
        mset._merge_f16_rn_rz_flag_bits()

        analysis_run_fixedpoint(d, mset, analysis_disambiguate_flags)
        analysis_run_fixedpoint(d, mset, analysis_promote_known_flags)
        analysis_run_fixedpoint(d, mset, analysis_operand_fix)
        analysis_run_fixedpoint(d, mset, analysis_disambiguate_operand_flags)
        analysis_run_fixedpoint(d, mset, analysis_fimm_bridge_constants)
        analysis_run_fixedpoint(d, mset, analysis_extend_modifiers)
        analysis_run_fixedpoint(d, mset, analysis_modifier_splitting)

        print(f"\n=== {key} (raw cache sample) ===")
        print(f"  inst: {inst.hex()}")
        print(f"  asm: {[l for l in asm.splitlines() if l.strip()][-1][:70]}")
        print(f"  modifier_bits: {sorted(mset.modifier_bits)}")
        print(f"  operand_modifier_bits: {sorted(mset.operand_modifier_bits)}")
        print(f"  modifier_bits count: {len(mset.modifier_bits)}")

        # 用 distill 后的
        try:
            dist = bytes(d.distill_instruction(inst))
        except Exception:
            dist = inst
        if dist != inst:
            asm2 = d.disassemble(dist)
            mut2 = d.mutate_inst(dist, end=128)
            mset2 = InstructionMutationSet(dist, asm2, mut2, d)
            mset2._merge_f16_rn_rz_flag_bits()
            analysis_run_fixedpoint(d, mset2, analysis_disambiguate_flags)
            analysis_run_fixedpoint(d, mset2, analysis_promote_known_flags)
            analysis_run_fixedpoint(d, mset2, analysis_operand_fix)
            analysis_run_fixedpoint(d, mset2, analysis_disambiguate_operand_flags)
            analysis_run_fixedpoint(d, mset2, analysis_fimm_bridge_constants)
            analysis_run_fixedpoint(d, mset2, analysis_extend_modifiers)
            analysis_run_fixedpoint(d, mset2, analysis_modifier_splitting)
            print(f"\n=== {key} (after distill) ===")
            print(f"  inst: {dist.hex()}")
            print(f"  asm: {[l for l in asm2.splitlines() if l.strip()][-1][:70]}")
            print(f"  modifier_bits: {sorted(mset2.modifier_bits)}")
            print(f"  operand_modifier_bits: {sorted(mset2.operand_modifier_bits)}")


if __name__ == "__main__":
    main()
