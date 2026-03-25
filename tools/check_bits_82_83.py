#!/usr/bin/env python3
"""Quick check: do bits 82, 83 (between operand 2 segments) affect INT_IMM?"""
import os
import sys

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, PROJECT_ROOT)

from nv_isa_solver.disasm_utils import Disassembler
from nv_isa_solver.parser import InstructionParser, IntIMMOperand

def get_imm(parsed):
    for op in parsed.get_flat_operands():
        if isinstance(op, IntIMMOperand):
            return op.constant
    return None

dis = Disassembler("SM100a")
dis.load_cache(os.path.join(PROJECT_ROOT, "disasm_cache_sm100a.merged.txt"))

# Find @P0 RET.REL P0, R0 0x10 (RET_P_R_I)
for ib, asm in dis.cache.items():
    if not asm or "RET.REL P0, R0 0x10" not in asm:
        continue
    lines = [l for l in asm.splitlines() if l.strip()]
    if not lines:
        continue
    try:
        p = InstructionParser.parseInstruction(lines[-1])
        if p.get_key() != "RET_P_R_I":
            continue
        inst = bytes(ib)
        base_imm = get_imm(p)
        print(f"Base: {lines[-1][:50]}...  imm={base_imm}  hex={inst.hex()[:40]}...")
        for bit in [82, 83]:
            mut = bytearray(inst)
            if len(mut) < 16:
                mut.extend(b"\x00" * (16 - len(mut)))
            mut[bit // 8] ^= 1 << (bit % 8)
            asm2 = dis.disassemble(bytes(mut))
            lines2 = [l for l in asm2.splitlines() if l.strip()] if asm2 else []
            if lines2:
                p2 = InstructionParser.parseInstruction(lines2[-1])
                imm2 = get_imm(p2)
                key2 = p2.get_key()
                print(f"  Bit {bit}: key={key2} imm={imm2} (base={base_imm})  changed_imm={imm2 != base_imm}")
        break
    except Exception as e:
        print(f"Error: {e}")
        break
else:
    print("No RET_P_R_I with 0x10 found")
