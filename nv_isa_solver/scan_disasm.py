"""
Scan a dissassembly file to add to the corpus.

`cuobjdump --dump-sass --gpu-architecture sm_90 file`
"""

from .parser import InstructionParser
from .disasm_utils import Disassembler, get_bit_range

import argparse
from argparse import ArgumentParser


def main():
    arg_parser = ArgumentParser()
    arg_parser.add_argument("--arch", default="SM90a")
    arg_parser.add_argument("--cache_file", default="disasm_cache.txt")
    arg_parser.add_argument("--nvdisasm", default="nvdisasm")
    arg_parser.add_argument("file", type=argparse.FileType("r"))

    arguments = arg_parser.parse_args()

    disassembler = Disassembler(arguments.arch, nvdisasm=arguments.nvdisasm)
    disassembler.load_cache(arguments.cache_file)

    instructions = disassembler.find_uniques_from_cache()
    uncached = set()

    def process_instruction(disasm, instbytes):
        try:
            parsed = InstructionParser.parseInstruction(disasm)
        except Exception:
            print("Couldn't parse", inst)
            return False
        opcode = get_bit_range(instbytes, 0, 12)
        key = f"{opcode}.{parsed.get_key()}"
        if key not in instructions:
            instructions[key] = instbytes
            uncached.add(key)
            return True
        return False

    def to_bytes(first, second):
        first = first.strip()
        second = second.strip()

        def reverse_(a):
            return "".join(reversed([a[i : i + 2] for i in range(0, len(a), 2)]))
        # Be tolerant: extract hex sequences like '0x...'; ignore other chars
        import re

        m1 = re.search(r"0x([0-9a-fA-F]+)", first)
        m2 = re.search(r"0x([0-9a-fA-F]+)", second)
        if not m1 or not m2:
            return None
        a = m1.group(1)
        b = m2.group(1)
        # Ensure even-length hex (should be), otherwise pad
        if len(a) % 2 == 1:
            a = "0" + a
        if len(b) % 2 == 1:
            b = "0" + b
        try:
            return bytes.fromhex(reverse_(a) + reverse_(b))
        except Exception:
            return None

    prev = None
    asm = None
    for i, line in enumerate(arguments.file):
        line = line.strip()
        if not line.startswith("/*"):
            continue

        new_asm = None
        if line.count("/*") == 2:
            line_rest = line[line.find("*/") + 2 :].strip()
            new_asm = line_rest[: line_rest.find("/*")].strip()[:-1]
        else:
            line_rest = line

        line_dump = line_rest[line_rest.find("/*") + 2 : line_rest.find("*/")]
        if new_asm is not None:
            prev = line_dump
            asm = new_asm
            continue

        # If we haven't yet captured a previous dump (prev), skip this line
        if prev is None:
            prev = line_dump
            asm = None
            continue

        inst = to_bytes(prev, line_dump)
        if inst is None:
            # Could not parse hex from these comments; advance prev and skip
            prev = line_dump
            asm = None
            continue

        if process_instruction(asm, inst):
            print("Distilling", asm)
            disassembler.distill_instruction(inst)

    print("Found", len(uncached), "instructions")

    disassembler.dump_cache(arguments.cache_file)


if __name__ == "__main__":
    main()
