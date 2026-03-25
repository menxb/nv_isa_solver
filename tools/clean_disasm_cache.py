#!/usr/bin/env python3
"""Clean disassembly cache entries against live nvdisasm output.

This script reads a cache file with lines in the form:
  asm --- hex

For each entry, it re-disassembles the hex bytes using nvdisasm for the target
architecture (default: SM100a) and drops entries that are not consistent.

By default, an entry is dropped when:
1) cache line is malformed (missing delimiter / invalid hex),
2) cached asm line is empty / placeholder-like (??? / INVALID / ..),
3) cached asm cannot be parsed by InstructionParser,
4) live disassembly is empty / placeholder-like / unparseable,
5) parsed key from cached asm != parsed key from live disassembly.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import sys
from collections import Counter, defaultdict

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, PROJECT_ROOT)

from nv_isa_solver.disasm_utils import Disassembler
from nv_isa_solver.parser import InstructionParser


INVALID_RE = re.compile(r"(?<!\w)INVALID(?!\w)", flags=re.IGNORECASE)


def is_placeholder_like(text: str) -> bool:
    if not text:
        return True
    if "???" in text:
        return True
    if ".." in text:
        return True
    if INVALID_RE.search(text):
        return True
    return False


def parse_cache_line(raw_line: str):
    if "---" not in raw_line:
        return None, "malformed_missing_delimiter"

    asm_part, hex_part = raw_line.split("---", 1)
    asm_text = asm_part.strip()
    hex_text = re.sub(r"[^0-9a-fA-F]", "", hex_part)

    if not asm_text:
        return None, "malformed_empty_asm"
    if not hex_text:
        return None, "malformed_empty_hex"
    if len(hex_text) % 2 != 0:
        return None, "malformed_odd_hex_length"

    try:
        inst = bytes.fromhex(hex_text)
    except ValueError:
        return None, "malformed_invalid_hex"

    return (asm_text, inst, hex_text), None


def parse_key(asm_line: str):
    parsed = InstructionParser.parseInstruction(asm_line)
    return parsed.get_key()


def last_non_empty_line(text: str) -> str:
    lines = [line.strip() for line in (text or "").splitlines() if line.strip()]
    return lines[-1] if lines else ""


def sample_add(samples, reason: str, line_no: int, cache_line: str, rebuilt_line: str = ""):
    if len(samples[reason]) >= 5:
        return
    samples[reason].append(
        {
            "line": line_no,
            "cache": cache_line,
            "rebuilt": rebuilt_line,
        }
    )


def clean_cache(args):
    if os.path.sep in args.nvdisasm:
        nvdisasm_ok = os.path.exists(args.nvdisasm) and os.access(args.nvdisasm, os.X_OK)
    else:
        nvdisasm_ok = shutil.which(args.nvdisasm) is not None
    if not nvdisasm_ok:
        print(
            f"error: nvdisasm not found or not executable: {args.nvdisasm}",
            file=sys.stderr,
        )
        print(
            "hint: install CUDA toolkit or pass --nvdisasm /path/to/nvdisasm",
            file=sys.stderr,
        )
        return 2

    disassembler = Disassembler(args.arch, nvdisasm=args.nvdisasm)

    reason_counts = Counter()
    samples = defaultdict(list)
    total = 0
    kept = 0
    dropped = 0

    output_path = args.output
    if args.in_place:
        output_path = args.input + ".tmp.cleaning"

    with open(args.input, "r", encoding="utf-8", errors="ignore") as fin, open(
        output_path, "w", encoding="utf-8"
    ) as fout:
        for line_no, raw in enumerate(fin, start=1):
            if args.max_lines > 0 and total >= args.max_lines:
                break

            total += 1
            raw_line = raw.rstrip("\n")
            parsed, parse_reason = parse_cache_line(raw_line)

            if parse_reason is not None:
                dropped += 1
                reason_counts[parse_reason] += 1
                sample_add(samples, parse_reason, line_no, raw_line)
                continue

            cached_asm, inst, _hex_text = parsed
            cached_line = last_non_empty_line(cached_asm)

            if is_placeholder_like(cached_line):
                dropped += 1
                reason_counts["cache_placeholder_like"] += 1
                sample_add(samples, "cache_placeholder_like", line_no, cached_line)
                continue

            try:
                cache_key = parse_key(cached_line)
            except Exception:
                dropped += 1
                reason_counts["cache_parse_error"] += 1
                sample_add(samples, "cache_parse_error", line_no, cached_line)
                continue

            try:
                rebuilt_full = disassembler.disassemble(inst)
            except Exception as exc:
                dropped += 1
                reason = "live_disasm_error"
                reason_counts[reason] += 1
                sample_add(samples, reason, line_no, cached_line, f"<error: {exc}>")
                continue

            rebuilt_line = last_non_empty_line(rebuilt_full)
            if is_placeholder_like(rebuilt_line):
                dropped += 1
                reason = "live_disasm_placeholder_like"
                reason_counts[reason] += 1
                sample_add(samples, reason, line_no, cached_line, rebuilt_line)
                continue

            try:
                rebuilt_key = parse_key(rebuilt_line)
            except Exception:
                dropped += 1
                reason = "live_disasm_parse_error"
                reason_counts[reason] += 1
                sample_add(samples, reason, line_no, cached_line, rebuilt_line)
                continue

            if args.key_check and cache_key != rebuilt_key:
                dropped += 1
                reason = "key_mismatch"
                reason_counts[reason] += 1
                sample_add(
                    samples,
                    reason,
                    line_no,
                    f"{cached_line} [key={cache_key}]",
                    f"{rebuilt_line} [key={rebuilt_key}]",
                )
                continue

            kept += 1
            fout.write(raw_line + "\n")

            if args.progress_every > 0 and total % args.progress_every == 0:
                print(
                    f"[progress] lines={total} kept={kept} dropped={dropped} unique_live_cache={len(disassembler.cache)}"
                )

    if args.in_place:
        os.replace(output_path, args.input)
        final_output = args.input
    else:
        final_output = output_path

    print("=== clean_disasm_cache report ===")
    print(f"input:  {args.input}")
    print(f"output: {final_output}")
    print(f"arch:   {args.arch}")
    print(f"total:  {total}")
    print(f"kept:   {kept}")
    print(f"dropped:{dropped}")
    print(f"live_disasm_unique_hex:{len(disassembler.cache)}")

    if reason_counts:
        print("drop reasons:")
        for reason, count in reason_counts.most_common():
            print(f"  {reason}: {count}")

    if args.show_samples and reason_counts:
        print("samples:")
        for reason, _count in reason_counts.most_common():
            for item in samples[reason][: args.show_samples]:
                cache_line = item.get("cache", "")
                rebuilt_line = item.get("rebuilt", "")
                if rebuilt_line:
                    print(f"  [{reason}] line {item['line']}")
                    print(f"    cache:   {cache_line}")
                    print(f"    rebuilt: {rebuilt_line}")
                else:
                    print(f"  [{reason}] line {item['line']} cache: {cache_line}")

    return 0


def build_argparser():
    ap = argparse.ArgumentParser(
        description="Remove cache entries not consistent with live nvdisasm output."
    )
    ap.add_argument(
        "--input",
        default=os.path.join(PROJECT_ROOT, "disasm_cache_sm100a.merged.txt"),
        help="Input cache file path (format: asm --- hex)",
    )
    ap.add_argument(
        "--output",
        default=os.path.join(PROJECT_ROOT, "disasm_cache_sm100a.merged.cleaned.txt"),
        help="Output cache file path (ignored with --in-place)",
    )
    ap.add_argument("--arch", default="SM100a", help="Target arch for nvdisasm --binary")
    ap.add_argument("--nvdisasm", default="nvdisasm", help="Path to nvdisasm executable")
    ap.add_argument(
        "--no-key-check",
        dest="key_check",
        action="store_false",
        help="Do not drop entries when parsed key differs between cached asm and live disasm",
    )
    ap.set_defaults(key_check=True)
    ap.add_argument(
        "--in-place",
        action="store_true",
        help="Overwrite input file in place (writes temp file then replace)",
    )
    ap.add_argument(
        "--max-lines",
        type=int,
        default=0,
        help="Only process first N lines (0 means all)",
    )
    ap.add_argument(
        "--progress-every",
        type=int,
        default=50000,
        help="Print progress every N processed lines (0 disables)",
    )
    ap.add_argument(
        "--show-samples",
        type=int,
        default=2,
        help="Show up to N sample lines per drop reason (0 disables)",
    )
    return ap


def main():
    args = build_argparser().parse_args()
    return clean_cache(args)


if __name__ == "__main__":
    sys.exit(main())
