#!/usr/bin/env python3
import argparse
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
import json
import os
import re
import subprocess
import tempfile
import time
from pathlib import Path


LINE_RE = re.compile(r"^\s*/\*[0-9A-Fa-f]+\*/\s*(.*?)\s*;\s*$", re.M)
HEX_RE = re.compile(r"[^0-9a-fA-F]")
INVALID_TOKEN_RE = re.compile(r"\bINVALID\w*\b", re.IGNORECASE)
DEFAULT_STDERR_PREVIEW_CHARS = 240
DEFAULT_AUTO_JOBS_CAP = 32
MIN_PARALLEL_CHUNK_SIZE = 64

STAT_KEYS = (
    "seen_lines",
    "kept_lines",
    "rewritten_asm_lines",
    "removed_illegal_lines",
    "removed_placeholder_lines",
    "kept_passthrough_lines",
    "format_invalid_lines",
    "chunks_checked",
    "leaf_checks",
)


def default_jobs():
    return max(1, min(os.cpu_count() or 1, DEFAULT_AUTO_JOBS_CAP))


def compute_effective_chunk_size(chunk_size, jobs):
    chunk_size = max(1, chunk_size)
    if jobs <= 1:
        return chunk_size
    target = max(MIN_PARALLEL_CHUNK_SIZE, chunk_size // jobs)
    return max(1, min(chunk_size, target))


def default_max_inflight(jobs):
    return max(1, jobs * 2)


def new_stats():
    return {key: 0 for key in STAT_KEYS}


def parse_args():
    parser = argparse.ArgumentParser(
        description="Filter a disassembly cache file by nvdisasm legality."
    )
    parser.add_argument("--input", required=True, help="Input cache shard or file")
    parser.add_argument("--output", required=True, help="Filtered output path")
    parser.add_argument("--arch", required=True, help="Architecture passed to nvdisasm")
    parser.add_argument("--nvdisasm", required=True, help="Path to nvdisasm")
    parser.add_argument("--chunk-size", type=int, default=16384)
    parser.add_argument(
        "--jobs",
        type=int,
        default=default_jobs(),
        help="Number of worker processes used to run nvdisasm",
    )
    parser.add_argument(
        "--max-inflight",
        type=int,
        default=0,
        help="Maximum pending blocks in flight; 0 picks a jobs-based default",
    )
    parser.add_argument("--report", help="Optional JSON summary output path")
    parser.add_argument("--report-every-sec", type=int, default=30)
    parser.add_argument("--max-examples", type=int, default=50)
    parser.add_argument(
        "--stderr-preview-chars",
        type=int,
        default=DEFAULT_STDERR_PREVIEW_CHARS,
        help="Max stderr chars stored per removed example (0 disables stderr capture)",
    )
    parser.add_argument(
        "--stdout-detailed-summary",
        action="store_true",
        help="Print full JSON summary to stdout instead of a compact one-line summary",
    )
    parser.add_argument(
        "--drop-placeholders",
        action="store_true",
        help="Also drop outputs containing ??? or INVALID* tokens",
    )
    parser.add_argument(
        "--rewrite-asm",
        action="store_true",
        help="Rewrite kept cache lines to the current nvdisasm text",
    )
    return parser.parse_args()


def preview_text(text, limit):
    text = (text or "").strip()
    if limit <= 0 or not text:
        return ""
    if len(text) <= limit:
        return text
    return text[:limit].rstrip() + f"...[truncated {len(text) - limit} chars]"


def compact_summary(summary, *, report_path=None):
    compact = {
        key: summary[key]
        for key in (
            "input",
            "output",
            "arch",
            "nvdisasm",
            "jobs",
            "max_inflight",
            "requested_chunk_size",
            "effective_chunk_size",
            "elapsed_sec",
            "seen_lines",
            "kept_lines",
            "rewritten_asm_lines",
            "removed_illegal_lines",
            "removed_placeholder_lines",
            "kept_passthrough_lines",
            "format_invalid_lines",
            "chunks_checked",
            "leaf_checks",
        )
        if key in summary
    }
    compact["removed_example_count"] = len(summary.get("removed_examples") or [])
    compact["format_invalid_example_count"] = len(
        summary.get("format_invalid_examples") or []
    )
    if report_path:
        compact["report"] = str(report_path)
    return compact


def run_nvdisasm_range(entries, start, end, nvdisasm, arch):
    blob = b"".join(entries[idx]["inst_bytes"] for idx in range(start, end))
    fd, name = tempfile.mkstemp(prefix="cache_filter_", dir="/tmp")
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(blob)
        result = subprocess.run(
            [nvdisasm, name, "--binary", arch],
            capture_output=True,
            text=True,
        )
    finally:
        os.remove(name)
    inst_lines = LINE_RE.findall(result.stdout or "")
    has_placeholder = any(
        ("???" in s) or INVALID_TOKEN_RE.search(s) for s in inst_lines
    )
    return result, inst_lines, has_placeholder


def format_cache_line(asm_text, hexstr):
    asm_text = (asm_text or "").strip()
    if asm_text.endswith(";"):
        return f"{asm_text} --- {hexstr.lower()}\n"
    return f"{asm_text} ; --- {hexstr.lower()}\n"


def normalized_asm_text(asm_text):
    return " ".join((asm_text or "").strip().split())


def filter_entry_range(
    entries,
    start,
    end,
    nvdisasm,
    arch,
    drop_placeholders,
    max_examples,
    stderr_preview_chars,
    rewrite_asm,
    stats,
    removed_examples,
    kept_entries,
):
    stats["chunks_checked"] += 1
    result, inst_lines, has_placeholder = run_nvdisasm_range(
        entries, start, end, nvdisasm, arch
    )
    ok = (
        result.returncode == 0
        and "Illegal instruction" not in (result.stderr or "")
        and "Unrecognized operation" not in (result.stderr or "")
        and len(inst_lines) == (end - start)
        and (not has_placeholder or not drop_placeholders)
    )
    if ok:
        for offset, entry_index in enumerate(range(start, end)):
            entry = entries[entry_index]
            output_line = entry["raw_line"]
            if rewrite_asm:
                redisasm = (inst_lines[offset] if offset < len(inst_lines) else "").strip()
                output_line = format_cache_line(redisasm, entry["hexstr"])
                if normalized_asm_text(redisasm) != normalized_asm_text(entry["asm"]):
                    stats["rewritten_asm_lines"] += 1
            kept_entries[entry_index] = output_line
        return
    if end - start == 1:
        entry = entries[start]
        stats["leaf_checks"] += 1
        if has_placeholder and drop_placeholders:
            stats["removed_placeholder_lines"] += 1
            kind = "placeholder"
        else:
            stats["removed_illegal_lines"] += 1
            kind = "illegal"
        if len(removed_examples) < max_examples:
            removed_examples.append(
                {
                    "kind": kind,
                    "line": entry["lineno"],
                    "asm": entry["asm"],
                    "hex": entry["hexstr"],
                    "redisasm": inst_lines[0] if inst_lines else "",
                    "stderr": preview_text(result.stderr, stderr_preview_chars),
                    "returncode": result.returncode,
                }
            )
        return
    mid = start + ((end - start) // 2)
    filter_entry_range(
        entries,
        start,
        mid,
        nvdisasm,
        arch,
        drop_placeholders,
        max_examples,
        stderr_preview_chars,
        rewrite_asm,
        stats,
        removed_examples,
        kept_entries,
    )
    filter_entry_range(
        entries,
        mid,
        end,
        nvdisasm,
        arch,
        drop_placeholders,
        max_examples,
        stderr_preview_chars,
        rewrite_asm,
        stats,
        removed_examples,
        kept_entries,
    )


def process_block(
    entries,
    items,
    nvdisasm,
    arch,
    drop_placeholders,
    max_examples,
    stderr_preview_chars,
    rewrite_asm,
):
    stats = new_stats()
    removed_examples = []
    kept_entries = {}

    if entries:
        filter_entry_range(
            entries,
            0,
            len(entries),
            nvdisasm,
            arch,
            drop_placeholders,
            max_examples,
            stderr_preview_chars,
            rewrite_asm,
            stats,
            removed_examples,
            kept_entries,
        )
    output_lines = []
    for item in items:
        if item["type"] == "passthrough":
            output_lines.append(item["raw_line"])
            stats["kept_passthrough_lines"] += 1
            continue
        if item["entry_index"] in kept_entries:
            output_lines.append(kept_entries[item["entry_index"]])

    stats["kept_lines"] = len(output_lines)
    return {
        **stats,
        "output_lines": output_lines,
        "removed_examples": removed_examples,
    }


def merge_stats(dst, src):
    for key in STAT_KEYS:
        dst[key] += src.get(key, 0)


def main():
    args = parse_args()
    input_path = Path(args.input)
    output_path = Path(args.output)
    jobs = max(1, args.jobs)
    effective_chunk_size = compute_effective_chunk_size(args.chunk_size, jobs)
    max_inflight = (
        max(jobs, args.max_inflight)
        if args.max_inflight > 0
        else default_max_inflight(jobs)
    )

    stats = new_stats()
    removed_examples = []
    format_invalid_examples = []
    start = time.time()
    last_report = start

    def maybe_report(stage="progress"):
        nonlocal last_report
        now = time.time()
        if stage == "progress" and now - last_report < args.report_every_sec:
            return
        print(
            json.dumps(
                {
                    "stage": stage,
                    "input": str(input_path),
                    "elapsed_sec": round(now - start, 1),
                    "jobs": jobs,
                    "effective_chunk_size": effective_chunk_size,
                    **stats,
                },
                ensure_ascii=False,
            ),
            flush=True,
        )
        last_report = now

    with ProcessPoolExecutor(max_workers=jobs) as executor:
        with input_path.open("r", encoding="utf-8", errors="replace") as src, output_path.open(
            "w", encoding="utf-8"
        ) as out_f:
            block_items = []
            block_entries = []
            next_block_id = 0
            next_write_block = 0
            pending = {}
            buffered_results = {}

            def write_ready_blocks():
                nonlocal next_write_block
                while next_write_block in buffered_results:
                    result = buffered_results.pop(next_write_block)
                    out_f.writelines(result["output_lines"])
                    next_write_block += 1

            def handle_done(done_futures):
                for future in done_futures:
                    block_id = pending.pop(future)
                    result = future.result()
                    buffered_results[block_id] = result
                    merge_stats(stats, result)
                    if len(removed_examples) < args.max_examples:
                        remaining = args.max_examples - len(removed_examples)
                        removed_examples.extend(result["removed_examples"][:remaining])
                write_ready_blocks()
                maybe_report("progress")

            def submit_block():
                nonlocal next_block_id, block_items, block_entries
                if not block_items:
                    return
                future = executor.submit(
                    process_block,
                    block_entries,
                    block_items,
                    args.nvdisasm,
                    args.arch,
                    args.drop_placeholders,
                    args.max_examples,
                    args.stderr_preview_chars,
                    args.rewrite_asm,
                )
                pending[future] = next_block_id
                next_block_id += 1
                block_items = []
                block_entries = []

            for lineno, raw_line in enumerate(src, 1):
                stats["seen_lines"] += 1
                if "---" not in raw_line:
                    block_items.append({"type": "passthrough", "raw_line": raw_line})
                    continue

                asm, inst = raw_line.split("---", 1)
                asm = asm.strip()
                hexstr = HEX_RE.sub("", inst)
                if not hexstr or len(hexstr) % 2 != 0:
                    stats["format_invalid_lines"] += 1
                    if len(format_invalid_examples) < args.max_examples:
                        format_invalid_examples.append(
                            {"line": lineno, "reason": "bad_hex", "raw": raw_line[:200]}
                        )
                    continue

                try:
                    inst_bytes = bytes.fromhex(hexstr)
                except ValueError:
                    stats["format_invalid_lines"] += 1
                    if len(format_invalid_examples) < args.max_examples:
                        format_invalid_examples.append(
                            {
                                "line": lineno,
                                "reason": "fromhex_failed",
                                "raw": raw_line[:200],
                            }
                        )
                    continue

                entry_index = len(block_entries)
                block_items.append({"type": "entry", "entry_index": entry_index})
                block_entries.append(
                    {
                        "lineno": lineno,
                        "asm": asm,
                        "hexstr": hexstr.lower(),
                        "inst_bytes": inst_bytes,
                        "raw_line": raw_line,
                    }
                )

                if len(block_entries) >= effective_chunk_size:
                    submit_block()
                    while len(pending) >= max_inflight:
                        done, _ = wait(
                            tuple(pending.keys()),
                            return_when=FIRST_COMPLETED,
                        )
                        handle_done(done)

            submit_block()
            while pending:
                done, _ = wait(tuple(pending.keys()), return_when=FIRST_COMPLETED)
                handle_done(done)
            write_ready_blocks()

    maybe_report("done")
    summary = {
        "input": str(input_path),
        "output": str(output_path),
        "arch": args.arch,
        "nvdisasm": args.nvdisasm,
        "jobs": jobs,
        "max_inflight": max_inflight,
        "requested_chunk_size": args.chunk_size,
        "effective_chunk_size": effective_chunk_size,
        "elapsed_sec": round(time.time() - start, 1),
        **stats,
        "removed_examples": removed_examples,
        "format_invalid_examples": format_invalid_examples,
    }
    if args.report:
        Path(args.report).write_text(
            json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8"
        )
    stdout_payload = (
        summary
        if args.stdout_detailed_summary
        else compact_summary(summary, report_path=args.report)
    )
    print(json.dumps(stdout_payload, ensure_ascii=False), flush=True)


if __name__ == "__main__":
    main()
