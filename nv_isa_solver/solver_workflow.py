import copy
import html
import json
import os
import re
import threading
import traceback
import sys
from argparse import ArgumentParser
from collections import Counter, defaultdict
from concurrent import futures
from itertools import combinations, product

from . import parser
from .modifier_domain import (
    is_diagnose_noise_token,
    split_token_parts,
)
from .parser import InstructionParser

_DIAGNOSTIC_FEEDBACK_HINTS = {}


def _report_nonfatal_exception(stage, key=None):
    """记录非致命异常并继续主流程。"""
    try:
        if key is None:
            sys.stderr.write(f"[nv_isa_solver] non-fatal error during {stage}\n")
        else:
            sys.stderr.write(
                f"[nv_isa_solver] non-fatal error during {stage}: {key}\n"
            )
        traceback.print_exc(file=sys.stderr)
        sys.stderr.flush()
    except Exception:
        pass


def flat_operand_signature(parsed_inst):
    try:
        ops = parsed_inst.get_flat_operands()
    except Exception:
        return tuple()
    sig = []
    for op in ops:
        try:
            ident = getattr(op, "ident", None)
            if ident is not None:
                sig.append(f"id:{ident}")
            else:
                sig.append(f"repr:{repr(op)}")
        except Exception:
            sig.append("<?>")
    return tuple(sig)


def operand_instance_fingerprint(op):
    try:
        return f"{type(op).__name__}:{repr(op)}"
    except Exception:
        try:
            ident = getattr(op, "ident", None)
            mods = tuple(getattr(op, "modifiers", []) or [])
            return f"{type(op).__name__}:id={ident}:mods={mods}"
        except Exception:
            return "<?>"


def normalized_token_counter_from_parsed(parsed_inst, split_token_parts_fn):
    out = Counter()
    try:
        base = getattr(parsed_inst, "base_name", None)
        if isinstance(base, str):
            for part in base.split(".")[1:]:
                for token in split_token_parts_fn(part):
                    out[token] += 1
    except Exception:
        pass

    try:
        for modifier in getattr(parsed_inst, "modifiers", []) or []:
            for token in split_token_parts_fn(modifier):
                out[token] += 1
    except Exception:
        pass

    try:
        for operand in parsed_inst.get_flat_operands():
            if isinstance(operand, (parser.IntIMMOperand, parser.FloatIMMOperand)):
                continue
            for modifier in getattr(operand, "modifiers", []) or []:
                for token in split_token_parts_fn(modifier):
                    out[token] += 1
    except Exception:
        pass
    return out


def diagnostic_token_location(raw_asm: str, token: str, split_token_parts_fn):
    if not raw_asm or not isinstance(raw_asm, str) or not token:
        return (None, None)
    try:
        parsed = InstructionParser.parseInstruction(raw_asm)
    except Exception:
        return (None, None)

    try:
        base = getattr(parsed, "base_name", None)
        if isinstance(base, str):
            for part in base.split(".")[1:]:
                if token in split_token_parts_fn(part):
                    return ("modifier", None)
    except Exception:
        pass

    try:
        for modifier in getattr(parsed, "modifiers", []) or []:
            if token in split_token_parts_fn(modifier):
                return ("modifier", None)
    except Exception:
        pass

    try:
        for op_idx, operand in enumerate(parsed.get_flat_operands()):
            for modifier in getattr(operand, "modifiers", []) or []:
                if token in split_token_parts_fn(modifier):
                    return ("operand_modifier", op_idx)
    except Exception:
        pass

    return (None, None)


def build_diagnostic_feedback_hints(
    payload,
    diagnostic_token_location_fn,
    extract_opcode_from_analysis_key_fn,
    get_bit_range_fn,
):
    if not isinstance(payload, list):
        return {}
    hints = defaultdict(list)
    for entry in payload:
        if not isinstance(entry, dict):
            continue
        hint_key = entry.get("analysis_key") or entry.get("parsed_key")
        parsed_key = entry.get("parsed_key")
        diagnostics = entry.get("diagnostics")
        if (not hint_key) or (not parsed_key) or not isinstance(diagnostics, list):
            continue
        for diag in diagnostics:
            if not isinstance(diag, dict):
                continue
            if diag.get("reason") != "single_bit_toggle":
                continue
            token = diag.get("token")
            evidence = diag.get("evidence") or {}
            entry_opcode = extract_opcode_from_analysis_key_fn(entry.get("analysis_key"))
            try:
                raw_inst_hex = evidence.get("raw_inst_hex")
                raw_opcode = (
                    get_bit_range_fn(bytes.fromhex(raw_inst_hex), 0, 12)
                    if isinstance(raw_inst_hex, str) and raw_inst_hex
                    else None
                )
            except Exception:
                raw_opcode = None
            if (
                entry_opcode is not None
                and raw_opcode is not None
                and entry_opcode != raw_opcode
            ):
                continue
            try:
                bits = sorted(
                    {
                        int(bit)
                        for bit in (evidence.get("single_bits") or [])
                        if isinstance(bit, int) or str(bit).isdigit()
                    }
                )
            except Exception:
                bits = []
            if not token or not bits:
                continue
            raw_asm = evidence.get("raw_asm") or evidence.get("distilled_asm") or ""
            kind, operand_index = diagnostic_token_location_fn(raw_asm, token)
            if kind is None:
                continue
            if kind == "operand_modifier":
                try:
                    operand_value_bits = {
                        int(bit)
                        for bit in (evidence.get("operand_value_bits") or [])
                        if isinstance(bit, int) or str(bit).isdigit()
                    }
                    bits = [bit for bit in bits if bit not in operand_value_bits]
                except Exception:
                    pass
            if not bits:
                continue
            hints[hint_key].append(
                {
                    "token": token,
                    "kind": kind,
                    "operand_index": operand_index,
                    "bits": bits,
                }
            )
    return dict(hints)


def load_diagnostic_feedback_hints(
    report_path: str,
    diagnostic_token_location_fn,
    extract_opcode_from_analysis_key_fn,
    get_bit_range_fn,
):
    if not report_path or not isinstance(report_path, str) or not os.path.exists(report_path):
        return {}
    try:
        with open(report_path, "r", encoding="utf-8") as f:
            payload = json.load(f)
    except Exception:
        return {}
    return build_diagnostic_feedback_hints(
        payload,
        diagnostic_token_location_fn=diagnostic_token_location_fn,
        extract_opcode_from_analysis_key_fn=extract_opcode_from_analysis_key_fn,
        get_bit_range_fn=get_bit_range_fn,
    )


def set_diagnostic_feedback_hints(hints):
    global _DIAGNOSTIC_FEEDBACK_HINTS
    try:
        _DIAGNOSTIC_FEEDBACK_HINTS = hints if isinstance(hints, dict) else {}
    except Exception:
        _DIAGNOSTIC_FEEDBACK_HINTS = {}


def variable_operand_indices_for_analysis_key(
    disassembler,
    analysis_key: str,
    parsed_inst=None,
    max_samples: int = 1024,
    extract_parsed_key_from_analysis_key_fn=None,
    extract_opcode_from_analysis_key_fn=None,
    cache_iter_by_key_fn=None,
    get_bit_range_fn=None,
):
    try:
        parsed_key = extract_parsed_key_from_analysis_key_fn(analysis_key)
    except Exception:
        parsed_key = None
    try:
        opcode_value = extract_opcode_from_analysis_key_fn(analysis_key)
    except Exception:
        opcode_value = None
    if not parsed_key:
        return None

    base_ops = []
    if parsed_inst is not None:
        try:
            base_ops = list(parsed_inst.get_flat_operands() or [])
        except Exception:
            base_ops = []

    sample_count = 0
    operand_variants = None
    for inst_b, asm_text in cache_iter_by_key_fn(disassembler, parsed_key):
        if max_samples > 0 and sample_count >= max_samples:
            break
        try:
            if opcode_value is not None and get_bit_range_fn(inst_b, 0, 12) != opcode_value:
                continue
        except Exception:
            continue
        try:
            if not asm_text or not isinstance(asm_text, str):
                continue
            lines = [line for line in asm_text.splitlines() if line.strip()]
            if not lines:
                continue
            parsed = InstructionParser.parseInstruction(lines[-1])
        except Exception:
            continue
        try:
            if parsed.get_key() != parsed_key:
                continue
        except Exception:
            continue

        try:
            ops = list(parsed.get_flat_operands() or [])
        except Exception:
            continue
        if operand_variants is None:
            operand_variants = [set() for _ in range(len(ops))]
        if len(ops) != len(operand_variants):
            continue
        if base_ops and len(base_ops) != len(ops):
            continue

        for idx, op in enumerate(ops):
            operand_variants[idx].add(operand_instance_fingerprint(op))
        sample_count += 1

    if operand_variants is None:
        return None
    return {
        idx for idx, variants in enumerate(operand_variants)
        if len(variants) >= 2
    }


def apply_diagnostic_feedback_hints(
    mutation_set,
    parsed_key: str,
    *,
    mutation_analysis_end_bit: int,
    is_control_code_bit_fn,
    is_placeholder_modifier_fn,
    analysis_key: str | None = None,
    feedback_hints=None,
):
    hints = []
    hint_source = feedback_hints if isinstance(feedback_hints, dict) else (_DIAGNOSTIC_FEEDBACK_HINTS or {})
    try:
        if analysis_key:
            hints = hint_source.get(analysis_key) or []
    except Exception:
        hints = []
    if not hints:
        hints = hint_source.get(parsed_key) or []
    if not hints:
        return False

    grouped_hints = {}
    for hint in hints:
        try:
            bits = sorted(
                {
                    int(bit)
                    for bit in (hint.get("bits") or [])
                    if 0 <= int(bit) < mutation_analysis_end_bit
                }
            )
        except Exception:
            bits = []
        if not bits:
            continue
        filtered_bits = [bit for bit in bits if not is_control_code_bit_fn(bit)]
        if hint.get("kind") in {"modifier", "operand_modifier"}:
            filtered_bits = [bit for bit in filtered_bits if bit >= 12]
        if not filtered_bits:
            continue
        runs = []
        current = [filtered_bits[0]]
        for bit in filtered_bits[1:]:
            if bit == current[-1] + 1:
                current.append(bit)
            else:
                runs.append(tuple(current))
                current = [bit]
        runs.append(tuple(current))
        token = hint.get("token")
        for span in runs:
            key = (hint.get("kind"), hint.get("operand_index"), span)
            bucket = grouped_hints.setdefault(
                key,
                {
                    "kind": hint.get("kind"),
                    "operand_index": hint.get("operand_index"),
                    "span": span,
                    "tokens": set(),
                },
            )
            if isinstance(token, str) and token:
                bucket["tokens"].add(token)

    if not grouped_hints:
        return False

    changed = False
    next_gid = max([0] + list((getattr(mutation_set, "modifier_groups", {}) or {}).values())) + 1

    for hint in grouped_hints.values():
        span = hint["span"]
        token_names = {
            tok
            for tok in (hint.get("tokens") or set())
            if isinstance(tok, str) and tok and not is_placeholder_modifier_fn(tok)
        }
        if hint["kind"] == "modifier":
            gid = next_gid
            next_gid += 1
            for bit in span:
                if bit in getattr(mutation_set, "predicate_bits", set()):
                    continue
                mutation_set.opcode_bits.discard(bit)
                mutation_set.operand_value_bits.discard(bit)
                mutation_set.operand_modifier_bits.discard(bit)
                mutation_set.operand_modifier_bit_flag.pop(bit, None)
                mutation_set.bit_to_operand.pop(bit, None)
                mutation_set.modifier_bits.add(bit)
                mutation_set.modifier_groups[bit] = gid
                changed = True
        elif hint["kind"] == "operand_modifier":
            operand_index = hint.get("operand_index")
            if operand_index is None:
                continue
            for bit in span:
                if bit in getattr(mutation_set, "predicate_bits", set()):
                    continue
                mutation_set.opcode_bits.discard(bit)
                mutation_set.modifier_bits.discard(bit)
                mutation_set.modifier_groups.pop(bit, None)
                mutation_set.instruction_modifier_bit_flag.pop(bit, None)
                mutation_set.operand_value_bits.discard(bit)
                mutation_set.operand_modifier_bits.add(bit)
                if len(span) == 1 and len(token_names) == 1:
                    mutation_set.operand_modifier_bit_flag[bit] = next(iter(token_names))
                else:
                    mutation_set.operand_modifier_bit_flag.pop(bit, None)
                mutation_set.bit_to_operand[bit] = operand_index
                changed = True

    return changed


def write_diagnostic_report(report_path: str, report_entries):
    if not report_path or not isinstance(report_path, str):
        return
    try:
        payload = []
        for entry in report_entries or []:
            if not isinstance(entry, dict):
                continue
            payload.append(entry)
        with open(report_path, "w", encoding="utf-8") as f:
            f.write(json.dumps(payload, ensure_ascii=False, indent=2))
    except Exception:
        return


def diagnostic_entry_score(diag_entry):
    if not isinstance(diag_entry, dict):
        return 10**9
    status = diag_entry.get("analysis_status", "ok")
    missing = diag_entry.get("missing_tokens") or []
    penalty = 10**6 if status != "ok" else 0
    return penalty + len(missing)


def diagnostic_entry_has_feedback(diag_entry, diagnostic_token_location_fn):
    if not isinstance(diag_entry, dict):
        return False
    for diag in diag_entry.get("diagnostics") or []:
        if not isinstance(diag, dict):
            continue
        evidence = diag.get("evidence") or {}
        reason = diag.get("reason")
        if reason == "single_bit_toggle" and (evidence.get("single_bits") or []):
            return True
        if reason == "unresolved":
            token = diag.get("token")
            raw_asm = evidence.get("raw_asm") or ""
            kind, _operand_index = diagnostic_token_location_fn(raw_asm, token)
            if kind == "operand_modifier" and evidence.get("raw_inst_hex"):
                return True
        if reason == "operand_value_token" and (evidence.get("single_bits") or []):
            return True
        if reason == "distill_dropped_token":
            token = diag.get("token")
            raw_asm = evidence.get("raw_asm") or ""
            kind, _operand_index = diagnostic_token_location_fn(raw_asm, token)
            if evidence.get("raw_inst_hex") and (
                kind in {"modifier", "operand_modifier"}
                or (token and raw_asm and token in raw_asm)
            ):
                return True
    return False


def select_feedback_seed_instruction(
    diag_entry,
    current_inst,
    diagnostic_token_location_fn,
    extract_mnemonic_head_from_disasm_fn,
    expected_family_head=None,
):
    if not isinstance(diag_entry, dict):
        return current_inst
    diagnostics = diag_entry.get("diagnostics") or []
    for reason_priority in ("distill_dropped_token", "single_bit_toggle", "unresolved"):
        for diag in diagnostics:
            if not isinstance(diag, dict):
                continue
            if diag.get("reason") != reason_priority:
                continue
            evidence = diag.get("evidence") or {}
            raw_asm = evidence.get("raw_asm") or ""
            token = diag.get("token")
            kind, _operand_index = diagnostic_token_location_fn(raw_asm, token)
            if kind not in {"modifier", "operand_modifier"}:
                if reason_priority != "distill_dropped_token" or not token or (raw_asm and token not in raw_asm):
                    continue
            raw_inst_hex = evidence.get("raw_inst_hex")
            if not isinstance(raw_inst_hex, str) or not raw_inst_hex:
                continue
            try:
                seed_inst = bytes.fromhex(raw_inst_hex)
            except Exception:
                continue
            if expected_family_head:
                try:
                    if extract_mnemonic_head_from_disasm_fn(raw_asm) != expected_family_head:
                        continue
                except Exception:
                    continue
            if seed_inst != current_inst:
                return seed_inst
    return current_inst


def diagnose_missing_tokens_for_key(
    disassembler,
    parsed_key: str,
    visible_tokens,
    max_tokens: int = 12,
    pair_budget: int = 256,
    max_cache_samples: int = 4000,
    family_heads=None,
    opcode_value=None,
    *,
    cache_iter_by_key_fn,
    extract_mnemonic_head_from_disasm_fn,
    parse_instruction_fn,
    get_bit_range_fn,
    has_placeholder_modifier_fn,
    split_token_parts_fn,
    is_diagnose_noise_token_fn,
    diagnose_operand_token_is_value_alias_fn,
    token_in_parsed_fn,
    set_bit_fn,
    mutation_analysis_end_bit,
    operand_value_changed_fn,
    parser_module,
):
    observed = set()
    token_samples = {}
    total = 0
    ok = 0
    cache_truncated = False
    for inst_b, asm_text in cache_iter_by_key_fn(disassembler, parsed_key):
        if max_cache_samples > 0 and total >= max_cache_samples:
            cache_truncated = True
            break
        total += 1
        if not asm_text or not isinstance(asm_text, str):
            continue
        lines = [line for line in asm_text.splitlines() if line.strip()]
        if not lines:
            continue
        asm_line = lines[-1]
        if family_heads:
            try:
                if extract_mnemonic_head_from_disasm_fn(asm_line) not in family_heads:
                    continue
            except Exception:
                continue
        try:
            parsed = parse_instruction_fn(asm_line)
        except Exception:
            continue
        if parsed.get_key() != parsed_key:
            continue
        if opcode_value is not None:
            try:
                if get_bit_range_fn(inst_b, 0, 12) != opcode_value:
                    continue
            except Exception:
                continue
        if has_placeholder_modifier_fn(getattr(parsed, "modifiers", [])):
            continue
        ok += 1

        base = getattr(parsed, "base_name", None)
        if isinstance(base, str):
            for part in base.split(".")[1:]:
                for token in split_token_parts_fn(part):
                    if is_diagnose_noise_token_fn(token):
                        continue
                    observed.add(token)
                    token_samples.setdefault(token, (bytes(inst_b), asm_line))
        for modifier in getattr(parsed, "modifiers", []) or []:
            for token in split_token_parts_fn(modifier):
                if is_diagnose_noise_token_fn(token):
                    continue
                observed.add(token)
                token_samples.setdefault(token, (bytes(inst_b), asm_line))
        try:
            for operand in parsed.get_flat_operands():
                if isinstance(operand, parser_module.FloatIMMOperand):
                    continue
                for modifier in getattr(operand, "modifiers", []) or []:
                    for token in split_token_parts_fn(modifier):
                        if diagnose_operand_token_is_value_alias_fn(operand, token):
                            continue
                        if (
                            isinstance(operand, parser_module.IntIMMOperand)
                            and token not in {"cNEG", "cABS"}
                        ):
                            continue
                        if is_diagnose_noise_token_fn(token):
                            continue
                        observed.add(token)
                        token_samples.setdefault(token, (bytes(inst_b), asm_line))
        except Exception:
            pass

    visible = {
        token.rstrip(".;")
        for token in (visible_tokens or set())
        if isinstance(token, str) and token
    }
    missing = sorted(observed - visible)
    if max_tokens > 0:
        missing = missing[:max_tokens]

    flip_probe_cache = {}

    def _probe_single_flips(distilled_inst):
        cache_key = bytes(distilled_inst)
        cached = flip_probe_cache.get(cache_key)
        if cached is not None:
            return cached

        bit_positions = list(range(0, mutation_analysis_end_bit))
        flip_insts = []
        for bit in bit_positions:
            arr = bytearray(distilled_inst)
            set_bit_fn(arr, bit)
            flip_insts.append(bytes(arr))

        try:
            flip_asms = disassembler.disassemble_parallel(flip_insts)
        except Exception:
            flip_asms = [disassembler.disassemble(inst) for inst in flip_insts]

        same_key_parsed = {}
        same_key_lines = {}
        for bit, inst_bytes, asm in zip(bit_positions, flip_insts, flip_asms):
            if not asm:
                continue
            if opcode_value is not None:
                try:
                    if get_bit_range_fn(inst_bytes, 0, 12) != opcode_value:
                        continue
                except Exception:
                    continue
            lines = [line for line in asm.splitlines() if line.strip()]
            if not lines:
                continue
            line = lines[-1]
            try:
                parsed = parse_instruction_fn(line)
            except Exception:
                continue
            if parsed.get_key() != parsed_key:
                continue
            same_key_parsed[bit] = parsed
            same_key_lines[bit] = line
        cached = (same_key_parsed, same_key_lines)
        flip_probe_cache[cache_key] = cached
        return cached

    diagnostics = []
    for token in missing:
        sample = token_samples.get(token)
        if not sample:
            diagnostics.append({"token": token, "reason": "no_sample", "evidence": {}})
            continue
        raw_inst, raw_asm = sample
        try:
            raw_parsed = parse_instruction_fn(raw_asm)
        except Exception:
            diagnostics.append(
                {
                    "token": token,
                    "reason": "sample_parse_failed",
                    "evidence": {"raw_asm": raw_asm},
                }
            )
            continue

        try:
            distilled = disassembler.distill_instruction(raw_inst)
            dist_asm_all = disassembler.disassemble(distilled)
            dist_lines = [line for line in dist_asm_all.splitlines() if line.strip()]
            dist_asm = dist_lines[-1] if dist_lines else dist_asm_all
            dist_parsed = parse_instruction_fn(dist_asm) if dist_asm else None
        except Exception:
            distilled = raw_inst
            dist_asm = ""
            dist_parsed = None

        distill_lost = False
        try:
            if dist_parsed is not None:
                distill_lost = token_in_parsed_fn(raw_parsed, token) and (
                    not token_in_parsed_fn(dist_parsed, token)
                )
        except Exception:
            distill_lost = False

        same_key_parsed, same_key_lines = _probe_single_flips(distilled)
        same_key_bits = sorted(same_key_parsed.keys())

        token_base = token_in_parsed_fn(dist_parsed, token) if dist_parsed is not None else False
        single_bits = []
        operand_value_bits = []
        for bit in same_key_bits:
            parsed = same_key_parsed[bit]
            token_now = token_in_parsed_fn(parsed, token)
            if token_now == token_base:
                continue
            single_bits.append(bit)
            if dist_parsed is not None and operand_value_changed_fn(dist_parsed, parsed):
                operand_value_bits.append(bit)

        coupled_pair = None
        if not single_bits and dist_parsed is not None:
            candidate_bits = same_key_bits[: min(len(same_key_bits), 24)]
            budget = 0
            for bit_a, bit_b in combinations(candidate_bits, 2):
                if budget >= pair_budget:
                    break
                budget += 1
                arr = bytearray(distilled)
                set_bit_fn(arr, bit_a)
                set_bit_fn(arr, bit_b)
                if opcode_value is not None:
                    try:
                        if get_bit_range_fn(arr, 0, 12) != opcode_value:
                            continue
                    except Exception:
                        continue
                asm = disassembler.disassemble(arr)
                if not asm:
                    continue
                lines = [line for line in asm.splitlines() if line.strip()]
                if not lines:
                    continue
                try:
                    parsed = parse_instruction_fn(lines[-1])
                except Exception:
                    continue
                if parsed.get_key() != parsed_key:
                    continue
                token_now = token_in_parsed_fn(parsed, token)
                if token_now != token_base:
                    coupled_pair = (bit_a, bit_b, lines[-1])
                    break

        reason = "unresolved"
        if single_bits:
            if len(operand_value_bits) == len(single_bits):
                reason = "operand_value_token"
            else:
                reason = "single_bit_toggle"
        elif coupled_pair is not None:
            reason = "multi_bit_coupled"
        elif distill_lost:
            reason = "distill_dropped_token"
        else:
            try:
                if isinstance(getattr(raw_parsed, "base_name", None), str):
                    in_base = token in [
                        part for part in raw_parsed.base_name.split(".")[1:] if part
                    ]
                    if in_base:
                        reason = "opcode_or_family_token"
            except Exception:
                pass

        diagnostics.append(
            {
                "token": token,
                "reason": reason,
                "evidence": {
                    "raw_inst_hex": raw_inst.hex(),
                    "raw_asm": raw_asm,
                    "distilled_asm": dist_asm,
                    "distill_lost": distill_lost,
                    "single_bits": single_bits[:32],
                    "operand_value_bits": operand_value_bits[:32],
                    "coupled_pair": coupled_pair,
                    "same_key_flip_bits": len(same_key_bits),
                    "single_flip_samples": [
                        {"bit": bit, "asm": same_key_lines.get(bit, "")}
                        for bit in single_bits[:6]
                    ],
                },
            }
        )

    return {
        "parsed_key": parsed_key,
        "observed_count": len(observed),
        "visible_count": len(visible),
        "missing_tokens": missing,
        "cache_samples_ok": ok,
        "cache_samples_total": total,
        "cache_samples_truncated": cache_truncated,
        "diagnostics": diagnostics,
    }


def build_key_miss_entry(
    disassembler,
    analysis_key: str,
    spec,
    *,
    max_tokens: int,
    pair_budget: int,
    max_cache_samples: int,
    extract_parsed_key_from_analysis_key_fn,
    extract_opcode_from_analysis_key_fn,
    get_bit_range_fn,
    visible_tokens_from_spec_fn,
    diagnose_missing_tokens_for_key_fn,
    family_heads=None,
):
    parsed_key = None
    try:
        if spec is not None and not getattr(spec, "filtered", False):
            parsed_key = spec.parsed.get_key()
    except Exception:
        parsed_key = None
    if not parsed_key:
        parsed_key = extract_parsed_key_from_analysis_key_fn(analysis_key)
    if not parsed_key:
        return {
            "analysis_key": analysis_key,
            "parsed_key": "",
            "observed_count": 0,
            "visible_count": 0,
            "missing_tokens": [],
            "cache_samples_ok": 0,
            "cache_samples_total": 0,
            "cache_samples_truncated": False,
            "diagnostics": [],
            "analysis_status": "no_parsed_key",
        }

    if spec is None or getattr(spec, "filtered", False):
        return {
            "analysis_key": analysis_key,
            "parsed_key": parsed_key,
            "observed_count": 0,
            "visible_count": 0,
            "missing_tokens": [],
            "cache_samples_ok": 0,
            "cache_samples_total": 0,
            "cache_samples_truncated": False,
            "diagnostics": [],
            "analysis_status": "no_spec",
        }

    opcode_value = extract_opcode_from_analysis_key_fn(analysis_key)
    if opcode_value is None:
        try:
            opcode_value = get_bit_range_fn(spec.ranges.inst, 0, 12)
        except Exception:
            opcode_value = None

    visible_tokens = visible_tokens_from_spec_fn(spec)
    diag = diagnose_missing_tokens_for_key_fn(
        disassembler,
        parsed_key,
        visible_tokens,
        max_tokens=max_tokens,
        pair_budget=pair_budget,
        max_cache_samples=max_cache_samples,
        family_heads=family_heads,
        opcode_value=opcode_value,
    )
    if not isinstance(diag, dict):
        diag = {}
    diag["analysis_key"] = analysis_key
    diag["analysis_status"] = "ok"
    return diag


def diagnose_operand_token_is_value_alias(operand, token: str, parser_module):
    try:
        clean = token.rstrip(".") if isinstance(token, str) else ""
        if not clean:
            return False
        if (
            isinstance(operand, parser_module.RegOperand)
            and getattr(operand, "reg_type", None) == "SNOWFLAKE"
        ):
            return True
    except Exception:
        return False
    return False


def token_in_parsed(parsed, token: str, split_token_parts_fn):
    target = token.rstrip(".;")
    if not target:
        return False
    try:
        base = getattr(parsed, "base_name", None)
        if isinstance(base, str):
            for part in base.split(".")[1:]:
                if part == target:
                    return True
    except Exception:
        pass
    try:
        for modifier in getattr(parsed, "modifiers", []) or []:
            for part in split_token_parts_fn(modifier):
                if part == target:
                    return True
    except Exception:
        pass
    try:
        for operand in parsed.get_flat_operands():
            for modifier in getattr(operand, "modifiers", []) or []:
                for part in split_token_parts_fn(modifier):
                    if part == target:
                        return True
    except Exception:
        pass
    return False


def visible_tokens_from_spec(
    spec,
    split_token_parts_fn,
    parser_module,
    encoding_range_type,
):
    tokens = set()
    try:
        for modifier in getattr(spec, "opcode_modis", []) or []:
            for token in split_token_parts_fn(modifier):
                tokens.add(token)
    except Exception:
        pass
    try:
        base = getattr(spec.parsed, "base_name", None)
        if isinstance(base, str):
            for part in base.split(".")[1:]:
                for token in split_token_parts_fn(part):
                    tokens.add(token)
    except Exception:
        pass
    try:
        for modifier in getattr(spec.parsed, "modifiers", []) or []:
            for token in split_token_parts_fn(modifier):
                tokens.add(token)
    except Exception:
        pass
    try:
        for group in getattr(spec, "modifiers", []) or []:
            for _value, name in group:
                for token in split_token_parts_fn(name):
                    tokens.add(token)
    except Exception:
        pass
    try:
        for operand in spec.parsed.get_flat_operands():
            for modifier in getattr(operand, "modifiers", []) or []:
                for token in split_token_parts_fn(modifier):
                    if isinstance(operand, (parser_module.IntIMMOperand, parser_module.FloatIMMOperand)) and token not in {"cNEG", "cABS"}:
                        continue
                    tokens.add(token)
    except Exception:
        pass
    try:
        for rows in (getattr(spec, "operand_modifiers", {}) or {}).values():
            for _value, name in rows:
                for token in split_token_parts_fn(name):
                    tokens.add(token)
    except Exception:
        pass
    try:
        for rng in getattr(spec.ranges, "ranges", []) or []:
            if rng.type not in (
                encoding_range_type.MODIFIER,
                encoding_range_type.FLAG,
                encoding_range_type.OPERAND_FLAG,
            ):
                continue
            for token in split_token_parts_fn(getattr(rng, "name", None)):
                tokens.add(token)
    except Exception:
        pass
    try:
        reparsed = InstructionParser.parseInstruction(getattr(spec, "disasm", "") or "")
        for operand in reparsed.get_flat_operands():
            for modifier in getattr(operand, "modifiers", []) or []:
                for token in split_token_parts_fn(modifier):
                    if isinstance(operand, (parser_module.IntIMMOperand, parser_module.FloatIMMOperand)) and token not in {"cNEG", "cABS"}:
                        continue
                    tokens.add(token)
    except Exception:
        pass
    return tokens


def _seed_feedback_hints(analysis_key, parsed_key_hint, diagnostic_feedback_hints):
    local_feedback_hints = {}
    try:
        if analysis_key and isinstance(diagnostic_feedback_hints, dict):
            if diagnostic_feedback_hints.get(analysis_key):
                local_feedback_hints[analysis_key] = copy.deepcopy(
                    diagnostic_feedback_hints.get(analysis_key) or []
                )
            if parsed_key_hint and diagnostic_feedback_hints.get(parsed_key_hint):
                local_feedback_hints[parsed_key_hint] = copy.deepcopy(
                    diagnostic_feedback_hints.get(parsed_key_hint) or []
                )
    except Exception:
        local_feedback_hints = {}
    return local_feedback_hints


class IncrementalDiagnosticReporter:
    def __init__(self, report_path, write_report_fn):
        self.report_path = report_path
        self.write_report_fn = write_report_fn
        self.report_entries_by_key = {}
        self.report_lock = threading.Lock()

    def update(self, diag_entry):
        if not self.report_path or not isinstance(diag_entry, dict):
            return
        report_key = diag_entry.get("analysis_key") or diag_entry.get("parsed_key")
        if not report_key:
            return
        with self.report_lock:
            missing_tokens = diag_entry.get("missing_tokens") or []
            status = diag_entry.get("analysis_status", "ok")
            if missing_tokens or status != "ok":
                self.report_entries_by_key[report_key] = diag_entry
            else:
                self.report_entries_by_key.pop(report_key, None)
            self.write_report_fn(
                self.report_path, self.report_entries_by_key.values()
            )


def initialize_diagnostic_report(report_path, write_report_fn):
    if report_path:
        write_report_fn(report_path, [])


def emit_miss_report(
    kept_analysis_map,
    report_path,
    diagnose_key_for_spec,
    write_report_fn,
):
    if not report_path:
        return
    miss_report = []
    for key, spec in (kept_analysis_map or {}).items():
        try:
            diag = diagnose_key_for_spec(key, spec)
        except Exception:
            continue
        if not isinstance(diag, dict):
            continue
        missing_tokens = diag.get("missing_tokens") or []
        status = diag.get("analysis_status", "ok")
        if missing_tokens or status != "ok":
            miss_report.append(diag)
    write_report_fn(report_path, miss_report)


def handle_diagnose_only(
    filtered_analysis,
    diagnose_missing,
    exact_key,
    diagnose_report,
    family_key_delim,
    diagnose_key_for_spec,
    write_report_fn,
):
    kept_analysis_quick = {
        key: spec
        for key, spec in filtered_analysis.items()
        if spec is not None and not getattr(spec, "filtered", False)
    }
    if diagnose_missing and not kept_analysis_quick and exact_key:
        parsed_hint = None
        try:
            parsed_part = exact_key.split(".", 1)[1] if "." in exact_key else exact_key
            if family_key_delim in parsed_part:
                parsed_part = parsed_part.split(family_key_delim, 1)[0]
            parsed_part = parsed_part.strip()
            if parsed_part:
                parsed_hint = parsed_part
        except Exception:
            parsed_hint = None
        try:
            fallback = [
                {
                    "parsed_key": parsed_hint or "",
                    "observed_count": 0,
                    "visible_count": 0,
                    "missing_tokens": [],
                    "cache_samples_ok": 0,
                    "cache_samples_total": 0,
                    "cache_samples_truncated": False,
                    "diagnostics": [],
                    "analysis_status": "no_spec",
                }
            ]
            with open(diagnose_report, "w", encoding="utf-8") as file:
                file.write(json.dumps(fallback, ensure_ascii=False, indent=2))
        except Exception:
            pass
        return True

    emit_miss_report(
        kept_analysis_map=kept_analysis_quick,
        report_path=diagnose_report,
        diagnose_key_for_spec=diagnose_key_for_spec,
        write_report_fn=write_report_fn,
    )
    return True


def analyze_instruction_with_feedback(
    analysis_key,
    inst,
    disassembler,
    arch_code,
    diagnose_only,
    operand_interactions,
    diagnose_light,
    diagnostic_feedback_hints,
    extract_parsed_key_from_analysis_key,
    diagnose_key_for_spec,
    incremental_reporter,
    diagnostic_entry_score,
    diagnostic_entry_has_feedback,
    build_diagnostic_feedback_hints,
    select_feedback_seed_instruction,
    extract_mnemonic_head_from_disasm,
    instruction_analysis_pipeline,
    expected_family_head=None,
    allow_expensive_cache_recovery=True,
):
    best_spec = None
    best_diag = None
    best_score = 10**9
    max_rounds = 1 if diagnose_only else 3
    round_inst = inst
    parsed_key_hint = extract_parsed_key_from_analysis_key(analysis_key)
    local_feedback_hints = _seed_feedback_hints(
        analysis_key,
        parsed_key_hint,
        diagnostic_feedback_hints,
    )

    for round_idx in range(max_rounds):
        skip_distill = round_idx >= 1
        spec = instruction_analysis_pipeline(
            round_inst,
            disassembler,
            arch_code,
            False,
            32768,
            expected_family_head,
            allow_expensive_cache_recovery,
            operand_interactions,
            diagnose_light,
            analysis_key=analysis_key,
            diagnostic_feedback_hints=local_feedback_hints,
            skip_distill=skip_distill,
        )
        diag_entry = diagnose_key_for_spec(
            analysis_key,
            spec,
            expected_family_head=expected_family_head,
        )
        incremental_reporter.update(diag_entry)

        score = diagnostic_entry_score(diag_entry)
        if score < best_score:
            best_score = score
            best_spec = spec
            best_diag = diag_entry

        if score == 0:
            break
        if round_idx + 1 >= max_rounds:
            break
        if not diagnostic_entry_has_feedback(diag_entry):
            break

        try:
            local_feedback_hints = build_diagnostic_feedback_hints([diag_entry])
        except Exception:
            local_feedback_hints = {}
        prev_round_inst = round_inst
        round_inst = select_feedback_seed_instruction(
            diag_entry,
            round_inst,
            expected_family_head=expected_family_head,
        )
        if expected_family_head is None and round_inst != prev_round_inst:
            try:
                head = extract_mnemonic_head_from_disasm(
                    disassembler.disassemble(round_inst)
                )
                if head:
                    expected_family_head = head
            except Exception:
                pass

    if best_diag is not None:
        incremental_reporter.update(best_diag)
    return best_spec


def run_instruction_analysis(
    instruction_items,
    num_parallel,
    analyze_instruction_with_feedback_fn,
):
    analysis_result = {}
    if num_parallel > 1 and len(instruction_items) > 1:
        with futures.ThreadPoolExecutor(max_workers=num_parallel) as executor:
            future_map = {}
            for (
                key,
                inst,
                expected_family_head,
                allow_expensive_cache_recovery,
            ) in instruction_items:
                future = executor.submit(
                    analyze_instruction_with_feedback_fn,
                    key,
                    inst,
                    expected_family_head,
                    allow_expensive_cache_recovery,
                )
                future_map[future] = key
            for future, key in future_map.items():
                try:
                    analysis_result[key] = future.result()
                except Exception:
                    _report_nonfatal_exception("instruction analysis", key)
                    analysis_result[key] = None
    else:
        for (
            key,
            inst,
            expected_family_head,
            allow_expensive_cache_recovery,
        ) in instruction_items:
            try:
                analysis_result[key] = analyze_instruction_with_feedback_fn(
                    key,
                    inst,
                    expected_family_head=expected_family_head,
                    allow_expensive_cache_recovery=allow_expensive_cache_recovery,
                )
            except Exception:
                _report_nonfatal_exception("instruction analysis", key)
                analysis_result[key] = None
    return analysis_result


def _collect_analysis_candidates(
    filtered_analysis,
    disassembler,
    arch_code,
    encoding_range_type,
    is_placeholder_modifier,
    recover_operand_spec_from_cache,
    backfill_modifier_tables_from_ranges,
    safe_flat_operand_count,
    safe_operand_range_count,
    safe_parsed_key,
    variable_operand_indices_for_analysis_key,
    extract_parsed_key_from_analysis_key,
):
    recovered_missing_operands = []
    analysis_candidates = []

    for key, spec in filtered_analysis.items():
        if spec is None:
            parsed_key_hint = None
            if "." in key:
                parsed_key_hint = extract_parsed_key_from_analysis_key(key)
            if parsed_key_hint:
                recovered_spec = recover_operand_spec_from_cache(
                    disassembler, parsed_key_hint, arch_code
                )
                if recovered_spec:
                    spec = recovered_spec
                    filtered_analysis[key] = spec
                    if key not in recovered_missing_operands:
                        recovered_missing_operands.append(key)
        if spec is None or getattr(spec, "filtered", False):
            continue

        try:
            backfill_modifier_tables_from_ranges(spec, disassembler)
        except Exception:
            pass

        parsed_ops_hint = safe_flat_operand_count(spec)
        operand_range_hint = safe_operand_range_count(spec)
        parsed_key_hint = safe_parsed_key(spec)

        if (
            parsed_ops_hint > 0
            and operand_range_hint == 0
            and parsed_key_hint is not None
        ):
            recovered_spec = recover_operand_spec_from_cache(
                disassembler, parsed_key_hint, arch_code
            )
            if recovered_spec:
                new_operand_count = safe_operand_range_count(recovered_spec)
                if new_operand_count > 0:
                    spec = recovered_spec
                    filtered_analysis[key] = spec
                    recovered_missing_operands.append(key)

        try:
            operand_ranges = spec.ranges._find(encoding_range_type.OPERAND)
            operand_range_count = len(operand_ranges)

            variable_operand_indices = variable_operand_indices_for_analysis_key(
                disassembler,
                key,
                parsed_inst=getattr(spec, "parsed", None),
            )
            if hasattr(spec.parsed, "get_flat_operands"):
                try:
                    parsed_ops_count = len(spec.parsed.get_flat_operands())
                except Exception:
                    parsed_ops_count = 0
            else:
                parsed_ops_count = len(getattr(spec.parsed, "operands", []))
            if variable_operand_indices is not None:
                required_operand_count = len(variable_operand_indices)
            else:
                required_operand_count = parsed_ops_count

            try:
                parsed_key = spec.parsed.get_key()
            except Exception:
                parsed_key = None
            canonical_name = (
                getattr(spec, "canonical_name", None)
                or getattr(spec.parsed, "base_name", None)
                or parsed_key
                or key
            )
            dedup_key = key
        except Exception:
            parsed_ops_count = 0
            required_operand_count = 0
            operand_range_count = 0
            dedup_key = key
            canonical_name = key

        analysis_candidates.append(
            {
                "key": key,
                "spec": spec,
                "parsed_ops_count": parsed_ops_count,
                "required_operand_count": required_operand_count,
                "operand_range_count": operand_range_count,
                "dedup_key": dedup_key,
                "canonical_name": canonical_name,
            }
        )

    return analysis_candidates, recovered_missing_operands


def _clean_name(name, is_placeholder_modifier):
    try:
        if not name or not isinstance(name, str):
            return None
        value = name.strip()
        if len(value) == 0:
            return None
        if is_placeholder_modifier(value):
            return None
        if value.lower() == "headerflags":
            return None
        return value
    except Exception:
        return None


def _sanitize_spec_json_obj(
    obj,
    spec,
    is_placeholder_modifier,
    filter_non_placeholder_modifiers,
):
    try:
        if "parsed" in obj and isinstance(obj["parsed"], dict):
            ops = obj["parsed"].get("operands", [])
            new_ops = []
            for op in ops:
                try:
                    if isinstance(op, dict) and "ident" in op:
                        ident = op.get("ident")
                        if (
                            isinstance(ident, str)
                            and is_placeholder_modifier(ident)
                        ):
                            op["ident"] = None
                except Exception:
                    pass
                new_ops.append(op)
            if new_ops:
                obj["parsed"]["operands"] = new_ops
            try:
                for op in obj["parsed"].get("operands", []):
                    if (
                        isinstance(op, dict)
                        and "modifiers" in op
                        and isinstance(op["modifiers"], list)
                    ):
                        op["modifiers"] = filter_non_placeholder_modifiers(
                            op["modifiers"]
                        )
            except Exception:
                pass
    except Exception:
        pass

    try:
        if "disasm" in obj and isinstance(obj["disasm"], str):
            try:
                disasm = obj["disasm"]
                try:
                    disasm = re.sub(r"\?+\d*", "", disasm)
                    disasm = re.sub(r"INVALID\w*", "", disasm, flags=re.IGNORECASE)
                except Exception:
                    disasm = disasm.replace("???", "").replace("INVALID", "")
                while ".." in disasm:
                    disasm = disasm.replace("..", ".")
                obj["disasm"] = disasm.strip()
            except Exception:
                pass
    except Exception:
        pass

    try:
        mods = obj.get("parsed", {}).get("modifiers", [])
        obj_parsed_mods = []
        for modifier in mods:
            clean_name = _clean_name(modifier, is_placeholder_modifier)
            if clean_name is not None:
                obj_parsed_mods.append(clean_name)
        if "parsed" not in obj:
            obj["parsed"] = {}
        obj["parsed"]["modifiers"] = obj_parsed_mods
    except Exception:
        pass

    try:
        if (
            "parsed" in obj
            and isinstance(obj["parsed"], dict)
            and "base_name" in obj["parsed"]
        ):
            base_name = obj["parsed"].get("base_name")
            if isinstance(base_name, str):
                try:
                    base_name = re.sub(r"\?+\d*", "", base_name)
                    base_name = re.sub(
                        r"INVALID\w*", "", base_name, flags=re.IGNORECASE
                    )
                except Exception:
                    base_name = base_name.replace("???", "").replace("INVALID", "")
                while ".." in base_name:
                    base_name = base_name.replace("..", ".")
                obj["parsed"]["base_name"] = base_name.strip()
    except Exception:
        pass

    try:
        if "modifiers" in obj and isinstance(obj["modifiers"], list):
            new_mods = []
            for group in obj["modifiers"]:
                try:
                    cleaned_group = []
                    for value, name in group:
                        clean_name = _clean_name(name, is_placeholder_modifier)
                        if clean_name is not None:
                            cleaned_group.append((value, clean_name))
                    if len(cleaned_group) > 0:
                        new_mods.append(cleaned_group)
                except Exception:
                    pass
            try:
                parsed_mods = []
                try:
                    disasm_lines = [
                        line
                        for line in str(getattr(spec, "disasm", "")).splitlines()
                        if line.strip()
                    ]
                    if disasm_lines:
                        parsed_disasm = InstructionParser.parseInstruction(
                            disasm_lines[-1]
                        )
                        for modifier in getattr(parsed_disasm, "modifiers", []) or []:
                            if isinstance(modifier, str):
                                name = modifier.rstrip(".")
                                if (
                                    name
                                    and not is_placeholder_modifier(name)
                                    and name not in parsed_mods
                                ):
                                    parsed_mods.append(name)
                except Exception:
                    parsed_mods = []
                if not parsed_mods:
                    for group in spec.modifiers:
                        if group and len(group) > 0:
                            name = group[0][1]
                            if isinstance(name, str):
                                stripped = name.rstrip(".")
                                if (
                                    stripped
                                    and not is_placeholder_modifier(stripped)
                                    and stripped not in parsed_mods
                                ):
                                    parsed_mods.append(stripped)
                            else:
                                text = str(name)
                                if text and text not in parsed_mods:
                                    parsed_mods.append(text)
                if parsed_mods and hasattr(spec.parsed, "modifiers"):
                    spec.parsed.modifiers = parsed_mods
            except Exception:
                pass
            obj["modifiers"] = new_mods
    except Exception:
        pass

    try:
        if "operand_modifiers" in obj and isinstance(obj["operand_modifiers"], dict):
            new_opmods = {}
            for opidx, rows in obj["operand_modifiers"].items():
                try:
                    rows_clean = []
                    for value, name in rows:
                        clean_name = _clean_name(name, is_placeholder_modifier)
                        try:
                            if (
                                isinstance(clean_name, str)
                                and clean_name.strip().lower() == "reuse"
                            ):
                                clean_name = None
                        except Exception:
                            pass
                        if clean_name is not None:
                            rows_clean.append((value, clean_name))
                    if rows_clean:
                        new_opmods[opidx] = rows_clean
                except Exception:
                    continue
            obj["operand_modifiers"] = new_opmods
    except Exception:
        pass

    try:
        if "ranges" in obj and isinstance(obj["ranges"], dict):
            ranges = obj["ranges"].get("ranges", [])
            for rng in ranges:
                try:
                    if isinstance(rng, dict) and "name" in rng:
                        name = rng.get("name")
                        if isinstance(name, str):
                            stripped = name.strip()
                            if (
                                len(stripped) == 0
                                or "???" in stripped
                                or stripped.upper().startswith("INVALID")
                            ):
                                rng["name"] = None
                except Exception:
                    continue
            obj["ranges"]["ranges"] = ranges
    except Exception:
        pass

    try:
        if "modifiers" in obj and isinstance(obj["modifiers"], list):
            if len(obj["modifiers"]) > 0 and all(
                isinstance(item, str) for item in obj["modifiers"]
            ):
                obj["modifiers"] = [
                    modifier
                    for modifier in obj["modifiers"]
                    if modifier
                    and not (
                        "???" in modifier
                        or modifier.upper().startswith("INVALID")
                        or modifier.strip().lower() == "headerflags"
                    )
                ]
    except Exception:
        pass

    return obj


def _select_best_analysis_candidates(
    analysis_candidates,
    is_placeholder_modifier,
    filter_non_placeholder_modifiers,
):
    canonical_best_operand = defaultdict(int)
    for entry in analysis_candidates:
        dedup_key = entry["dedup_key"]
        canonical_best_operand[dedup_key] = max(
            canonical_best_operand[dedup_key], entry["operand_range_count"]
        )

    kept_analysis = {}
    dropped_missing_operands = []
    best_per_dedup_key = {}

    for entry in analysis_candidates:
        key = entry.get("key")
        try:
            spec = entry["spec"]
            parsed_ops_count = entry["parsed_ops_count"]
            required_operand_count = entry.get(
                "required_operand_count", parsed_ops_count
            )
            operand_range_count = entry["operand_range_count"]
            max_operand_for_key = canonical_best_operand.get(
                entry["dedup_key"], operand_range_count
            )

            if (
                required_operand_count > 0
                and operand_range_count < required_operand_count
                and max_operand_for_key >= required_operand_count
            ):
                continue

            if (
                required_operand_count > 0
                and operand_range_count < max_operand_for_key
            ):
                continue

            obj = spec.to_json_obj()
            _sanitize_spec_json_obj(
                obj,
                spec,
                is_placeholder_modifier,
                filter_non_placeholder_modifiers,
            )

            dedup_key = entry["dedup_key"]
            if dedup_key in best_per_dedup_key:
                prev_key, prev_count = best_per_dedup_key[dedup_key]
                if operand_range_count <= prev_count:
                    continue
                try:
                    del kept_analysis[prev_key]
                except Exception:
                    pass
            best_per_dedup_key[dedup_key] = (key, operand_range_count)
            kept_analysis[key] = spec
        except Exception:
            _report_nonfatal_exception("postprocess candidate selection", key)
            continue

    return kept_analysis, dropped_missing_operands


def _replace_placeholder_specs(
    kept_analysis,
    dropped,
    replaced,
    disassembler,
    arch_code,
    enable_cache_fallback,
    encoding_range_type,
    has_placeholder_modifier,
    is_placeholder_modifier,
    find_clean_cache_candidate,
    instruction_analysis_pipeline,
):
    for key in list(kept_analysis.keys()):
        spec = kept_analysis[key]
        try:
            parsed_mods = getattr(spec.parsed, "modifiers", []) or []
            has_parsed_placeholders = has_placeholder_modifier(parsed_mods)
        except Exception:
            has_parsed_placeholders = False

        has_group_placeholders = False
        try:
            for group in getattr(spec, "modifiers", []):
                for _, name in group:
                    if isinstance(name, str):
                        stripped = name.strip()
                        if stripped and is_placeholder_modifier(stripped):
                            has_group_placeholders = True
                            break
                    elif name is not None:
                        has_group_placeholders = True
                        break
                if has_group_placeholders:
                    break
        except Exception:
            has_group_placeholders = False

        if not (has_parsed_placeholders or has_group_placeholders):
            continue

        clean = None
        try:
            if enable_cache_fallback:
                cache_res = find_clean_cache_candidate(
                    disassembler, getattr(spec, "parsed", spec)
                )
                if cache_res:
                    _parsed_cand, _groups, clean_inst, _clean_asm = cache_res
                    clean = (clean_inst,)
        except Exception:
            clean = None

        replaced_ok = False
        if clean:
            inst_bytes = None
            try:
                if isinstance(clean, dict):
                    inst_hex = clean.get("inst") or clean.get("bytes")
                    if isinstance(inst_hex, str):
                        inst_bytes = bytes.fromhex(inst_hex)
                elif isinstance(clean, (list, tuple)) and len(clean) > 0:
                    inst_bytes = clean[0]
                else:
                    inst_bytes = getattr(clean, "inst", None)
            except Exception:
                inst_bytes = None

            try:
                if isinstance(inst_bytes, str):
                    inst_bytes = bytes.fromhex(inst_bytes)
                if inst_bytes:
                    new_spec = instruction_analysis_pipeline(
                        inst_bytes,
                        disassembler,
                        arch_code,
                        analysis_key=key,
                    )
                    if new_spec:
                        kept_analysis[key] = new_spec
                        replaced.append(key)
                        replaced_ok = True
            except Exception:
                replaced_ok = False

        if replaced_ok:
            continue

        try:
            mod_ranges = spec.ranges._find(encoding_range_type.MODIFIER)
            if not mod_ranges or len(mod_ranges) == 0:
                del kept_analysis[key]
                dropped.append(key)
            else:
                domains = [range(2 ** rng.length) for rng in mod_ranges]
                max_enum = 32768
                tried = 0
                found = False
                try:
                    operand_count = len(spec.parsed.get_flat_operands())
                except Exception:
                    operand_count = spec.ranges.operand_count()
                operand_values = [0] * operand_count

                for combo in product(*domains):
                    tried += 1
                    if tried > max_enum:
                        break
                    try:
                        inst_bytes = spec.ranges.encode(operand_values, list(combo))
                    except Exception:
                        continue
                    try:
                        asm = disassembler.disassemble(inst_bytes)
                        asm_lines = [line for line in asm.splitlines() if line.strip()]
                        asm_to_parse = asm_lines[-1] if asm_lines else asm
                        if not asm_to_parse:
                            continue
                        parsed_candidate = InstructionParser.parseInstruction(
                            asm_to_parse
                        )
                        if parsed_candidate.get_key() != spec.parsed.get_key():
                            continue
                        if has_placeholder_modifier(
                            getattr(parsed_candidate, "modifiers", [])
                        ):
                            continue
                        new_spec = instruction_analysis_pipeline(
                            inst_bytes,
                            disassembler,
                            arch_code,
                            analysis_key=key,
                        )
                        if new_spec:
                            kept_analysis[key] = new_spec
                            replaced.append(key)
                            found = True
                            break
                    except Exception:
                        continue

                if not found:
                    has_concrete = False
                    try:
                        for group in getattr(spec, "modifiers", []):
                            for _, name in group:
                                if (
                                    isinstance(name, str)
                                    and not is_placeholder_modifier(name)
                                ):
                                    has_concrete = True
                                    break
                            if has_concrete:
                                break
                    except Exception:
                        pass
                    if not has_concrete:
                        try:
                            del kept_analysis[key]
                        except Exception:
                            pass
                        dropped.append(key)
        except Exception:
            try:
                del kept_analysis[key]
            except Exception:
                pass
            dropped.append(key)


def _drop_structural_duplicates(kept_analysis, dropped, spec_structural_fingerprint):
    try:
        seen_struct = {}
        for key in sorted(list(kept_analysis.keys())):
            try:
                fingerprint = spec_structural_fingerprint(kept_analysis[key])
            except Exception:
                fingerprint = None
            if fingerprint is None:
                continue
            prev = seen_struct.get(fingerprint)
            if prev is None:
                seen_struct[fingerprint] = key
                continue
            try:
                del kept_analysis[key]
            except Exception:
                pass
            dropped.append(key)
    except Exception:
        pass


def _fold_by_signature(
    kept_analysis,
    dropped,
    signature_fn,
    score_fn,
):
    try:
        best_by_sig = {}
        for key in sorted(list(kept_analysis.keys())):
            spec = kept_analysis.get(key)
            if spec is None:
                continue
            signature = signature_fn(spec)
            if signature is None:
                continue
            score = score_fn(spec)
            prev = best_by_sig.get(signature)
            if prev is None:
                best_by_sig[signature] = (key, score)
                continue
            prev_key, prev_score = prev
            if score > prev_score or (score == prev_score and key < prev_key):
                best_by_sig[signature] = (key, score)

        keep_keys = {item[0] for item in best_by_sig.values()}
        for key in sorted(list(kept_analysis.keys())):
            spec = kept_analysis.get(key)
            if spec is None:
                continue
            signature = signature_fn(spec)
            if signature is None or key in keep_keys:
                continue
            try:
                del kept_analysis[key]
            except Exception:
                continue
            dropped.append(key)
    except Exception:
        pass


def _fold_superset_profiles(
    kept_analysis,
    dropped,
    spec_coverage_profile,
    spec_coverage_quality_score,
    coverage_profile_is_superset,
):
    try:
        by_parsed_key = defaultdict(list)
        for key, spec in kept_analysis.items():
            profile = spec_coverage_profile(spec)
            if profile is None:
                continue
            score = spec_coverage_quality_score(spec)
            by_parsed_key[profile["parsed_key"]].append((key, profile, score))

        for _parsed_key, entries in by_parsed_key.items():
            if len(entries) <= 1:
                continue
            entries_sorted = sorted(
                entries,
                key=lambda item: (
                    -item[2][0],
                    -item[2][1],
                    -item[2][2],
                    -item[2][3],
                    -item[2][4],
                    -item[2][5],
                    -item[2][6],
                    item[0],
                ),
            )
            keep = []
            for key, profile, score in entries_sorted:
                covered = False
                for _keep_key, keep_profile, keep_score in keep:
                    if keep_score < score:
                        continue
                    if coverage_profile_is_superset(keep_profile, profile):
                        covered = True
                        break
                if covered:
                    if key in kept_analysis:
                        try:
                            del kept_analysis[key]
                        except Exception:
                            pass
                        dropped.append(key)
                    continue
                keep.append((key, profile, score))
    except Exception:
        pass


def _build_base_variable_map(kept_analysis):
    try:
        base_variable_map = {}
        for _key, spec in kept_analysis.items():
            try:
                base = getattr(spec.parsed, "base_name", None)
                if base is None:
                    continue
                if base not in base_variable_map:
                    base_variable_map[base] = set()
                groups = spec.modifiers if spec.modifiers else []
                for idx, group in enumerate(groups):
                    try:
                        if group and len(group) > 1:
                            base_variable_map[base].add(idx)
                    except Exception:
                        continue
            except Exception:
                continue
        return base_variable_map
    except Exception:
        return {}


def postprocess_analysis_results(
    filtered_analysis,
    disassembler,
    arch_code,
    encoding_range_type,
    enable_cache_fallback,
    is_placeholder_modifier,
    has_placeholder_modifier,
    filter_non_placeholder_modifiers,
    recover_operand_spec_from_cache,
    backfill_modifier_tables_from_ranges,
    safe_flat_operand_count,
    safe_operand_range_count,
    safe_parsed_key,
    variable_operand_indices_for_analysis_key,
    extract_parsed_key_from_analysis_key,
    find_clean_cache_candidate,
    instruction_analysis_pipeline,
    spec_structural_fingerprint,
    spec_family_merge_signature,
    spec_coverage_quality_score,
    spec_coverage_fold_signature,
    spec_coverage_profile,
    coverage_profile_is_superset,
):
    analysis_candidates, recovered_missing_operands = _collect_analysis_candidates(
        filtered_analysis=filtered_analysis,
        disassembler=disassembler,
        arch_code=arch_code,
        encoding_range_type=encoding_range_type,
        is_placeholder_modifier=is_placeholder_modifier,
        recover_operand_spec_from_cache=recover_operand_spec_from_cache,
        backfill_modifier_tables_from_ranges=backfill_modifier_tables_from_ranges,
        safe_flat_operand_count=safe_flat_operand_count,
        safe_operand_range_count=safe_operand_range_count,
        safe_parsed_key=safe_parsed_key,
        variable_operand_indices_for_analysis_key=variable_operand_indices_for_analysis_key,
        extract_parsed_key_from_analysis_key=extract_parsed_key_from_analysis_key,
    )

    kept_analysis, dropped_missing_operands = _select_best_analysis_candidates(
        analysis_candidates=analysis_candidates,
        is_placeholder_modifier=is_placeholder_modifier,
        filter_non_placeholder_modifiers=filter_non_placeholder_modifiers,
    )

    replaced = []
    dropped = list(dropped_missing_operands)

    _replace_placeholder_specs(
        kept_analysis=kept_analysis,
        dropped=dropped,
        replaced=replaced,
        disassembler=disassembler,
        arch_code=arch_code,
        enable_cache_fallback=enable_cache_fallback,
        encoding_range_type=encoding_range_type,
        has_placeholder_modifier=has_placeholder_modifier,
        is_placeholder_modifier=is_placeholder_modifier,
        find_clean_cache_candidate=find_clean_cache_candidate,
        instruction_analysis_pipeline=instruction_analysis_pipeline,
    )
    _drop_structural_duplicates(
        kept_analysis=kept_analysis,
        dropped=dropped,
        spec_structural_fingerprint=spec_structural_fingerprint,
    )
    _fold_by_signature(
        kept_analysis=kept_analysis,
        dropped=dropped,
        signature_fn=spec_family_merge_signature,
        score_fn=spec_coverage_quality_score,
    )
    _fold_by_signature(
        kept_analysis=kept_analysis,
        dropped=dropped,
        signature_fn=spec_coverage_fold_signature,
        score_fn=spec_coverage_quality_score,
    )
    _fold_superset_profiles(
        kept_analysis=kept_analysis,
        dropped=dropped,
        spec_coverage_profile=spec_coverage_profile,
        spec_coverage_quality_score=spec_coverage_quality_score,
        coverage_profile_is_superset=coverage_profile_is_superset,
    )
    _build_base_variable_map(kept_analysis)

    return {
        "kept_analysis": kept_analysis,
        "recovered_missing_operands": recovered_missing_operands,
        "replaced": replaced,
        "dropped": dropped,
    }


def _serialized_obj_has_only_placeholder_modifiers(obj, is_placeholder_modifier):
    try:
        for modifier in obj.get("parsed", {}).get("modifiers", []):
            try:
                if isinstance(modifier, str) and not is_placeholder_modifier(modifier):
                    return False
            except Exception:
                continue

        for group in obj.get("modifiers", []) or []:
            try:
                for _value, name in group:
                    if isinstance(name, str) and not is_placeholder_modifier(name):
                        return False
            except Exception:
                continue

        for rows in (obj.get("operand_modifiers", {}) or {}).values():
            try:
                for _value, name in rows:
                    if isinstance(name, str) and not is_placeholder_modifier(name):
                        return False
            except Exception:
                continue

        for entry in obj.get("modifier_interactions", []) or []:
            try:
                for token in entry.get("tokens", []) or []:
                    if isinstance(token, str) and not is_placeholder_modifier(token):
                        return False
            except Exception:
                continue

        serialized = json.dumps(obj)
        return "???" in serialized or "INVALID" in serialized.upper()
    except Exception:
        return True


def _clean_modifier_interactions_entries(modifier_interactions, is_placeholder_modifier):
    if not isinstance(modifier_interactions, list):
        return []

    cleaned = []
    for entry in modifier_interactions:
        try:
            groups = [int(group) for group in list(entry.get("groups") or [])]
            values = [int(value) for value in list(entry.get("values") or [])]
        except Exception:
            continue
        if not groups or len(groups) != len(values):
            continue

        seen_tokens = set()
        tokens = []
        for token in list(entry.get("tokens") or []):
            try:
                clean = token.rstrip(".").strip() if isinstance(token, str) else ""
            except Exception:
                clean = token
            if not clean:
                continue
            try:
                if isinstance(clean, str) and is_placeholder_modifier(clean):
                    continue
            except Exception:
                pass
            if clean in seen_tokens:
                continue
            tokens.append(clean)
            seen_tokens.add(clean)
        if not tokens:
            continue
        cleaned.append(
            {
                "groups": groups,
                "values": values,
                "tokens": tokens,
            }
        )
    return cleaned


def _clean_operand_modifiers_for_json(obj, is_placeholder_modifier):
    try:
        if "operand_modifiers" not in obj or not isinstance(
            obj["operand_modifiers"], dict
        ):
            return

        new_opmods = {}
        for opidx, rows in obj["operand_modifiers"].items():
            try:
                rows_clean = []
                for value, name in rows:
                    try:
                        if isinstance(name, str) and is_placeholder_modifier(name):
                            continue
                    except Exception:
                        pass

                    try:
                        name_clean = (
                            name.rstrip(".").strip() if isinstance(name, str) else name
                        )
                    except Exception:
                        name_clean = name

                    if not name_clean:
                        continue
                    rows_clean.append((value, name_clean))
                if rows_clean:
                    new_opmods[opidx] = rows_clean
            except Exception:
                continue
        obj["operand_modifiers"] = new_opmods
    except Exception:
        pass


def _clean_modifier_interactions_for_json(obj, is_placeholder_modifier):
    try:
        obj["modifier_interactions"] = _clean_modifier_interactions_entries(
            obj.get("modifier_interactions"),
            is_placeholder_modifier,
        )
    except Exception:
        pass


def _try_remediate_serialized_spec(
    key,
    kept_analysis,
    analysis_serialized,
    disassembler,
    arch_code,
    enable_cache_fallback,
    find_clean_cache_candidate,
    instruction_analysis_pipeline,
):
    try:
        if not enable_cache_fallback or key not in kept_analysis:
            return False

        spec = kept_analysis[key]
        cache_res = find_clean_cache_candidate(
            disassembler, getattr(spec, "parsed", spec)
        )
        if not cache_res:
            return False

        _parsed_cand, _groups, inst_bytes, _clean_asm = cache_res
        if not inst_bytes:
            return False

        new_spec = instruction_analysis_pipeline(
            inst_bytes,
            disassembler,
            arch_code,
            analysis_key=key,
        )
        if new_spec is None or getattr(new_spec, "filtered", False):
            return False

        analysis_serialized[key] = new_spec.to_json_obj()
        kept_analysis[key] = new_spec
        return True
    except Exception:
        return False


def finalize_serialized_analysis(
    kept_analysis,
    dropped,
    disassembler,
    arch_code,
    is_placeholder_modifier,
    enable_cache_fallback,
    find_clean_cache_candidate,
    instruction_analysis_pipeline,
):
    analysis_serialized = {}
    for key, spec in list(kept_analysis.items()):
        try:
            analysis_serialized[key] = spec.to_json_obj()
        except Exception:
            _report_nonfatal_exception("final serialization", key)
            try:
                del kept_analysis[key]
            except Exception:
                pass
            if key not in dropped:
                dropped.append(key)
    final_dropped = []

    for key in list(analysis_serialized.keys()):
        obj = analysis_serialized[key]
        _clean_operand_modifiers_for_json(obj, is_placeholder_modifier)
        _clean_modifier_interactions_for_json(obj, is_placeholder_modifier)

        if not _serialized_obj_has_only_placeholder_modifiers(
            obj, is_placeholder_modifier
        ):
            continue

        remedied = _try_remediate_serialized_spec(
            key=key,
            kept_analysis=kept_analysis,
            analysis_serialized=analysis_serialized,
            disassembler=disassembler,
            arch_code=arch_code,
            enable_cache_fallback=enable_cache_fallback,
            find_clean_cache_candidate=find_clean_cache_candidate,
            instruction_analysis_pipeline=instruction_analysis_pipeline,
        )
        if remedied:
            continue

        final_dropped.append(key)
        try:
            del analysis_serialized[key]
        except Exception:
            pass
        try:
            if key in kept_analysis:
                del kept_analysis[key]
        except Exception:
            pass

    for key in list(analysis_serialized.keys()):
        try:
            serialized = json.dumps(analysis_serialized[key])
            if "???" in serialized or "INVALID" in serialized.upper():
                try:
                    del analysis_serialized[key]
                except Exception:
                    pass
                try:
                    if key in kept_analysis:
                        del kept_analysis[key]
                except Exception:
                    pass
                if key not in dropped:
                    dropped.append(key)
        except Exception:
            pass

    for key in final_dropped:
        if key not in dropped:
            dropped.append(key)

    return analysis_serialized


def write_verification_log(path, recovered_missing_operands, replaced, dropped):
    try:
        with open(path, "w") as file:
            file.write(
                f"recovered_missing_operands: {len(recovered_missing_operands)}\n"
            )
            for item in recovered_missing_operands:
                file.write("O " + item + "\n")
            file.write(f"replaced: {len(replaced)}\n")
            for item in replaced:
                file.write("R " + item + "\n")
            file.write(f"dropped: {len(dropped)}\n")
            for item in dropped:
                file.write("D " + item + "\n")
    except Exception:
        pass


def group_specs_by_base_name(analysis_result):
    base_names = {}
    for _key, spec in analysis_result:
        try:
            base_name = spec.parsed.base_name
            if base_name not in base_names:
                base_names[base_name] = []
            base_names[base_name].append(spec)
        except Exception:
            _report_nonfatal_exception("group specs by base name", _key)
            continue
    return base_names


def _clean_operand_modifiers_for_html(operand_modifiers, is_placeholder_modifier):
    if not isinstance(operand_modifiers, dict):
        return operand_modifiers

    new_opmods = {}
    for opidx, rows in operand_modifiers.items():
        try:
            original_row_count = len(rows or [])
            rows_clean = []
            for value, name in rows:
                try:
                    if isinstance(name, str) and is_placeholder_modifier(name):
                        continue
                except Exception:
                    pass

                try:
                    name_clean = name.rstrip(".") if isinstance(name, str) else name
                except Exception:
                    name_clean = name

                try:
                    if (
                        isinstance(name_clean, str)
                        and name_clean.strip().lower() == "reuse"
                    ):
                        continue
                except Exception:
                    pass

                rows_clean.append((value, name_clean))

            distinct_names = {
                name
                for _value, name in rows_clean
                if isinstance(name, str) and name.strip()
            }
            has_binary_toggle = original_row_count >= 2 and len(distinct_names) >= 1
            if len(distinct_names) >= 2 or has_binary_toggle:
                new_opmods[opidx] = rows_clean
        except Exception:
            continue
    return new_opmods


def _format_modifier_interaction_value(value, width):
    try:
        if width is not None and int(width) > 1:
            return format(int(value), f"0{int(width)}b")
    except Exception:
        pass
    try:
        return str(int(value))
    except Exception:
        return str(value)


def _row_name_map(rows):
    mapping = {}
    for value, name in rows or []:
        try:
            clean = name.rstrip(".").strip() if isinstance(name, str) else ""
        except Exception:
            clean = ""
        mapping[int(value)] = clean
    return mapping


def _build_joint_modifier_tables(
    modifier_interactions,
    modifier_rows_by_group,
    group_number_map,
    group_width_map,
    selected_value_map,
):
    if not modifier_interactions:
        return [], set()

    grouped_entries = {}
    for entry in modifier_interactions:
        try:
            groups = tuple(int(group) for group in list(entry.get("groups") or []))
            values = tuple(int(value) for value in list(entry.get("values") or []))
        except Exception:
            continue
        tokens = [str(token) for token in list(entry.get("tokens") or []) if str(token)]
        if not groups or len(groups) != len(values) or not tokens:
            continue
        bucket = grouped_entries.setdefault(groups, {})
        bucket[values] = tokens

    rendered = []
    covered_groups = set()
    for groups, exact_tokens in grouped_entries.items():
        row_maps = []
        domains = []
        selected_names = []
        valid = True
        for group_idx in groups:
            rows = modifier_rows_by_group.get(group_idx) or []
            row_map = _row_name_map(rows)
            if not row_map:
                valid = False
                break
            row_maps.append(row_map)
            domains.append(sorted(row_map))
            selected_val = selected_value_map.get(group_idx)
            if selected_val is not None:
                selected_name = row_map.get(int(selected_val), "")
                if selected_name:
                    selected_names.append(selected_name)
        if not valid:
            continue

        base_token = None
        unique_selected = list(dict.fromkeys(selected_names))
        if len(unique_selected) == 1:
            base_token = unique_selected[0]

        rows = []
        seen_rows = set()
        for values in product(*domains):
            tokens = exact_tokens.get(tuple(values))
            if tokens is None:
                changed_tokens = []
                for group_idx, value, row_map in zip(groups, values, row_maps):
                    name = row_map.get(int(value), "")
                    if not name:
                        continue
                    selected_val = selected_value_map.get(group_idx)
                    if selected_val is not None and int(value) == int(selected_val):
                        continue
                    if base_token and name == base_token:
                        continue
                    if name not in changed_tokens:
                        changed_tokens.append(name)
                if changed_tokens:
                    if len(changed_tokens) != 1:
                        continue
                    tokens = changed_tokens
                else:
                    fallback_names = [
                        row_map.get(int(value), "")
                        for value, row_map in zip(values, row_maps)
                        if row_map.get(int(value), "")
                    ]
                    fallback_names = list(dict.fromkeys(fallback_names))
                    if base_token:
                        tokens = [base_token]
                    elif len(fallback_names) == 1:
                        tokens = fallback_names
                    else:
                        continue
            row_key = (tuple(values), tuple(tokens))
            if row_key in seen_rows:
                continue
            rows.append(
                {
                    "values": [
                        _format_modifier_interaction_value(
                            value,
                            group_width_map.get(group_idx),
                        )
                        for group_idx, value in zip(groups, values)
                    ],
                    "tokens": tokens,
                }
            )
            seen_rows.add(row_key)

        if not rows:
            continue
        rendered.append(
            {
                "groups": groups,
                "display_groups": [
                    group_number_map.get(group_idx, int(group_idx) + 1)
                    for group_idx in groups
                ],
                "rows": rows,
            }
        )
        covered_groups.update(groups)
    return rendered, covered_groups


def _render_modifier_interactions_html(
    modifier_interactions,
    group_number_map,
    group_width_map,
):
    if not modifier_interactions:
        return ""

    grouped_rows = {}
    for entry in modifier_interactions:
        groups = list(entry.get("groups") or [])
        values = list(entry.get("values") or [])
        tokens = list(entry.get("tokens") or [])
        if not groups or len(groups) != len(values) or not tokens:
            continue

        display_groups = []
        display_values = []
        for group_idx, value in zip(groups, values):
            display_group = group_number_map.get(group_idx, int(group_idx) + 1)
            width = group_width_map.get(group_idx)
            value_text = _format_modifier_interaction_value(value, width)
            display_groups.append(display_group)
            display_values.append(value_text)

        grouped_rows.setdefault(tuple(display_groups), []).append(
            {
                "values": display_values,
                "tokens": tokens,
            }
        )

    if not grouped_rows:
        return ""

    html_result = "<p>modifier interactions</p>"
    for display_groups, rows in grouped_rows.items():
        title = " + ".join(f"modi {group}" for group in display_groups) + " modifiers"
        html_result += f"<p>{html.escape(title)}"
        html_result += '<table class="instviz"><tbody>'
        html_result += '<tr class="smoll">'
        for display_group in display_groups:
            html_result += f'<td class="">modi {display_group}</td>'
        html_result += '<td class="">token</td></tr>'
        for row in rows:
            html_result += '<tr class="">'
            for value_text in row["values"]:
                html_result += f'<td class="">{html.escape(str(value_text))}</td>'
            token_text = ", ".join(html.escape(str(token)) for token in row["tokens"])
            html_result += f'<td class="">{token_text}</td></tr>'
        html_result += "</tbody></table></p>"
    return html_result


def _render_joint_modifier_tables_html(joint_tables):
    if not joint_tables:
        return ""

    html_result = ""
    for table in joint_tables:
        display_groups = list(table.get("display_groups") or [])
        rows = list(table.get("rows") or [])
        if not display_groups or not rows:
            continue
        title = " + ".join(f"modi {group}" for group in display_groups) + " modifiers"
        html_result += f"<p>{html.escape(title)}"
        html_result += '<table class="instviz"><tbody>'
        html_result += '<tr class="smoll">'
        for display_group in display_groups:
            html_result += f'<td class="">modi {display_group}</td>'
        html_result += '<td class="">token</td></tr>'
        for row in rows:
            html_result += '<tr class="">'
            for value_text in list(row.get("values") or []):
                html_result += f'<td class="">{html.escape(str(value_text))}</td>'
            token_text = ", ".join(
                html.escape(str(token)) for token in list(row.get("tokens") or [])
            )
            html_result += f'<td class="">{token_text}</td></tr>'
        html_result += "</tbody></table></p>"
    return html_result


def _clean_operand_modifier_composites_entries(
    operand_modifier_composites,
    is_placeholder_modifier,
):
    if not isinstance(operand_modifier_composites, list):
        return []

    cleaned = []
    for entry in operand_modifier_composites:
        try:
            operand_index = int(entry.get("operand_index"))
            group_id = int(entry.get("group_id"))
            main_width = int(entry.get("main_width"))
            overlay_width = int(entry.get("overlay_width"))
        except Exception:
            continue
        rows = []
        seen_rows = set()
        for row in list(entry.get("rows") or []):
            try:
                main_value = int(row.get("main_value"))
                overlay_value = int(row.get("overlay_value"))
            except Exception:
                continue
            seen_tokens = set()
            tokens = []
            for token in list(row.get("tokens") or []):
                try:
                    clean = token.rstrip(".").strip() if isinstance(token, str) else ""
                except Exception:
                    clean = token
                if not clean:
                    continue
                try:
                    if isinstance(clean, str) and is_placeholder_modifier(clean):
                        continue
                except Exception:
                    pass
                if clean in seen_tokens:
                    continue
                tokens.append(clean)
                seen_tokens.add(clean)
            if not tokens:
                continue
            row_key = (main_value, overlay_value, tuple(tokens))
            if row_key in seen_rows:
                continue
            rows.append(
                {
                    "main_value": main_value,
                    "overlay_value": overlay_value,
                    "tokens": tokens,
                }
            )
            seen_rows.add(row_key)
        if not rows:
            continue
        cleaned.append(
            {
                "operand_index": operand_index,
                "group_id": group_id,
                "main_width": main_width,
                "overlay_width": overlay_width,
                "rows": rows,
            }
        )
    return cleaned


def _render_operand_modifier_composite_html(
    entry,
    modi_id=None,
):
    try:
        operand_index = int(entry.get("operand_index"))
    except Exception:
        return ""
    rows = list(entry.get("rows") or [])
    if not rows:
        return ""

    try:
        main_width = int(entry.get("main_width"))
    except Exception:
        main_width = None
    try:
        overlay_width = int(entry.get("overlay_width"))
    except Exception:
        overlay_width = None

    title = f"Operand {operand_index} operand modifiers"
    if modi_id is not None:
        title += f" (modi {modi_id} + ovl)"
    html_result = f"<p>{html.escape(title)}"
    html_result += '<table class="instviz"><tbody>'
    html_result += '<tr class="smoll"><td class="">main</td><td class="">ovl</td><td class="">token</td></tr>'
    for row in rows:
        main_text = _format_modifier_interaction_value(row.get("main_value"), main_width)
        overlay_text = _format_modifier_interaction_value(
            row.get("overlay_value"),
            overlay_width,
        )
        token_text = ", ".join(
            html.escape(str(token)) for token in list(row.get("tokens") or [])
        )
        html_result += (
            '<tr class="">'
            f'<td class="">{html.escape(str(main_text))}</td>'
            f'<td class="">{html.escape(str(overlay_text))}</td>'
            f'<td class="">{token_text}</td>'
            "</tr>"
        )
    html_result += "</tbody></table></p>"
    return html_result


def _clean_disasm_for_html(disasm):
    if not isinstance(disasm, str):
        return disasm

    text = disasm
    try:
        text = re.sub(r"\?+\d*", "", text)
        text = re.sub(r"INVALID\w*", "", text, flags=re.IGNORECASE)
        text = re.sub(r"(?:(?<=\.)|^ )0(?=\.|$)", "", text)
        text = re.sub(r"(^|\.)0(?=\.|$)", "", text)
    except Exception:
        text = text.replace("???", "").replace("INVALID", "")

    while ".." in text:
        text = text.replace("..", ".")
    return text.strip()


def prepare_spec_for_html(
    spec,
    is_placeholder_modifier,
    *,
    get_bit_range_fn,
    encoding_range_type,
    encoding_range_cls,
    generate_modifier_table_fn,
    get_operand_modifier_rows_fn,
):
    try:
        cleaned = copy.deepcopy(spec)

        if hasattr(cleaned.parsed, "modifiers"):
            cleaned.parsed.modifiers = [
                modifier
                for modifier in cleaned.parsed.modifiers
                if not (
                    isinstance(modifier, str) and is_placeholder_modifier(modifier)
                )
            ]

        cleaned.operand_modifiers = _clean_operand_modifiers_for_html(
            getattr(cleaned, "operand_modifiers", None),
            is_placeholder_modifier,
        )
        cleaned.modifier_interactions = _clean_modifier_interactions_entries(
            getattr(cleaned, "modifier_interactions", None),
            is_placeholder_modifier,
        )
        cleaned.operand_modifier_composites = _clean_operand_modifier_composites_entries(
            getattr(cleaned, "operand_modifier_composites", None),
            is_placeholder_modifier,
        )
        cleaned.disasm = _clean_disasm_for_html(getattr(cleaned, "disasm", None))

        try:
            flat_ops = cleaned.parsed.get_flat_operands()
            used_operands = {
                er.operand_index
                for er in getattr(cleaned.ranges, "ranges", []) or []
                if er.type == encoding_range_type.OPERAND and er.operand_index is not None
            }
            for op in flat_ops:
                ident = None
                try:
                    ident = op.get_operand_key()
                except Exception:
                    ident = getattr(op, "ident", None)
                if not ident or "c[" not in ident:
                    continue
                idx = getattr(op, "flat_operand_index", None)
                if idx is None or idx in used_operands:
                    continue
                cleaned.ranges.ranges.append(
                    encoding_range_cls(
                        encoding_range_type.OPERAND,
                        start=0,
                        length=8,
                        operand_index=idx,
                        name=f"operand {idx}",
                    )
                )
                used_operands.add(idx)
        except Exception:
            pass

        try:
            modi_i = 0
            for er in getattr(cleaned.ranges, "ranges", []) or []:
                if er.type != encoding_range_type.MODIFIER:
                    continue
                try:
                    if (
                        hasattr(cleaned, "modifiers")
                        and cleaned.modifiers
                        and modi_i < len(cleaned.modifiers)
                    ):
                        group = cleaned.modifiers[modi_i]
                        for _value, name in group:
                            if isinstance(name, str) and not is_placeholder_modifier(name):
                                er.name = name.rstrip(".")
                                break
                except Exception:
                    pass
                modi_i += 1
        except Exception:
            pass

        try:
            for fr in cleaned.ranges._find(encoding_range_type.FLAG):
                try:
                    if not fr.name or is_placeholder_modifier(fr.name):
                        fr.name = None
                except Exception:
                    fr.name = None

            for fr in cleaned.ranges._find(encoding_range_type.OPERAND_FLAG):
                try:
                    if not fr.name or is_placeholder_modifier(fr.name):
                        fr.name = None
                except Exception:
                    fr.name = None
        except Exception:
            pass

        try:
            if hasattr(cleaned.ranges, "_compute_unified_modi_numbering"):
                initial_order = cleaned.ranges._compute_unified_modi_numbering()
            else:
                initial_order = []
        except Exception:
            initial_order = []

        try:
            orig_mod_ranges = cleaned.ranges._find(encoding_range_type.MODIFIER)
            orig_range_to_group = {
                (rng.start, rng.length, rng.group_id): idx
                for idx, rng in enumerate(orig_mod_ranges)
            }
        except Exception:
            orig_range_to_group = {}

        try:
            for entry in initial_order:
                kind = entry.get("kind")
                rng = entry.get("range")
                if rng is None:
                    continue

                if kind == "modifier":
                    key = (rng.start, rng.length, rng.group_id)
                    gidx = orig_range_to_group.get(key)
                    if gidx is None or gidx >= len(cleaned.modifiers):
                        continue
                    rows = cleaned.modifiers[gidx]
                    try:
                        sel_val = get_bit_range_fn(
                            cleaned.ranges.inst, rng.start, rng.start + rng.length
                        )
                    except Exception:
                        sel_val = None
                    tbl = generate_modifier_table_fn("_probe_", rows, rng, sel_val)
                    if not tbl:
                        try:
                            c_val = get_bit_range_fn(
                                cleaned.ranges.inst, rng.start, rng.start + rng.length
                            )
                        except Exception:
                            c_val = 0
                        rng.type = encoding_range_type.CONSTANT
                        rng.constant = c_val
                        rng.group_id = None
                        rng.name = None
                elif kind == "operand_modifier":
                    op_idx = entry.get("operand_index")
                    if op_idx is None:
                        continue
                    op_rng = rng
                    rows = get_operand_modifier_rows_fn(
                        cleaned.operand_modifiers, op_idx, op_rng
                    )
                    tbl = generate_modifier_table_fn("_probe_", rows, op_rng, None)
                    if not tbl:
                        try:
                            c_val = get_bit_range_fn(
                                cleaned.ranges.inst,
                                op_rng.start,
                                op_rng.start + op_rng.length,
                            )
                        except Exception:
                            c_val = 0
                        op_rng.type = encoding_range_type.CONSTANT
                        op_rng.constant = c_val
                        op_rng.operand_index = None
                        op_rng.name = None
        except Exception:
            pass

        try:
            if hasattr(cleaned.ranges, "_compute_unified_modi_numbering"):
                unified_order = cleaned.ranges._compute_unified_modi_numbering()
            else:
                unified_order = []
        except Exception:
            unified_order = []

        modifier_ranges = cleaned.ranges._find(encoding_range_type.MODIFIER)
        operand_modifier_ranges = cleaned.ranges._find(
            encoding_range_type.OPERAND_MODIFIER
        )
        operand_modifier_ranges_dict = {
            rng.operand_index: rng for rng in operand_modifier_ranges
        }

        try:
            selected_vals = {}
            for idx, rng in enumerate(modifier_ranges):
                try:
                    val = get_bit_range_fn(cleaned.ranges.inst, rng.start, rng.start + rng.length)
                except Exception:
                    val = None
                selected_vals[idx] = val
        except Exception:
            selected_vals = {}

        table_fragments = []
        composite_map = {}
        for entry in getattr(cleaned, "operand_modifier_composites", None) or []:
            operand_index = entry.get("operand_index")
            group_id = entry.get("group_id")
            composite_map[("group", operand_index, group_id)] = entry
            composite_map[("operand_modifier", operand_index, group_id)] = entry
        modifier_rows_by_group = {
            idx: rows for idx, rows in enumerate(getattr(cleaned, "modifiers", []) or [])
        }
        joint_tables, joint_groups = _build_joint_modifier_tables(
            getattr(cleaned, "modifier_interactions", None),
            modifier_rows_by_group,
            {},
            {},
            selected_vals,
        )
        if not unified_order:
            modifier_group_numbers = {}
            modifier_group_widths = {}
            joint_tables, joint_groups = _build_joint_modifier_tables(
                getattr(cleaned, "modifier_interactions", None),
                modifier_rows_by_group,
                {idx: idx + 1 for idx in modifier_rows_by_group},
                {
                    idx: getattr(rng, "length", None)
                    for idx, rng in enumerate(modifier_ranges)
                },
                selected_vals,
            )
            for i, rows in enumerate(cleaned.modifiers):
                rng = modifier_ranges[i] if i < len(modifier_ranges) else None
                if rng is None:
                    continue
                modifier_group_numbers[i] = i + 1
                modifier_group_widths[i] = getattr(rng, "length", None)
                if i in joint_groups:
                    continue
                tbl = generate_modifier_table_fn(
                    f"Modifier Group {i + 1}",
                    rows,
                    rng,
                    selected_vals.get(i),
                )
                if tbl:
                    table_fragments.append(tbl)
            seen_operand_modifier_groups = set()
            for rng in operand_modifier_ranges:
                op_idx = getattr(rng, "operand_index", None)
                if op_idx is None:
                    continue
                group_key = None
                if getattr(rng, "group_id", None) is not None:
                    group_key = ("group", op_idx, rng.group_id)
                    if group_key in seen_operand_modifier_groups:
                        continue
                    seen_operand_modifier_groups.add(group_key)
                    composite_entry = composite_map.get(group_key)
                    if composite_entry:
                        tbl = _render_operand_modifier_composite_html(composite_entry)
                        if tbl:
                            table_fragments.append(tbl)
                        continue
                modifiers = (
                    (
                        cleaned.operand_modifiers.get(group_key)
                        if group_key is not None
                        else None
                    )
                    or cleaned.operand_modifiers.get((op_idx, rng.start, rng.length))
                    or cleaned.operand_modifiers.get(op_idx)
                )
                if not modifiers:
                    continue
                tbl = generate_modifier_table_fn(
                    f"Operand {op_idx} operand modifiers",
                    modifiers,
                    rng,
                    None,
                )
                if tbl:
                    table_fragments.append(tbl)
            joint_html = _render_joint_modifier_tables_html(joint_tables)
            if joint_html:
                table_fragments.append(joint_html)
            interaction_tbl = _render_modifier_interactions_html(
                [],
                modifier_group_numbers,
                modifier_group_widths,
            )
            if interaction_tbl:
                table_fragments.append(interaction_tbl)
            setattr(cleaned, "_html_table_fragments", table_fragments)
            return cleaned

        seen_operand_modifier_groups = set()
        modifier_group_numbers = {}
        modifier_group_widths = {}
        orig_group_selected_vals = {}
        for entry in unified_order:
            kind = entry.get("kind")
            modi_id = entry.get("modi")
            if kind == "modifier":
                rng = entry.get("range")
                if rng is None:
                    continue
                key = (rng.start, rng.length, rng.group_id)
                gidx_orig = orig_range_to_group.get(key)
                if gidx_orig is None or gidx_orig >= len(cleaned.modifiers):
                    continue
                modifier_group_numbers[gidx_orig] = modi_id
                modifier_group_widths[gidx_orig] = getattr(rng, "length", None)
                orig_group_selected_vals[gidx_orig] = selected_vals.get(entry.get("group_index"))
        joint_tables, joint_groups = _build_joint_modifier_tables(
            getattr(cleaned, "modifier_interactions", None),
            modifier_rows_by_group,
            modifier_group_numbers,
            modifier_group_widths,
            orig_group_selected_vals,
        )
        rendered_joint_tables = False
        for entry in unified_order:
            kind = entry.get("kind")
            modi_id = entry.get("modi")
            if kind == "modifier":
                rng = entry.get("range")
                if rng is None:
                    continue
                key = (rng.start, rng.length, rng.group_id)
                gidx_orig = orig_range_to_group.get(key)
                if gidx_orig is None or gidx_orig >= len(cleaned.modifiers):
                    continue
                if gidx_orig in joint_groups:
                    if not rendered_joint_tables:
                        joint_html = _render_joint_modifier_tables_html(joint_tables)
                        if joint_html:
                            table_fragments.append(joint_html)
                        rendered_joint_tables = True
                    continue
                rows = cleaned.modifiers[gidx_orig]
                gidx = entry.get("group_index")
                sel = selected_vals.get(gidx)
                tbl = generate_modifier_table_fn(f"modi {modi_id} modifiers", rows, rng, sel)
                if tbl:
                    table_fragments.append(tbl)
                else:
                    setattr(rng, "hide_modi_label", True)
            elif kind == "operand_modifier":
                op_idx = entry.get("operand_index")
                if op_idx is None:
                    continue
                group_key = entry.get("group_key")
                if group_key is not None:
                    if group_key in seen_operand_modifier_groups:
                        continue
                    seen_operand_modifier_groups.add(group_key)
                    composite_entry = composite_map.get(group_key)
                    if composite_entry:
                        tbl = _render_operand_modifier_composite_html(
                            composite_entry,
                            modi_id=modi_id,
                        )
                        if tbl:
                            table_fragments.append(tbl)
                        continue
                rng = entry.get("range") or operand_modifier_ranges_dict.get(op_idx)
                rows = get_operand_modifier_rows_fn(cleaned.operand_modifiers, op_idx, rng)
                if not rows:
                    continue
                tbl = generate_modifier_table_fn(
                    f"Operand {op_idx} operand modifiers (modi {modi_id})",
                    rows,
                    rng,
                    None,
                )
                if tbl:
                    table_fragments.append(tbl)
                elif rng is not None:
                    setattr(rng, "hide_modi_label", True)

        setattr(cleaned, "_html_table_fragments", table_fragments)
        return cleaned
    except Exception:
        return spec


def write_html_outputs(
    base_names,
    output_dir,
    arch,
    instruction_desc_header,
    instviz_header,
    prepare_spec_for_html_fn,
    render_spec_html_fn,
):
    os.makedirs(output_dir, exist_ok=True)

    for base, specs in base_names.items():
        try:
            result = instruction_desc_header + instviz_header
            for idx, spec in enumerate(specs):
                try:
                    prepared = prepare_spec_for_html_fn(spec)
                    result += render_spec_html_fn(prepared)
                except Exception:
                    _report_nonfatal_exception(
                        "render spec html", f"{base}[{idx}]"
                    )
                    continue
            with open(os.path.join(output_dir, f"{base}.html"), "w") as file:
                file.write(result)
        except Exception:
            _report_nonfatal_exception("write family html", base)
            continue

    try:
        with open(os.path.join(output_dir, "index.html"), "w") as file:
            result = f"<h1> Nvidia {arch} Instruction Set Architecture</h1>"
            for base in base_names:
                result += f'<a href="{base}.html">{base}</a><br>'
            file.write(result)
    except Exception:
        _report_nonfatal_exception("write html index")


def build_arg_parser():
    parser = ArgumentParser()
    parser.add_argument("--arch", default="SM90a")
    parser.add_argument(
        "--arch_code", default=None, type=int
    )
    parser.add_argument("--cache_file", default="disasm_cache.txt")
    parser.add_argument("--nvdisasm", default="nvdisasm")
    parser.add_argument(
        "--dump_cache",
        action="store_true",
        help="将运行过程中新增的反汇编缓存写回 --cache_file（可能显著增大文件，默认关闭）。",
    )
    parser.add_argument("--num_parallel", default=4, type=int)
    parser.add_argument("--filter", default=None, type=str)
    parser.add_argument(
        "--filters_file",
        default=None,
        type=str,
        help="按文件提供多个 substring 过滤条件（每行一个，支持 # 注释）。与 --filter 取交集。",
    )
    parser.add_argument("--exact_key", default=None, type=str)
    parser.add_argument("--fast_exact", action="store_true")
    parser.add_argument("--diagnose_missing", action="store_true")
    parser.add_argument("--diagnose_only", action="store_true")
    parser.add_argument(
        "--operand_interactions",
        action="store_true",
        help="启用 operand live-range 交互分析（非常耗时，默认关闭）。",
    )
    parser.add_argument(
        "--diagnose_light",
        action="store_true",
        help="诊断专用轻量模式：跳过重枚举以换取速度，结果可能低估 visible token。",
    )
    parser.add_argument("--diagnose_max_tokens", default=12, type=int)
    parser.add_argument("--diagnose_max_keys", default=12, type=int)
    parser.add_argument("--diagnose_pair_budget", default=96, type=int)
    parser.add_argument("--diagnose_max_cache_samples", default=4000, type=int)
    parser.add_argument(
        "--diagnose_report",
        default="miss_reason_report.json",
        type=str,
    )
    return parser


class InstructionSolverDriver:
    def __init__(self, arguments, core_api):
        self.arguments = arguments
        self.core = core_api

    def _normalize_arguments(self):
        if self.arguments.arch_code is None:
            inferred_arch_code = None
            try:
                arch_text = str(self.arguments.arch or "").strip()
                match = re.search(r"SM\s*([0-9]+)", arch_text, flags=re.IGNORECASE)
                if match:
                    inferred_arch_code = int(match.group(1))
            except Exception:
                inferred_arch_code = None
            self.arguments.arch_code = (
                inferred_arch_code if inferred_arch_code is not None else 90
            )
        if not self.arguments.diagnose_only:
            self.arguments.diagnose_missing = True

    def _initialize_feedback_hints(self):
        diagnostic_feedback_hints = {}
        if not self.arguments.diagnose_only:
            try:
                diagnostic_feedback_hints = self.core.load_diagnostic_feedback_hints(
                    self.arguments.diagnose_report
                )
            except Exception:
                diagnostic_feedback_hints = {}
        self.core.set_diagnostic_feedback_hints(diagnostic_feedback_hints)
        if self.arguments.diagnose_only:
            diagnostic_feedback_hints = {}
            self.core.set_diagnostic_feedback_hints({})
        return diagnostic_feedback_hints

    def _load_filter_terms(self):
        filter_terms = []
        try:
            if self.arguments.filters_file and os.path.exists(self.arguments.filters_file):
                with open(self.arguments.filters_file, "r", encoding="utf-8") as file:
                    for line in file:
                        value = line.strip()
                        if not value or value.startswith("#"):
                            continue
                        filter_terms.append(value)
        except Exception:
            filter_terms = []
        return filter_terms

    def _match_filters(self, full_key, filter_terms):
        try:
            if self.arguments.filter and self.arguments.filter not in full_key:
                return False
            if filter_terms and not any(term in full_key for term in filter_terms):
                return False
            return True
        except Exception:
            return False

    def _build_instruction_items(self, disassembler, filter_terms):
        if self.arguments.exact_key:
            instructions = list(
                self.core.select_instruction_by_exact_key(
                    disassembler, self.arguments.exact_key
                ).items()
            )
            exact_expected_family = None
            try:
                if (
                    isinstance(self.arguments.exact_key, str)
                    and "." in self.arguments.exact_key
                ):
                    parsed_part = self.arguments.exact_key.split(".", 1)[1]
                    if self.core.FAMILY_KEY_DELIM in parsed_part:
                        exact_expected_family = parsed_part.split(
                            self.core.FAMILY_KEY_DELIM, 1
                        )[1].strip()
            except Exception:
                exact_expected_family = None
            if self.arguments.filter:
                instructions = [
                    (key, inst)
                    for key, inst in instructions
                    if self.arguments.filter in key
                ]
            if filter_terms:
                instructions = [
                    (key, inst)
                    for key, inst in instructions
                    if self._match_filters(key, filter_terms)
                ]
            return [
                (key, inst, exact_expected_family, not self.arguments.fast_exact)
                for key, inst in instructions
            ]

        all_uniques = disassembler.find_uniques_from_cache()
        instructions = list(all_uniques.items())
        instructions = [
            (key, inst)
            for key, inst in instructions
            if self._match_filters(key, filter_terms)
        ]
        return [(key, inst, None, True) for key, inst in instructions]

    def _make_diagnose_key_for_spec(self, disassembler):
        def diagnose_key_for_spec(analysis_key, spec, expected_family_head=None):
            family_heads = None
            try:
                if expected_family_head:
                    family_heads = {expected_family_head}
                elif spec is not None and not getattr(spec, "filtered", False):
                    head = self.core.extract_mnemonic_head_from_disasm(
                        getattr(spec, "disasm", "")
                    )
                    if head:
                        family_heads = {head}
            except Exception:
                family_heads = None
            return self.core.build_key_miss_entry(
                disassembler,
                analysis_key,
                spec,
                max_tokens=self.arguments.diagnose_max_tokens,
                pair_budget=self.arguments.diagnose_pair_budget,
                max_cache_samples=self.arguments.diagnose_max_cache_samples,
                family_heads=family_heads,
            )

        return diagnose_key_for_spec

    def run(self):
        self._normalize_arguments()

        disassembler = self.core.create_disassembler(
            self.arguments.arch,
            self.arguments.nvdisasm,
        )
        disassembler.load_cache(self.arguments.cache_file)
        diagnostic_feedback_hints = self._initialize_feedback_hints()
        filter_terms = self._load_filter_terms()
        instruction_items = self._build_instruction_items(disassembler, filter_terms)

        initialize_diagnostic_report(
            self.arguments.diagnose_report,
            self.core.write_diagnostic_report,
        )
        incremental_reporter = IncrementalDiagnosticReporter(
            self.arguments.diagnose_report,
            self.core.write_diagnostic_report,
        )
        diagnose_key_for_spec = self._make_diagnose_key_for_spec(disassembler)

        def analyze_instruction_with_feedback_local(
            analysis_key,
            inst,
            expected_family_head=None,
            allow_expensive_cache_recovery=True,
        ):
            return analyze_instruction_with_feedback(
                analysis_key=analysis_key,
                inst=inst,
                disassembler=disassembler,
                arch_code=self.arguments.arch_code,
                diagnose_only=self.arguments.diagnose_only,
                operand_interactions=self.arguments.operand_interactions,
                diagnose_light=self.arguments.diagnose_light,
                diagnostic_feedback_hints=diagnostic_feedback_hints,
                extract_parsed_key_from_analysis_key=self.core.extract_parsed_key_from_analysis_key,
                diagnose_key_for_spec=diagnose_key_for_spec,
                incremental_reporter=incremental_reporter,
                diagnostic_entry_score=self.core.diagnostic_entry_score,
                diagnostic_entry_has_feedback=self.core.diagnostic_entry_has_feedback,
                build_diagnostic_feedback_hints=self.core.build_diagnostic_feedback_hints,
                select_feedback_seed_instruction=self.core.select_feedback_seed_instruction,
                extract_mnemonic_head_from_disasm=self.core.extract_mnemonic_head_from_disasm,
                instruction_analysis_pipeline=self.core.instruction_analysis_pipeline,
                expected_family_head=expected_family_head,
                allow_expensive_cache_recovery=allow_expensive_cache_recovery,
            )

        analysis_result = run_instruction_analysis(
            instruction_items=instruction_items,
            num_parallel=self.arguments.num_parallel,
            analyze_instruction_with_feedback_fn=analyze_instruction_with_feedback_local,
        )
        filtered_analysis = analysis_result

        if self.arguments.diagnose_only:
            try:
                if handle_diagnose_only(
                    filtered_analysis=filtered_analysis,
                    diagnose_missing=self.arguments.diagnose_missing,
                    exact_key=self.arguments.exact_key,
                    diagnose_report=self.arguments.diagnose_report,
                    family_key_delim=self.core.FAMILY_KEY_DELIM,
                    diagnose_key_for_spec=diagnose_key_for_spec,
                    write_report_fn=self.core.write_diagnostic_report,
                ):
                    return
            except Exception:
                _report_nonfatal_exception("diagnose-only handling")

        kept_analysis = {
            key: spec
            for key, spec in filtered_analysis.items()
            if spec is not None and not getattr(spec, "filtered", False)
        }
        recovered_missing_operands = []
        replaced = []
        dropped = []

        try:
            postprocessed = postprocess_analysis_results(
                filtered_analysis=filtered_analysis,
                disassembler=disassembler,
                arch_code=self.arguments.arch_code,
                encoding_range_type=self.core.EncodingRangeType,
                enable_cache_fallback=self.core.ENABLE_CACHE_FALLBACK,
                is_placeholder_modifier=self.core.is_placeholder_modifier,
                has_placeholder_modifier=self.core.has_placeholder_modifier,
                filter_non_placeholder_modifiers=self.core.filter_non_placeholder_modifiers,
                recover_operand_spec_from_cache=self.core.recover_operand_spec_from_cache,
                backfill_modifier_tables_from_ranges=self.core.backfill_modifier_tables_from_ranges,
                safe_flat_operand_count=self.core.safe_flat_operand_count,
                safe_operand_range_count=self.core.safe_operand_range_count,
                safe_parsed_key=self.core.safe_parsed_key,
                variable_operand_indices_for_analysis_key=self.core.variable_operand_indices_for_analysis_key,
                extract_parsed_key_from_analysis_key=self.core.extract_parsed_key_from_analysis_key,
                find_clean_cache_candidate=self.core.find_clean_cache_candidate,
                instruction_analysis_pipeline=self.core.instruction_analysis_pipeline,
                spec_structural_fingerprint=self.core.spec_structural_fingerprint,
                spec_family_merge_signature=self.core.spec_family_merge_signature,
                spec_coverage_quality_score=self.core.spec_coverage_quality_score,
                spec_coverage_fold_signature=self.core.spec_coverage_fold_signature,
                spec_coverage_profile=self.core.spec_coverage_profile,
                coverage_profile_is_superset=self.core.coverage_profile_is_superset,
            )
            kept_analysis = postprocessed["kept_analysis"]
            recovered_missing_operands = postprocessed["recovered_missing_operands"]
            replaced = postprocessed["replaced"]
            dropped = postprocessed["dropped"]
        except Exception:
            _report_nonfatal_exception("postprocess analysis results")

        analysis_serialized = {}
        try:
            analysis_serialized = finalize_serialized_analysis(
                kept_analysis=kept_analysis,
                dropped=dropped,
                disassembler=disassembler,
                arch_code=self.arguments.arch_code,
                is_placeholder_modifier=self.core.is_placeholder_modifier,
                enable_cache_fallback=self.core.ENABLE_CACHE_FALLBACK,
                find_clean_cache_candidate=self.core.find_clean_cache_candidate,
                instruction_analysis_pipeline=self.core.instruction_analysis_pipeline,
            )
        except Exception:
            _report_nonfatal_exception("finalize serialized analysis")
            for key, spec in list(kept_analysis.items()):
                try:
                    analysis_serialized[key] = spec.to_json_obj()
                except Exception:
                    _report_nonfatal_exception(
                        "fallback final serialization", key
                    )
                    if key not in dropped:
                        dropped.append(key)
                    try:
                        del kept_analysis[key]
                    except Exception:
                        pass

        try:
            with open("isa.json", "w") as isa_json_file:
                isa_json_file.write(json.dumps(analysis_serialized))
        except Exception:
            _report_nonfatal_exception("write isa.json")

        write_verification_log(
            path="verification.log",
            recovered_missing_operands=recovered_missing_operands,
            replaced=replaced,
            dropped=dropped,
        )

        try:
            emit_miss_report(
                kept_analysis_map=kept_analysis,
                report_path=self.arguments.diagnose_report,
                diagnose_key_for_spec=diagnose_key_for_spec,
                write_report_fn=self.core.write_diagnostic_report,
            )
        except Exception:
            _report_nonfatal_exception("emit miss report")

        try:
            analysis_result = sorted(
                [(key, spec) for key, spec in kept_analysis.items()],
                key=lambda item: item[0],
            )
            base_names = group_specs_by_base_name(analysis_result)
            write_html_outputs(
                base_names=base_names,
                output_dir="output",
                arch=self.arguments.arch,
                instruction_desc_header=self.core.INSTRUCTION_DESC_HEADER,
                instviz_header=self.core.INSTVIZ_HEADER,
                prepare_spec_for_html_fn=self.core.prepare_spec_for_html,
                render_spec_html_fn=self.core.render_spec_html,
            )
        except Exception:
            _report_nonfatal_exception("write html outputs")

        if self.arguments.dump_cache:
            try:
                disassembler.dump_cache(self.arguments.cache_file)
            except Exception:
                _report_nonfatal_exception("dump cache")
