from collections import defaultdict

from .parser import InstructionParser


def recover_operand_spec_from_cache(
    disassembler,
    target_key,
    arch_code,
    enable_cache_fallback,
    cache_iter_by_key,
    instruction_analysis_pipeline,
    encoding_range_type,
    max_candidates=256,
):
    if not enable_cache_fallback or not target_key:
        return None

    tried = 0
    for inst_b, asm_text in cache_iter_by_key(disassembler, target_key):
        if tried >= max_candidates:
            break
        try:
            if not asm_text or not isinstance(asm_text, str):
                continue
            lines = [line for line in asm_text.splitlines() if line.strip()]
            if not lines:
                continue
            parsed = InstructionParser.parseInstruction(lines[-1])
            if parsed.get_key() != target_key:
                continue
            tried += 1
        except Exception:
            continue

        try:
            recovered_spec = instruction_analysis_pipeline(
                inst_b, disassembler, arch_code
            )
        except Exception:
            recovered_spec = None
        if recovered_spec is None or getattr(recovered_spec, "filtered", False):
            continue
        try:
            operand_ranges = recovered_spec.ranges._find(encoding_range_type.OPERAND)
        except Exception:
            operand_ranges = []
        if operand_ranges:
            return recovered_spec

    return None


def safe_operand_range_count(spec, encoding_range_type):
    try:
        return len(spec.ranges._find(encoding_range_type.OPERAND))
    except Exception:
        return 0


def safe_flat_operand_count(spec):
    try:
        if hasattr(spec.parsed, "get_flat_operands"):
            return len(spec.parsed.get_flat_operands())
        return len(getattr(spec.parsed, "operands", []))
    except Exception:
        return 0


def safe_parsed_key(spec):
    try:
        return spec.parsed.get_key()
    except Exception:
        return None


def extract_parsed_key_from_analysis_key(analysis_key, family_key_delim):
    try:
        if not isinstance(analysis_key, str) or "." not in analysis_key:
            return None
        parsed_part = analysis_key.split(".", 1)[1]
        if family_key_delim in parsed_part:
            parsed_part = parsed_part.split(family_key_delim, 1)[0]
        parsed_part = parsed_part.strip()
        return parsed_part if parsed_part else None
    except Exception:
        return None


def extract_opcode_from_analysis_key(analysis_key):
    try:
        if not isinstance(analysis_key, str) or "." not in analysis_key:
            return None
        opcode_text = analysis_key.split(".", 1)[0].strip()
        return int(opcode_text)
    except Exception:
        return None


def extract_mnemonic_head_from_disasm(disasm_text):
    try:
        if not isinstance(disasm_text, str) or not disasm_text:
            return ""
        lines = [line for line in disasm_text.splitlines() if line.strip()]
        line = lines[-1].strip() if lines else disasm_text.strip()
        if not line:
            return ""
        parts = line.split()
        if not parts:
            return ""
        head = parts[0]
        if head.startswith("@") and len(parts) >= 2:
            head = parts[1]
        return head.strip()
    except Exception:
        return ""


def rank_cache_candidate_for_exact(
    asm_text,
    instruction_parser,
    is_placeholder_modifier,
):
    if not isinstance(asm_text, str) or not asm_text:
        return (0, -1, -9999)
    upper = asm_text.upper()
    has_placeholder = ("???" in asm_text) or ("INVALID" in upper)
    concrete = 0
    placeholders = 0
    try:
        lines = [line for line in asm_text.splitlines() if line.strip()]
        if lines:
            parsed = instruction_parser.parseInstruction(lines[-1])
            for token in (getattr(parsed, "modifiers", []) or []):
                if isinstance(token, str) and token:
                    if is_placeholder_modifier(token):
                        placeholders += 1
                    else:
                        concrete += 1
            for operand in parsed.get_flat_operands():
                for token in (getattr(operand, "modifiers", []) or []):
                    if isinstance(token, str) and token:
                        if is_placeholder_modifier(token):
                            placeholders += 1
                        else:
                            concrete += 1
    except Exception:
        pass
    clean = 0 if has_placeholder else 1
    return (clean, concrete, -placeholders)


def semantic_inst_popcount(inst_bytes):
    try:
        data = bytes(inst_bytes)
    except Exception:
        return 0
    semantic_prefix = data[:13]
    try:
        return sum(byte.bit_count() for byte in semantic_prefix)
    except Exception:
        return sum(bin(byte).count("1") for byte in semantic_prefix)


def select_instruction_by_exact_key(
    disassembler,
    exact_key,
    family_key_delim,
    cache_iter_by_key,
    get_bit_range,
    extract_mnemonic_head_from_disasm_fn,
    rank_cache_candidate_for_exact_fn,
    semantic_inst_popcount_fn,
):
    if not isinstance(exact_key, str) or not exact_key:
        return {}

    opcode_target = None
    parsed_part = exact_key
    if "." in exact_key:
        maybe_opcode, rest = exact_key.split(".", 1)
        parsed_part = rest
        try:
            opcode_target = int(maybe_opcode)
        except Exception:
            opcode_target = None

    family_target = None
    parsed_key = parsed_part
    if family_key_delim in parsed_part:
        parsed_key, family_target = parsed_part.split(family_key_delim, 1)
    parsed_key = parsed_key.strip()
    if not parsed_key:
        return {}

    best = None
    best_rank = None
    for inst_b, asm_text in cache_iter_by_key(disassembler, parsed_key):
        try:
            if opcode_target is not None and get_bit_range(inst_b, 0, 12) != opcode_target:
                continue
            if family_target:
                head = extract_mnemonic_head_from_disasm_fn(asm_text)
                if head != family_target:
                    continue
        except Exception:
            continue
        rank = rank_cache_candidate_for_exact_fn(asm_text) + (
            semantic_inst_popcount_fn(inst_b),
        )
        if best is None or rank > best_rank:
            best = bytes(inst_b)
            best_rank = rank

    if best is None:
        return {}
    return {exact_key: best}


CONTROL_RANGE_TYPES = frozenset(
    {
        "stall",
        "y",
        "r-bar",
        "w-bar",
        "b-mask",
        "reuse",
    }
)


def _normalize_modifier_name_for_signature(name, is_placeholder_modifier):
    if not isinstance(name, str):
        return ""
    clean = name.rstrip(".").strip()
    if not clean or is_placeholder_modifier(clean):
        return ""
    return clean


def _normalized_modifier_rows_for_signature(rows, is_placeholder_modifier):
    normalized = []
    for value, name in rows or []:
        try:
            normalized_value = int(value)
        except Exception:
            continue
        normalized.append(
            (
                normalized_value,
                _normalize_modifier_name_for_signature(name, is_placeholder_modifier),
            )
        )
    normalized.sort()
    return tuple(normalized)


def _modifier_name_set_from_rows(rows, is_placeholder_modifier):
    names = set()
    for _value, name in rows or []:
        clean = _normalize_modifier_name_for_signature(name, is_placeholder_modifier)
        if clean:
            names.add(clean)
    return names


def spec_optional_family_tokens(spec, is_placeholder_modifier):
    optional_tokens = set()
    for group in (getattr(spec, "modifiers", []) or []):
        if not group or len(group) <= 1:
            continue
        has_empty = False
        group_tokens = set()
        for _value, name in group:
            if not isinstance(name, str):
                has_empty = True
                continue
            clean = name.rstrip(".").strip()
            if not clean or is_placeholder_modifier(clean):
                has_empty = True
                continue
            for token in clean.split("."):
                if token and not is_placeholder_modifier(token):
                    group_tokens.add(token)
        if has_empty and group_tokens:
            optional_tokens.update(group_tokens)
    return optional_tokens


def spec_family_merge_signature(
    spec,
    safe_parsed_key,
    extract_mnemonic_head_from_disasm,
    is_placeholder_modifier,
):
    parsed_key = safe_parsed_key(spec)
    if not parsed_key:
        return None

    try:
        head = extract_mnemonic_head_from_disasm(getattr(spec, "disasm", ""))
    except Exception:
        head = None
    if not head:
        try:
            parsed = getattr(spec, "parsed", None)
            base = getattr(parsed, "base_name", None) or ""
            mods = [
                modifier.rstrip(".")
                for modifier in (getattr(parsed, "modifiers", []) or [])
                if isinstance(modifier, str)
                and modifier
                and not is_placeholder_modifier(modifier)
            ]
            head = ".".join([base] + mods) if base else ".".join(mods)
        except Exception:
            head = ""
    if not head:
        return None

    tokens = [
        token
        for token in head.split(".")
        if token and not is_placeholder_modifier(token)
    ]
    if not tokens:
        return None

    base = tokens[0]
    optional_tokens = spec_optional_family_tokens(spec, is_placeholder_modifier)
    kept_mods = [token for token in tokens[1:] if token not in optional_tokens]
    merged_family = ".".join([base] + kept_mods) if kept_mods else base
    try:
        opmods = getattr(spec, "operand_modifiers", {}) or {}
        operand_mod_sig = []
        for op_idx in sorted(opmods.keys()):
            operand_mod_sig.append(
                (
                    op_idx,
                    _normalized_modifier_rows_for_signature(
                        opmods.get(op_idx, []), is_placeholder_modifier
                    ),
                )
            )
        operand_mod_sig = tuple(operand_mod_sig)
    except Exception:
        operand_mod_sig = tuple()

    try:
        operand_flag_names = defaultdict(set)
        for rng in getattr(getattr(spec, "ranges", None), "ranges", []) or []:
            try:
                rtype = getattr(rng, "type", None)
                rtype_val = getattr(rtype, "value", rtype)
                if rtype_val != "operand_flag":
                    continue
                op_idx = getattr(rng, "operand_index", None)
                if op_idx is None:
                    continue
                clean = _normalize_modifier_name_for_signature(
                    getattr(rng, "name", None), is_placeholder_modifier
                )
                if clean:
                    operand_flag_names[int(op_idx)].add(clean)
            except Exception:
                continue
        operand_flag_sig = tuple(
            (op_idx, tuple(sorted(names)))
            for op_idx, names in sorted(operand_flag_names.items())
            if names
        )
    except Exception:
        operand_flag_sig = tuple()

    return (parsed_key, merged_family, operand_mod_sig, operand_flag_sig)


def spec_structural_fingerprint(spec, is_placeholder_modifier):
    try:
        parsed = getattr(spec, "parsed", None)
        try:
            parsed_key = parsed.get_key() if parsed is not None else ""
        except Exception:
            parsed_key = ""
        try:
            parsed_mods = tuple(
                modifier.rstrip(".")
                for modifier in (getattr(parsed, "modifiers", []) or [])
                if isinstance(modifier, str)
                and modifier
                and not is_placeholder_modifier(modifier)
            )
        except Exception:
            parsed_mods = tuple()

        range_sig = []
        try:
            for rng in getattr(getattr(spec, "ranges", None), "ranges", []) or []:
                try:
                    name = getattr(rng, "name", None)
                    if isinstance(name, str):
                        name = name.rstrip(".")
                        if is_placeholder_modifier(name):
                            name = None
                    elif not name:
                        name = None
                    range_sig.append(
                        (
                            str(getattr(rng, "type", "")),
                            int(getattr(rng, "start", -1)),
                            int(getattr(rng, "length", -1)),
                            getattr(rng, "operand_index", None),
                            name,
                            getattr(rng, "constant", None),
                        )
                    )
                except Exception:
                    continue
        except Exception:
            range_sig = []

        mod_sig = []
        try:
            for group in getattr(spec, "modifiers", []) or []:
                rows = []
                for value, name in group:
                    try:
                        normalized_name = name.rstrip(".") if isinstance(name, str) else name
                    except Exception:
                        normalized_name = name
                    if (
                        isinstance(normalized_name, str)
                        and is_placeholder_modifier(normalized_name)
                    ):
                        continue
                    rows.append((int(value), normalized_name))
                mod_sig.append(tuple(rows))
        except Exception:
            mod_sig = []

        op_mod_sig = []
        try:
            opmods = getattr(spec, "operand_modifiers", {}) or {}
            for op_idx in sorted(opmods.keys()):
                rows = []
                for value, name in opmods.get(op_idx, []) or []:
                    try:
                        normalized_name = name.rstrip(".") if isinstance(name, str) else name
                    except Exception:
                        normalized_name = name
                    if (
                        isinstance(normalized_name, str)
                        and is_placeholder_modifier(normalized_name)
                    ):
                        continue
                    rows.append((int(value), normalized_name))
                op_mod_sig.append((op_idx, tuple(rows)))
        except Exception:
            op_mod_sig = []

        return (
            parsed_key,
            parsed_mods,
            tuple(range_sig),
            tuple(mod_sig),
            tuple(op_mod_sig),
        )
    except Exception:
        return ("__fallback__", id(spec))


def spec_coverage_fold_signature(spec, is_placeholder_modifier):
    try:
        parsed = getattr(spec, "parsed", None)
        parsed_key = parsed.get_key() if parsed is not None else ""
    except Exception:
        parsed_key = ""
    if not parsed_key:
        return None

    try:
        mod_sig = tuple(
            _normalized_modifier_rows_for_signature(group, is_placeholder_modifier)
            for group in (getattr(spec, "modifiers", []) or [])
        )
    except Exception:
        mod_sig = tuple()

    try:
        opmods = getattr(spec, "operand_modifiers", {}) or {}
        op_mod_sig = []
        for op_idx in sorted(opmods.keys()):
            op_mod_sig.append(
                (
                    op_idx,
                    _normalized_modifier_rows_for_signature(
                        opmods.get(op_idx, []), is_placeholder_modifier
                    ),
                )
            )
        op_mod_sig = tuple(op_mod_sig)
    except Exception:
        op_mod_sig = tuple()

    try:
        operand_flag_names = defaultdict(set)
        for rng in getattr(getattr(spec, "ranges", None), "ranges", []) or []:
            try:
                rtype = getattr(rng, "type", None)
                rtype_val = getattr(rtype, "value", rtype)
                if rtype_val != "operand_flag":
                    continue
                op_idx = getattr(rng, "operand_index", None)
                if op_idx is None:
                    continue
                clean = _normalize_modifier_name_for_signature(
                    getattr(rng, "name", None), is_placeholder_modifier
                )
                if clean:
                    operand_flag_names[int(op_idx)].add(clean)
            except Exception:
                continue
        operand_flag_sig = tuple(
            (op_idx, tuple(sorted(names)))
            for op_idx, names in sorted(operand_flag_names.items())
            if names
        )
    except Exception:
        operand_flag_sig = tuple()

    try:
        opcode_modis = tuple(
            sorted(
                _normalize_modifier_name_for_signature(token, is_placeholder_modifier)
                for token in (getattr(spec, "opcode_modis", []) or [])
                if _normalize_modifier_name_for_signature(
                    token, is_placeholder_modifier
                )
            )
        )
    except Exception:
        opcode_modis = tuple()

    table_name_count = 0
    for group in mod_sig:
        for _value, name in group:
            if name:
                table_name_count += 1
    for _op_idx, rows in op_mod_sig:
        for _value, name in rows:
            if name:
                table_name_count += 1
    for _op_idx, names in operand_flag_sig:
        table_name_count += len(names)
    if table_name_count == 0:
        return None

    return (parsed_key, opcode_modis, mod_sig, op_mod_sig, operand_flag_sig)


def spec_coverage_profile(spec, is_placeholder_modifier):
    try:
        parsed = getattr(spec, "parsed", None)
        parsed_key = parsed.get_key() if parsed is not None else ""
    except Exception:
        parsed_key = ""
    if not parsed_key:
        return None

    opcode_names = set()
    try:
        for token in (getattr(spec, "opcode_modis", []) or []):
            clean = _normalize_modifier_name_for_signature(
                token, is_placeholder_modifier
            )
            if clean:
                opcode_names.add(clean)
    except Exception:
        opcode_names = set()

    mod_group_names = []
    try:
        for group in (getattr(spec, "modifiers", []) or []):
            mod_group_names.append(
                _modifier_name_set_from_rows(group, is_placeholder_modifier)
            )
    except Exception:
        mod_group_names = []

    operand_mod_names = {}
    try:
        opmods = getattr(spec, "operand_modifiers", {}) or {}
        for op_idx in sorted(opmods.keys()):
            operand_mod_names[op_idx] = _modifier_name_set_from_rows(
                opmods.get(op_idx, []),
                is_placeholder_modifier,
            )
    except Exception:
        operand_mod_names = {}

    operand_flag_names = {}
    try:
        for rng in getattr(getattr(spec, "ranges", None), "ranges", []) or []:
            try:
                rtype = getattr(rng, "type", None)
                rtype_val = getattr(rtype, "value", rtype)
                if rtype_val != "operand_flag":
                    continue
                op_idx = getattr(rng, "operand_index", None)
                if op_idx is None:
                    continue
                clean = _normalize_modifier_name_for_signature(
                    getattr(rng, "name", None), is_placeholder_modifier
                )
                if not clean:
                    continue
                operand_flag_names.setdefault(int(op_idx), set()).add(clean)
            except Exception:
                continue
    except Exception:
        operand_flag_names = {}

    has_named = bool(opcode_names)
    if not has_named:
        for names in mod_group_names:
            if names:
                has_named = True
                break
    if not has_named:
        for names in operand_mod_names.values():
            if names:
                has_named = True
                break
    if not has_named:
        for names in operand_flag_names.values():
            if names:
                has_named = True
                break
    if not has_named:
        return None

    return {
        "parsed_key": parsed_key,
        "opcode_names": opcode_names,
        "mod_group_names": mod_group_names,
        "operand_mod_names": operand_mod_names,
        "operand_flag_names": operand_flag_names,
    }


def coverage_profile_is_superset(candidate, target):
    try:
        if not candidate or not target:
            return False
        if candidate.get("parsed_key") != target.get("parsed_key"):
            return False

        cand_opcode = candidate.get("opcode_names", set()) or set()
        tgt_opcode = target.get("opcode_names", set()) or set()
        if tgt_opcode and not tgt_opcode.issubset(cand_opcode):
            return False

        cand_groups = candidate.get("mod_group_names", []) or []
        tgt_groups = target.get("mod_group_names", []) or []
        if len(cand_groups) < len(tgt_groups):
            return False
        for idx, tgt_names in enumerate(tgt_groups):
            if not tgt_names:
                continue
            cand_names = cand_groups[idx] if idx < len(cand_groups) else set()
            if not tgt_names.issubset(cand_names):
                return False

        cand_opmods = candidate.get("operand_mod_names", {}) or {}
        tgt_opmods = target.get("operand_mod_names", {}) or {}
        for op_idx, tgt_names in tgt_opmods.items():
            if not tgt_names:
                continue
            cand_names = cand_opmods.get(op_idx, set()) or set()
            if not tgt_names.issubset(cand_names):
                return False

        cand_opflags = candidate.get("operand_flag_names", {}) or {}
        tgt_opflags = target.get("operand_flag_names", {}) or {}
        for op_idx, tgt_names in tgt_opflags.items():
            if not tgt_names:
                continue
            cand_names = cand_opflags.get(op_idx, set()) or set()
            if not tgt_names.issubset(cand_names):
                return False
        return True
    except Exception:
        return False


def spec_coverage_quality_score(spec, is_placeholder_modifier):
    predicate_bits = 0
    control_bits = 0
    operand_bits = 0
    modifier_bits = 0
    operand_modifier_bits = 0
    operand_flag_bits = 0
    for rng in getattr(getattr(spec, "ranges", None), "ranges", []) or []:
        try:
            rtype = getattr(rng, "type", None)
            rtype_val = getattr(rtype, "value", rtype)
            rlen = int(getattr(rng, "length", 0) or 0)
        except Exception:
            continue
        if rtype_val == "predicate":
            predicate_bits += rlen
        elif rtype_val in CONTROL_RANGE_TYPES:
            control_bits += rlen
        elif rtype_val == "operand":
            operand_bits += rlen
        elif rtype_val == "modifier":
            modifier_bits += rlen
        elif rtype_val == "operand_modifier":
            operand_modifier_bits += rlen
        elif rtype_val == "operand_flag":
            operand_flag_bits += rlen

    try:
        parsed_mod_count = sum(
            1
            for token in (getattr(spec.parsed, "modifiers", []) or [])
            if isinstance(token, str)
            and _normalize_modifier_name_for_signature(
                token, is_placeholder_modifier
            )
        )
    except Exception:
        parsed_mod_count = 0

    try:
        table_mod_name_count = sum(
            1
            for group in (getattr(spec, "modifiers", []) or [])
            for _value, name in (group or [])
            if _normalize_modifier_name_for_signature(name, is_placeholder_modifier)
        )
    except Exception:
        table_mod_name_count = 0

    return (
        predicate_bits,
        control_bits,
        operand_bits,
        modifier_bits,
        operand_modifier_bits,
        operand_flag_bits,
        parsed_mod_count,
        table_mod_name_count,
    )
