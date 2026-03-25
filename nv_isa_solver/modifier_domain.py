import logging
import re
from collections import Counter

DIAGNOSE_IGNORED_TOKENS = frozenset({"reuse"})


def is_placeholder_modifier(modifier: str) -> bool:
    try:
        if not modifier or not isinstance(modifier, str):
            return True
        if "???" in modifier or "INVALID" in modifier.upper():
            return True
        for token in [part for part in re.split(r"\.", modifier) if part != ""]:
            if token.startswith("???") or token.upper().startswith("INVALID"):
                return True
            try:
                if re.match(r"^(R|UR|P|UP|SR)_[0-9]+$", token):
                    return True
            except Exception:
                pass
        return False
    except Exception:
        return True


def sanitize_modifier_display_name(name, is_placeholder_modifier_fn=is_placeholder_modifier):
    if not name or not isinstance(name, str):
        return None
    clean = name.rstrip(".").strip()
    if not clean:
        return ""
    if is_placeholder_modifier_fn(clean):
        return None
    return clean + "."


def split_token_parts(token: str, is_placeholder_modifier_fn=is_placeholder_modifier):
    parts = []
    if not isinstance(token, str):
        return parts
    for part in token.rstrip(".;").split("."):
        part = part.strip()
        if not part:
            continue
        if is_placeholder_modifier_fn(part):
            continue
        parts.append(part)
    return parts


def is_diagnose_noise_token(
    token: str,
    is_placeholder_modifier_fn=is_placeholder_modifier,
    ignored_tokens=DIAGNOSE_IGNORED_TOKENS,
):
    if not isinstance(token, str):
        return True
    text = token.strip().rstrip(".;")
    if not text:
        return True
    if is_placeholder_modifier_fn(text):
        return True
    if text.lower() in ignored_tokens:
        return True
    if re.fullmatch(r"[+-]?\d+", text):
        count = len(text.lstrip("+-"))
        if count <= 1 or count >= 8:
            return True
    if re.fullmatch(r"[+-]?\d+\.\d+", text):
        return True
    if re.fullmatch(r"[+-]?0x[0-9a-fA-F]+", text):
        return True
    return False


def get_operand_modifier_rows(operand_modifiers, op_idx, rng=None):
    if not operand_modifiers:
        return []
    if rng is not None and op_idx is not None:
        group_id = getattr(rng, "group_id", None)
        group_key = ("group", op_idx, group_id) if group_id is not None else None
        range_key = (op_idx, rng.start, rng.length)
        out = (
            (operand_modifiers.get(group_key) if group_key is not None else None)
            or operand_modifiers.get(range_key)
            or operand_modifiers.get(op_idx)
        )
    else:
        out = operand_modifiers.get(op_idx) if op_idx is not None else None
    return list(out) if out else []


def filter_non_placeholder_modifiers(modifiers, is_placeholder_modifier_fn=is_placeholder_modifier):
    return [
        modifier
        for modifier in (modifiers or [])
        if isinstance(modifier, str) and not is_placeholder_modifier_fn(modifier)
    ]


def has_placeholder_modifier(modifiers, is_placeholder_modifier_fn=is_placeholder_modifier):
    return any(is_placeholder_modifier_fn(modifier) for modifier in (modifiers or []))


def chosen_display_from_rows(rows, encoded_val, is_placeholder_modifier_fn=is_placeholder_modifier):
    saw_encoded_row = False
    for value, name in rows:
        if value != encoded_val:
            continue
        saw_encoded_row = True
        if isinstance(name, str) and not is_placeholder_modifier_fn(name):
            return name.rstrip(".")
        return None
    if saw_encoded_row:
        return None
    for _value, name in rows:
        if isinstance(name, str) and not is_placeholder_modifier_fn(name):
            return name.rstrip(".")
    return None


def sanitize_disasm(disasm_text: str) -> str:
    try:
        if not disasm_text or not isinstance(disasm_text, str):
            return disasm_text
        disasm_text = re.sub(r"\?+\d*", "", disasm_text)
        disasm_text = re.sub(r"INVALID\w*", "", disasm_text, flags=re.IGNORECASE)
        disasm_text = re.sub(r"(?<=\.|^)0(?=\.|$)", "", disasm_text)
        while ".." in disasm_text:
            disasm_text = disasm_text.replace("..", ".")
        return disasm_text.strip()
    except Exception:
        return disasm_text


def clean_modifier_row_name(name, is_placeholder_modifier_fn=is_placeholder_modifier):
    try:
        if not isinstance(name, str):
            return ""
        clean = name.rstrip(".").strip()
        if not clean or clean == "-" or is_placeholder_modifier_fn(clean):
            return ""
        return clean
    except Exception:
        return ""


def unify_spec_modifiers(
    spec,
    *,
    encoding_range_type,
    get_bit_range_fn,
    is_placeholder_modifier_fn=is_placeholder_modifier,
    filter_non_placeholder_modifiers_fn=None,
):
    if filter_non_placeholder_modifiers_fn is None:
        filter_non_placeholder_modifiers_fn = filter_non_placeholder_modifiers
    try:
        mod_ranges = spec.ranges._find(encoding_range_type.MODIFIER)
        if not mod_ranges:
            return
        parsed_mods = getattr(spec.parsed, "modifiers", []) or []
        vals = []
        cand_lists = []
        for idx, rng in enumerate(mod_ranges):
            try:
                val = get_bit_range_fn(spec.ranges.inst, rng.start, rng.start + rng.length)
            except Exception:
                val = 0
            vals.append(val)
            candidates = []
            try:
                if spec.modifiers and idx < len(spec.modifiers):
                    for value, name in spec.modifiers[idx]:
                        if not isinstance(name, str):
                            continue
                        clean = name.rstrip(".").strip()
                        if clean:
                            if is_placeholder_modifier_fn(clean):
                                continue
                            candidates.append((value, clean))
                        else:
                            candidates.append((value, ""))
            except Exception:
                pass
            cand_lists.append(candidates)

        parsed_tokens = [
            modifier.rstrip(".")
            for modifier in filter_non_placeholder_modifiers_fn(parsed_mods)
        ]
        try:
            def _token_priority(token: str):
                if re.match(r"^E\d+M\d+$", token):
                    return 0
                return 1

            parsed_tokens = sorted(parsed_tokens, key=_token_priority)
        except Exception:
            pass

        mapped_parser = [None] * len(mod_ranges)
        for parsed_token in parsed_tokens:
            assigned = False
            for idx, candidates in enumerate(cand_lists):
                if mapped_parser[idx] is not None:
                    continue
                names = [name for (_value, name) in candidates]
                if parsed_token in names:
                    mapped_parser[idx] = parsed_token
                    assigned = True
                    break
            if assigned:
                continue
            for idx, candidates in enumerate(cand_lists):
                if mapped_parser[idx] is not None:
                    continue
                names = [name for (_value, name) in candidates]
                for name in names:
                    try:
                        if parsed_token and name and (parsed_token in name or name in parsed_token):
                            mapped_parser[idx] = parsed_token
                            assigned = True
                            break
                    except Exception:
                        continue
                if assigned:
                    break
            if assigned:
                continue
            for idx, candidates in enumerate(cand_lists):
                if mapped_parser[idx] is not None:
                    continue
                names = [name for (_value, name) in candidates]
                for name in names:
                    try:
                        if re.search(r"\d", parsed_token) and re.search(r"\d", name):
                            if re.sub(r"\D", "", parsed_token) == re.sub(r"\D", "", name):
                                mapped_parser[idx] = parsed_token
                                assigned = True
                                break
                    except Exception:
                        continue
                if assigned:
                    break
            if assigned:
                continue
            for idx in range(len(mapped_parser)):
                if mapped_parser[idx] is None:
                    mapped_parser[idx] = parsed_token
                    break

        new_groups = []
        for idx, rng in enumerate(mod_ranges):
            val = vals[idx]
            candidates = cand_lists[idx]
            enc_name = ""
            has_explicit_encoded_candidate = False
            for value, name in candidates:
                if value == val:
                    has_explicit_encoded_candidate = True
                    enc_name = name
                    break

            enc_display = enc_name
            mapped = mapped_parser[idx]
            if not enc_display and mapped and not has_explicit_encoded_candidate:
                try:
                    if mapped != "" and not is_placeholder_modifier_fn(mapped):
                        for _candidate_value, candidate_name in candidates:
                            try:
                                if candidate_name == mapped:
                                    enc_display = mapped
                                    break
                            except Exception:
                                continue
                except Exception:
                    pass

            group = []
            if enc_display:
                group.append((val, enc_display + "."))
            else:
                group.append((val, ""))

            seen = {val}
            for value, name in candidates:
                if value in seen:
                    continue
                group.append((value, name + "." if name else ""))
                seen.add(value)

            new_groups.append(group)

            try:
                logger = logging.getLogger(__name__)
                for log_idx, log_rng in enumerate(mod_ranges):
                    log_val = vals[log_idx] if log_idx < len(vals) else None
                    log_candidates = cand_lists[log_idx] if log_idx < len(cand_lists) else []
                    names = [name for (_value, name) in log_candidates]
                    mapped_name = mapped_parser[log_idx] if log_idx < len(mapped_parser) else None
                    chosen = None
                    try:
                        if new_groups and log_idx < len(new_groups) and new_groups[log_idx]:
                            chosen = new_groups[log_idx][0][1]
                    except Exception:
                        chosen = None
                    logger.info(
                        "unify_spec_modifiers: range_idx=%s start=%s len=%s candidates=%s mapped_parser=%s encoded_val=%s chosen_display=%s",
                        log_idx,
                        log_rng.start,
                        log_rng.length,
                        names,
                        mapped_name,
                        log_val,
                        chosen,
                    )
            except Exception:
                pass

        spec.modifiers = new_groups
    except Exception:
        return


def factorize_operand_modifier_groups_from_rows(
    ranges,
    operand_modifier_values,
    *,
    encoding_range_type,
    encoding_range_cls,
    get_bit_range_fn,
    is_placeholder_modifier_fn=is_placeholder_modifier,
    find_modifier_difference_fn=None,
):
    try:
        if not isinstance(operand_modifier_values, dict):
            return operand_modifier_values, ranges
        if find_modifier_difference_fn is None:
            return operand_modifier_values, ranges

        def _clean_name(name):
            try:
                if not name or not isinstance(name, str):
                    return ""
                clean = name.rstrip(".").strip()
                if not clean or clean == "-":
                    return ""
                kept = [
                    part.strip()
                    for part in clean.split(".")
                    if part.strip() and not is_placeholder_modifier_fn(part.strip())
                ]
                if not kept:
                    return ""
                return ".".join(kept) + "."
            except Exception:
                return ""

        def _name_tokens(name):
            clean = _clean_name(name)
            if not clean:
                return []
            return [part for part in clean.rstrip(".").split(".") if part]

        def _signed_name_map(name):
            out = {}
            for token in _name_tokens(name):
                out[token] = out.get(token, 0) + 1
            return out

        def _signed_sub(lhs, rhs):
            out = {}
            for token in set(lhs) | set(rhs):
                delta = int(lhs.get(token, 0)) - int(rhs.get(token, 0))
                if delta:
                    out[token] = delta
            return out

        def _signed_add(*maps):
            out = {}
            for mapping in maps:
                for token, count in (mapping or {}).items():
                    out[token] = out.get(token, 0) + int(count)
                    if out[token] == 0:
                        out.pop(token, None)
            return out

        def _sanitize_split_group_tokens(left_rows, right_rows, left_base, right_base):
            try:
                left_controlled = set()
                right_controlled = set()
                for value, name in left_rows:
                    if int(value) == int(left_base):
                        continue
                    left_controlled.update(_name_tokens(name))
                for value, name in right_rows:
                    if int(value) == int(right_base):
                        continue
                    right_controlled.update(_name_tokens(name))

                def _strip(name, banned):
                    tokens = [token for token in _name_tokens(name) if token not in banned]
                    return ".".join(tokens) + ("." if tokens else "")

                new_left = [(value, _strip(name, right_controlled)) for value, name in left_rows]
                new_right = [
                    (value, _strip(name, left_controlled)) for value, name in right_rows
                ]
                return new_left, new_right
            except Exception:
                return left_rows, right_rows

        def _maybe_split_into_operand_flags(rng, base_val, full_name_map):
            try:
                if int(getattr(rng, "length", 0) or 0) != 2:
                    return None

                value_tokens = {
                    int(value): set(_name_tokens(name))
                    for value, name in full_name_map.items()
                    if int(value) in (0, 1, 2, 3)
                }
                if len(value_tokens) != 4:
                    return None

                inferred = []
                for bit_off in range(2):
                    bit_mask = 1 << bit_off
                    token_name = None
                    bit_one_enables_token = None
                    ok = True
                    for value in range(4):
                        if value & bit_mask:
                            continue
                        other = value | bit_mask
                        toks0 = value_tokens.get(value, set())
                        toks1 = value_tokens.get(other, set())
                        sym = toks0 ^ toks1
                        if len(sym) != 1:
                            ok = False
                            break
                        cur_name = next(iter(sym))
                        cur_orientation = cur_name in toks1 and cur_name not in toks0
                        if token_name is None:
                            token_name = cur_name
                            bit_one_enables_token = cur_orientation
                        elif (
                            token_name != cur_name
                            or bit_one_enables_token != cur_orientation
                        ):
                            ok = False
                            break
                    if not ok or not token_name:
                        return None
                    inferred.append((bit_off, token_name, bit_one_enables_token))

                for value in range(4):
                    expected = set()
                    for bit_off, token_name, bit_one_enables_token in inferred:
                        bit_is_one = bool(value & (1 << bit_off))
                        if bit_is_one == bit_one_enables_token:
                            expected.add(token_name)
                    if value_tokens.get(value, set()) != expected:
                        return None

                flags = []
                for bit_off, token_name, _bit_one_enables_token in inferred:
                    flags.append(
                        encoding_range_cls(
                            encoding_range_type.OPERAND_FLAG,
                            rng.start + bit_off,
                            1,
                            operand_index=rng.operand_index,
                            name=token_name,
                        )
                    )
                return flags
            except Exception:
                return None

        changed_any = False
        while True:
            changed = False
            new_ranges_list = []
            new_operand_mods = {}

            for rng in ranges.ranges:
                if rng.type != encoding_range_type.OPERAND_MODIFIER:
                    new_ranges_list.append(rng)
                    continue

                range_key = (rng.operand_index, rng.start, rng.length)
                group = list(operand_modifier_values.get(range_key, []) or [])
                if not group or rng.length <= 1:
                    new_ranges_list.append(rng)
                    if group:
                        new_operand_mods[range_key] = group
                    continue

                try:
                    base_val = get_bit_range_fn(ranges.inst, rng.start, rng.start + rng.length)
                except Exception:
                    base_val = 0

                full_name_map = {}
                for value, name in group:
                    try:
                        full_name_map[int(value)] = _clean_name(name)
                    except Exception:
                        continue
                if base_val not in full_name_map:
                    full_name_map[base_val] = ""

                try:
                    factor_base_val = min(
                        full_name_map.keys(),
                        key=lambda value: (
                            len(_name_tokens(full_name_map.get(int(value), ""))),
                            int(value),
                        ),
                    )
                except Exception:
                    factor_base_val = base_val

                split_flags = _maybe_split_into_operand_flags(
                    rng, factor_base_val, full_name_map
                )
                if split_flags is not None:
                    new_ranges_list.extend(split_flags)
                    changed = True
                    continue

                observed_values = sorted(int(value) for value in full_name_map.keys())
                split_groups = None
                split_point = None
                for split in range(1, int(rng.length)):
                    left_len = split
                    right_len = int(rng.length) - split
                    left_mask = (1 << left_len) - 1
                    left_base = int(factor_base_val) & left_mask
                    right_base = int(factor_base_val) >> split
                    left_values = sorted({int(value) & left_mask for value in observed_values})
                    right_values = sorted(
                        {int(value) >> split for value in observed_values}
                    )
                    if (left_base not in left_values) or (right_base not in right_values):
                        continue
                    if len(left_values) < 2 or len(right_values) < 2:
                        continue

                    base_tokens = _name_tokens(
                        full_name_map.get(int(factor_base_val), "")
                    )
                    base_signed = _signed_name_map(
                        full_name_map.get(int(factor_base_val), "")
                    )
                    left_rows = []
                    right_rows = []
                    left_delta = {}
                    right_delta = {}
                    ok = True

                    for left_value in left_values:
                        full_value = int(left_value) | (int(right_base) << split)
                        if full_value not in full_name_map:
                            ok = False
                            break
                        full_name = full_name_map[full_value]
                        left_rows.append(
                            (
                                left_value,
                                find_modifier_difference_fn(
                                    base_tokens, _name_tokens(full_name)
                                ),
                            )
                        )
                        left_delta[left_value] = _signed_sub(
                            _signed_name_map(full_name), base_signed
                        )
                    if not ok:
                        continue

                    for right_value in right_values:
                        full_value = int(left_base) | (int(right_value) << split)
                        if full_value not in full_name_map:
                            ok = False
                            break
                        full_name = full_name_map[full_value]
                        right_rows.append(
                            (
                                right_value,
                                find_modifier_difference_fn(
                                    base_tokens, _name_tokens(full_name)
                                ),
                            )
                        )
                        right_delta[right_value] = _signed_sub(
                            _signed_name_map(full_name), base_signed
                        )
                    if not ok:
                        continue

                    for left_value in left_values:
                        for right_value in right_values:
                            full_value = int(left_value) | (int(right_value) << split)
                            full_name = full_name_map.get(full_value)
                            if full_name is None:
                                ok = False
                                break
                            expected = _signed_add(
                                base_signed,
                                left_delta.get(int(left_value), {}),
                                right_delta.get(int(right_value), {}),
                            )
                            if expected != _signed_name_map(full_name):
                                ok = False
                                break
                        if not ok:
                            break
                    if not ok:
                        continue

                    left_rows, right_rows = _sanitize_split_group_tokens(
                        left_rows, right_rows, left_base, right_base
                    )
                    if len({name for _, name in left_rows}) < 2 or len(
                        {name for _, name in right_rows}
                    ) < 2:
                        continue
                    split_groups = (left_rows, right_rows)
                    split_point = split
                    break

                if split_groups is None or split_point is None:
                    new_ranges_list.append(rng)
                    if group:
                        new_operand_mods[range_key] = group
                    continue

                left_rows, right_rows = split_groups
                left_rng = encoding_range_cls(
                    encoding_range_type.OPERAND_MODIFIER,
                    rng.start,
                    split_point,
                    operand_index=rng.operand_index,
                    name=rng.name,
                )
                right_rng = encoding_range_cls(
                    encoding_range_type.OPERAND_MODIFIER,
                    rng.start + split_point,
                    int(rng.length) - split_point,
                    operand_index=rng.operand_index,
                    name=rng.name,
                )
                new_ranges_list.append(left_rng)
                new_ranges_list.append(right_rng)
                new_operand_mods[
                    (left_rng.operand_index, left_rng.start, left_rng.length)
                ] = left_rows
                new_operand_mods[
                    (right_rng.operand_index, right_rng.start, right_rng.length)
                ] = right_rows
                changed = True

            if not changed:
                break

            changed_any = True
            try:
                new_ranges_list.sort(key=lambda rng: rng.start)
            except Exception:
                pass
            ranges.ranges = new_ranges_list
            operand_modifier_values = new_operand_mods

        if not changed_any:
            return operand_modifier_values, ranges

        promoted_ranges = []
        promoted_operand_mods = {}
        for rng in ranges.ranges:
            if rng.type != encoding_range_type.OPERAND_MODIFIER or rng.length != 1:
                promoted_ranges.append(rng)
                continue

            range_key = (rng.operand_index, rng.start, rng.length)
            rows = list(operand_modifier_values.get(range_key, []) or [])
            try:
                base_val = get_bit_range_fn(ranges.inst, rng.start, rng.start + rng.length)
            except Exception:
                base_val = 0
            row_map = {int(value): _clean_name(name) for value, name in rows}
            base_name = row_map.get(int(base_val), "")
            alt_name = row_map.get(int(1 - int(base_val)), "")
            chosen_flag = None
            if not base_name and alt_name:
                alt_tokens = _name_tokens(alt_name)
                if len(alt_tokens) == 1:
                    chosen_flag = alt_tokens[0]
            elif base_name and not alt_name:
                base_tokens = _name_tokens(base_name)
                if len(base_tokens) == 1:
                    chosen_flag = base_tokens[0]

            if chosen_flag is not None:
                rng.type = encoding_range_type.OPERAND_FLAG
                rng.name = chosen_flag
                promoted_ranges.append(rng)
                continue

            promoted_ranges.append(rng)
            if rows:
                promoted_operand_mods[range_key] = rows

        try:
            promoted_ranges.sort(key=lambda rng: rng.start)
        except Exception:
            pass
        ranges.ranges = promoted_ranges
        return promoted_operand_mods, ranges
    except Exception:
        return operand_modifier_values, ranges


def normalize_modifier_rows(rows, *, sanitize_modifier_display_name_fn):
    normalized = []
    try:
        for value, name in rows or []:
            if not isinstance(name, str):
                continue
            display = sanitize_modifier_display_name_fn(name)
            if display is None:
                continue
            normalized.append((value, display))
    except Exception:
        return []
    return normalized


def concrete_modifier_names(rows, *, sanitize_modifier_display_name_fn):
    names = set()
    try:
        for _value, name in rows or []:
            display = sanitize_modifier_display_name_fn(name)
            if display and display != "":
                names.add(display.rstrip("."))
    except Exception:
        return set()
    return names


def backfill_modifier_tables_from_ranges(
    spec,
    disassembler,
    *,
    encoding_range_type,
    unify_spec_modifiers_fn,
    normalize_modifier_rows_fn,
    concrete_modifier_names_fn,
    filter_non_placeholder_modifiers_fn,
):
    changed = False

    try:
        mod_ranges = spec.ranges._find(encoding_range_type.MODIFIER)
    except Exception:
        mod_ranges = []
    if mod_ranges:
        try:
            re_enum_mods = spec.ranges.enumerate_modifiers(disassembler)
        except Exception:
            re_enum_mods = []
        if re_enum_mods:
            while len(spec.modifiers) < len(re_enum_mods):
                spec.modifiers.append([])
            for idx, rows in enumerate(re_enum_mods):
                normalized = normalize_modifier_rows_fn(rows)
                if not normalized:
                    continue
                current_names = concrete_modifier_names_fn(
                    spec.modifiers[idx] if idx < len(spec.modifiers) else []
                )
                new_names = concrete_modifier_names_fn(normalized)
                if len(new_names) > len(current_names):
                    spec.modifiers[idx] = normalized
                    changed = True

    try:
        re_enum_opmods = spec.ranges.enumerate_operand_modifiers(disassembler)
    except Exception:
        re_enum_opmods = {}
    if re_enum_opmods:
        if not isinstance(getattr(spec, "operand_modifiers", None), dict):
            spec.operand_modifiers = {}
        for range_key, rows in re_enum_opmods.items():
            normalized = normalize_modifier_rows_fn(rows)
            if not normalized:
                continue
            current_names = concrete_modifier_names_fn(
                spec.operand_modifiers.get(range_key, [])
            )
            new_names = concrete_modifier_names_fn(normalized)
            if len(new_names) > len(current_names):
                spec.operand_modifiers[range_key] = normalized
                changed = True

    if not changed:
        return False

    try:
        unify_spec_modifiers_fn(spec)
    except Exception:
        pass
    try:
        spec.opcode_modis = spec._get_opcode_modis()
    except Exception:
        pass
    try:
        parsed_mods = getattr(spec.parsed, "modifiers", []) or []
        clean_mods = filter_non_placeholder_modifiers_fn(parsed_mods)
        if parsed_mods and len(clean_mods) == len(parsed_mods):
            spec.canonical_name = ".".join([spec.parsed.base_name] + parsed_mods)
        else:
            spec.canonical_name = ".".join([spec.parsed.base_name] + spec.opcode_modis)
    except Exception:
        pass
    return True


def try_split_modifier_groups(
    disassembler,
    ranges,
    modifier_values,
    *,
    encoding_range_type,
    encoding_range_cls,
    get_bit_range_fn,
    instruction_parser,
    filter_non_placeholder_modifiers_fn,
    is_placeholder_modifier_fn,
    find_modifier_difference_fn,
):
    try:
        modifier_ranges = ranges._find(encoding_range_type.MODIFIER)
        base_vals = [
            get_bit_range_fn(ranges.inst, rng.start, rng.start + rng.length)
            for rng in modifier_ranges
        ]
        operand_values = [0] * ranges.operand_count()
        new_modifier_values = []
        new_ranges_list = []
        mod_idx = 0
        for rng in ranges.ranges:
            if rng.type != encoding_range_type.MODIFIER:
                new_ranges_list.append(rng)
                continue

            cur_vals = []
            if mod_idx < len(modifier_values):
                cur_vals = modifier_values[mod_idx]

            split_groups = None
            if rng.length > 1 and cur_vals:
                compound_names = [
                    name.rstrip(".")
                    for value, name in cur_vals
                    if name and isinstance(name, str)
                ]
                has_f16_rn_rz = (
                    len(compound_names) >= 2
                    and all("." in name for name in compound_names if name)
                    and any("F16" in name for name in compound_names)
                    and any(rounding in " ".join(compound_names) for rounding in ("RN", "RZ"))
                )
                has_e4m3_e2m3_e5m2 = (
                    len(compound_names) >= 2
                    and any("x4" in name for name in compound_names)
                    and any(token in " ".join(compound_names) for token in ("E4M3", "E2M3", "E5M2"))
                )
                if has_f16_rn_rz or has_e4m3_e2m3_e5m2:
                    new_ranges_list.append(rng)
                    new_modifier_values.append(cur_vals)
                    mod_idx += 1
                    continue

                candidate_tokens = set()
                for _value, name in cur_vals:
                    try:
                        if not name:
                            continue
                        parts = [part for part in name.split(".") if part]
                        for part in parts:
                            if not is_placeholder_modifier_fn(part):
                                candidate_tokens.add(part)
                    except Exception:
                        continue

                if len(candidate_tokens) >= 2:
                    try:
                        base_asm = disassembler.disassemble(ranges.inst)
                        base_lines = [line for line in base_asm.splitlines() if line.strip()]
                        base_line = base_lines[-1] if base_lines else base_asm
                        base_parsed = instruction_parser.parseInstruction(base_line)
                        base_mods = set(
                            filter_non_placeholder_modifiers_fn(
                                getattr(base_parsed, "modifiers", [])
                            )
                        )
                    except Exception:
                        base_parsed = None
                        base_mods = set()

                    token_bits = {token: set() for token in candidate_tokens}
                    baseline = list(base_vals)
                    for bit_off in range(rng.length):
                        probe_vals = list(baseline)
                        probe_vals[mod_idx] = baseline[mod_idx] ^ (1 << bit_off)
                        try:
                            inst_bytes = ranges.encode(operand_values, probe_vals)
                            asm = disassembler.disassemble(inst_bytes)
                            lines = [line for line in asm.splitlines() if line.strip()]
                            if not lines:
                                continue
                            parsed = instruction_parser.parseInstruction(lines[-1])
                            mods = set(
                                filter_non_placeholder_modifiers_fn(
                                    getattr(parsed, "modifiers", [])
                                )
                            )
                        except Exception:
                            continue

                        added = mods - base_mods
                        removed = base_mods - mods
                        for token in candidate_tokens:
                            if token in added:
                                token_bits[token].add(bit_off)
                            if token in removed:
                                token_bits[token].add(bit_off)

                    uniq = True
                    used_bits = set()
                    for token, bits in token_bits.items():
                        if len(bits) != 1:
                            uniq = False
                            break
                        bit = next(iter(bits))
                        if bit in used_bits:
                            uniq = False
                            break
                        used_bits.add(bit)

                    def _norm_counter(modifiers):
                        out = Counter()
                        try:
                            for modifier in filter_non_placeholder_modifiers_fn(modifiers):
                                out[modifier.rstrip(".")] += 1
                        except Exception:
                            return Counter()
                        return out

                    def _validate_bit_token_additivity(bit_to_token):
                        if not bit_to_token:
                            return False
                        try:
                            total_values = 1 << int(rng.length)
                        except Exception:
                            return False
                        if total_values <= 0 or total_values > 64:
                            return False

                        base_counter = _norm_counter(getattr(base_parsed, "modifiers", []) or [])
                        try:
                            base_val = int(baseline[mod_idx])
                        except Exception:
                            base_val = 0

                        for val in range(total_values):
                            probe_vals = list(baseline)
                            probe_vals[mod_idx] = val
                            try:
                                inst_bytes = ranges.encode(operand_values, probe_vals)
                                asm = disassembler.disassemble(inst_bytes)
                                lines = [line for line in asm.splitlines() if line.strip()]
                                if not lines:
                                    return False
                                parsed_v = instruction_parser.parseInstruction(lines[-1])
                            except Exception:
                                return False
                            try:
                                if base_parsed is not None and parsed_v.get_key() != base_parsed.get_key():
                                    return False
                            except Exception:
                                return False

                            mods_counter = _norm_counter(getattr(parsed_v, "modifiers", []) or [])
                            for bit_off, token in bit_to_token.items():
                                base_bit = (base_val >> bit_off) & 1
                                cur_bit = (int(val) >> bit_off) & 1
                                expected = (base_counter[token] > 0) ^ (cur_bit != base_bit)
                                actual = mods_counter[token] > 0
                                if expected != actual:
                                    return False
                        return True

                    def _validate_additive_single_bit_split():
                        try:
                            total_values = 1 << int(rng.length)
                        except Exception:
                            return False
                        if total_values <= 0 or total_values > 64:
                            return False

                        bit_to_token = {}
                        for token, bits in token_bits.items():
                            if len(bits) != 1:
                                continue
                            bit = next(iter(bits))
                            if bit in bit_to_token:
                                return False
                            bit_to_token[bit] = token
                        if not bit_to_token:
                            return False
                        return _validate_bit_token_additivity(bit_to_token)

                    def _name_counter(name):
                        out = Counter()
                        try:
                            if not name or not isinstance(name, str):
                                return out
                            clean = name.rstrip(".").strip()
                            if not clean or clean == "-" or is_placeholder_modifier_fn(clean):
                                return out
                            for part in clean.split("."):
                                token = part.strip()
                                if not token or is_placeholder_modifier_fn(token):
                                    continue
                                out[token] += 1
                        except Exception:
                            return Counter()
                        return out

                    def _name_tokens(name):
                        tokens = []
                        try:
                            if not name or not isinstance(name, str):
                                return tokens
                            clean = name.rstrip(".").strip()
                            if not clean or clean == "-":
                                return tokens
                            for part in clean.split("."):
                                token = part.strip()
                                if not token or is_placeholder_modifier_fn(token):
                                    continue
                                tokens.append(token)
                        except Exception:
                            return []
                        return tokens

                    def _signed_name_map(name):
                        out = {}
                        for token in _name_tokens(name):
                            out[token] = out.get(token, 0) + 1
                        return out

                    def _signed_sub(lhs, rhs):
                        out = {}
                        for token in set(lhs) | set(rhs):
                            delta = int(lhs.get(token, 0)) - int(rhs.get(token, 0))
                            if delta:
                                out[token] = delta
                        return out

                    def _signed_add(*maps):
                        out = {}
                        for mapping in maps:
                            for token, count in (mapping or {}).items():
                                out[token] = out.get(token, 0) + int(count)
                                if out[token] == 0:
                                    out.pop(token, None)
                        return out

                    def _strip_name_tokens(name, banned_tokens):
                        try:
                            if not banned_tokens or not isinstance(name, str):
                                return name
                            parts = []
                            for token in _name_tokens(name):
                                if token in banned_tokens:
                                    continue
                                parts.append(token)
                            return ".".join(parts) + ("." if parts else "")
                        except Exception:
                            return name

                    if uniq and len(used_bits) >= 1 and _validate_additive_single_bit_split():
                        split_groups = []
                        for bit_off in range(rng.length):
                            start = rng.start + bit_off
                            new_rng = encoding_range_cls(
                                encoding_range_type.MODIFIER,
                                start,
                                1,
                                group_id=None,
                            )
                            new_ranges_list.append(new_rng)
                            assigned_tok = None
                            for token, bits in token_bits.items():
                                if bit_off in bits:
                                    assigned_tok = token
                                    break
                            group = [(0, "")]
                            if assigned_tok:
                                group.append((1, assigned_tok + "."))
                            else:
                                group.append((1, ""))
                            split_groups.append(group)
                        for group in split_groups:
                            new_modifier_values.append(group)
                        mod_idx += 1
                        continue

                    bits_with_tokens = set()
                    for bits in token_bits.values():
                        bits_with_tokens.update(bits)
                    has_u32_rz = candidate_tokens >= {"U32", "RZ"} or candidate_tokens >= {"F32", "RZ"}
                    if len(bits_with_tokens) >= 2 or (has_u32_rz and rng.length >= 4 and len(bits_with_tokens) >= 1):
                        has_gather = "GATHER4" in candidate_tokens
                        split_candidates = []
                        for _token, bits in token_bits.items():
                            if len(bits) > 1:
                                low = min(bits)
                                if 0 < low < rng.length:
                                    split_candidates.append((0, low))
                        bits_sorted = sorted(bits_with_tokens)
                        best_gap = 0
                        gap_split = None
                        for idx in range(1, len(bits_sorted)):
                            gap = bits_sorted[idx] - bits_sorted[idx - 1]
                            if gap > 1 and gap > best_gap:
                                best_gap = gap
                                gap_split = bits_sorted[idx - 1] + 1
                        if gap_split is not None:
                            split_candidates.append((1, gap_split))
                        if gap_split == 2 and has_gather and rng.length >= 6:
                            split_candidates.append((1, 3))
                        if rng.length >= 4 and (
                            candidate_tokens >= {"U32", "RZ"} or candidate_tokens >= {"F32", "RZ"}
                        ):
                            split_candidates.append((0, 4))
                        try:
                            for split in range(1, int(rng.length)):
                                low_tokens = set()
                                high_tokens = set()
                                for token, bits in token_bits.items():
                                    if not bits:
                                        continue
                                    if all(bit < split for bit in bits):
                                        low_tokens.add(token)
                                    elif all(bit >= split for bit in bits):
                                        high_tokens.add(token)
                                if not low_tokens or not high_tokens:
                                    continue
                                bit_to_token_candidate = {}
                                ambiguous = False
                                for token in low_tokens:
                                    bits = {bit for bit in token_bits.get(token, set()) if bit < split}
                                    if len(bits) != 1:
                                        continue
                                    bit = next(iter(bits))
                                    if bit in bit_to_token_candidate:
                                        ambiguous = True
                                        break
                                    bit_to_token_candidate[bit] = token
                                if ambiguous or not bit_to_token_candidate:
                                    continue
                                if _validate_bit_token_additivity(bit_to_token_candidate):
                                    split_candidates.append((-2, split))
                                elif low_tokens and high_tokens:
                                    split_candidates.append((2, split))
                        except Exception:
                            pass

                        single_bit_token_by_bit = {}
                        ambiguous_bits = set()
                        for token, bits in token_bits.items():
                            if len(bits) != 1:
                                continue
                            bit = next(iter(bits))
                            if bit in single_bit_token_by_bit:
                                ambiguous_bits.add(bit)
                                continue
                            single_bit_token_by_bit[bit] = token
                        for bit in ambiguous_bits:
                            single_bit_token_by_bit.pop(bit, None)
                        edge_split_candidates = []
                        if 0 in single_bit_token_by_bit and _validate_bit_token_additivity({0: single_bit_token_by_bit[0]}):
                            edge_split_candidates.append(1)
                        hi_bit = rng.length - 1
                        if (
                            hi_bit in single_bit_token_by_bit
                            and hi_bit > 0
                            and _validate_bit_token_additivity({hi_bit: single_bit_token_by_bit[hi_bit]})
                        ):
                            edge_split_candidates.append(hi_bit)
                        for split_point in edge_split_candidates:
                            if 0 < split_point < rng.length:
                                split_candidates.append((-1, split_point))
                        split_candidates.sort(key=lambda item: (item[0], item[1]))
                        ordered = list(dict.fromkeys(split for _, split in split_candidates if 0 < split < rng.length))
                        for split in range(1, int(rng.length)):
                            if split not in ordered:
                                ordered.append(split)
                        try:
                            base_key = base_parsed.get_key()
                        except Exception:
                            base_key = None

                        split_done = False
                        for best_split in ordered:
                            left_len = best_split
                            right_len = rng.length - best_split
                            left_mask = (1 << left_len) - 1
                            right_mask = (1 << right_len) - 1
                            base_val = baseline[mod_idx]
                            left_base = base_val & left_mask
                            right_base = (base_val >> best_split) & right_mask

                            def _name_for_val(left_v, right_v):
                                value = left_v | (right_v << best_split)
                                probe_vals = list(baseline)
                                probe_vals[mod_idx] = value
                                try:
                                    inst_bytes = ranges.encode(operand_values, probe_vals)
                                    asm = disassembler.disassemble(inst_bytes)
                                    lines = [line for line in asm.splitlines() if line.strip()]
                                    if not lines:
                                        return None
                                    parsed = instruction_parser.parseInstruction(lines[-1])
                                    if base_key is not None and parsed.get_key() != base_key:
                                        return None
                                    base_mods = getattr(base_parsed, "modifiers", []) or []
                                    diff = find_modifier_difference_fn(base_mods, parsed.modifiers)
                                    return diff if diff else ""
                                except Exception:
                                    return None

                            def _validate_split_groups(left_rows, right_rows):
                                try:
                                    left_map = {int(value): (name or "") for value, name in left_rows}
                                    right_map = {int(value): (name or "") for value, name in right_rows}
                                except Exception:
                                    return False
                                if not left_map or not right_map:
                                    return False
                                for full_v, full_name in cur_vals:
                                    try:
                                        full_v = int(full_v)
                                    except Exception:
                                        return False
                                    left_v = full_v & left_mask
                                    right_v = (full_v >> best_split) & right_mask
                                    if left_v not in left_map or right_v not in right_map:
                                        return False
                                    combined = Counter()
                                    combined.update(_name_counter(left_map[left_v]))
                                    combined.update(_name_counter(right_map[right_v]))
                                    if combined != _name_counter(full_name):
                                        return False
                                return True

                            def _derive_split_groups_from_rows():
                                try:
                                    full_name_map = {int(value): (name or "") for value, name in cur_vals}
                                except Exception:
                                    return None
                                if base_val not in full_name_map:
                                    return None

                                base_name = full_name_map.get(base_val, "")
                                base_tokens = _name_tokens(base_name)
                                base_signed = _signed_name_map(base_name)
                                left_rows = []
                                right_rows = []
                                left_delta = {}
                                right_delta = {}

                                for left_v in range(1 << left_len):
                                    full_v = left_v | (right_base << best_split)
                                    full_name = full_name_map.get(full_v)
                                    if full_name is None:
                                        return None
                                    left_rows.append(
                                        (
                                            left_v,
                                            find_modifier_difference_fn(
                                                base_tokens,
                                                _name_tokens(full_name),
                                            ),
                                        )
                                    )
                                    left_delta[left_v] = _signed_sub(
                                        _signed_name_map(full_name), base_signed
                                    )

                                for right_v in range(1 << right_len):
                                    full_v = left_base | (right_v << best_split)
                                    full_name = full_name_map.get(full_v)
                                    if full_name is None:
                                        return None
                                    right_rows.append(
                                        (
                                            right_v,
                                            find_modifier_difference_fn(
                                                base_tokens,
                                                _name_tokens(full_name),
                                            ),
                                        )
                                    )
                                    right_delta[right_v] = _signed_sub(
                                        _signed_name_map(full_name), base_signed
                                    )

                                for full_v, full_name in full_name_map.items():
                                    left_v = full_v & left_mask
                                    right_v = (full_v >> best_split) & right_mask
                                    expected = _signed_add(
                                        base_signed,
                                        left_delta.get(left_v, {}),
                                        right_delta.get(right_v, {}),
                                    )
                                    if expected != _signed_name_map(full_name):
                                        return None
                                return left_rows, right_rows

                            def _sanitize_split_group_tokens(left_rows, right_rows):
                                try:
                                    left_controlled = set()
                                    right_controlled = set()
                                    for value, name in left_rows:
                                        if int(value) == left_base:
                                            continue
                                        left_controlled.update(_name_tokens(name))
                                    for value, name in right_rows:
                                        if int(value) == right_base:
                                            continue
                                        right_controlled.update(_name_tokens(name))
                                    new_left = [
                                        (value, _strip_name_tokens(name, right_controlled))
                                        for value, name in left_rows
                                    ]
                                    new_right = [
                                        (value, _strip_name_tokens(name, left_controlled))
                                        for value, name in right_rows
                                    ]
                                except Exception:
                                    return left_rows, right_rows
                                return new_left, new_right

                            split_groups = _derive_split_groups_from_rows()
                            if split_groups is None:
                                left_group = []
                                for left_v in range(1 << left_len):
                                    name = _name_for_val(left_v, right_base)
                                    if name is not None:
                                        left_group.append((left_v, name))
                                right_group = []
                                base_right_name = _name_for_val(left_base, right_base)
                                for right_v in range(1 << right_len):
                                    name = _name_for_val(left_base, right_v)
                                    if name is not None:
                                        if name == base_right_name:
                                            continue
                                        if base_right_name and name:
                                            base_stem = base_right_name.rstrip(".")
                                            if base_stem and name.startswith(base_stem + "."):
                                                name = name[len(base_stem) + 1:]
                                        right_group.append((right_v, name))
                                base_name = base_right_name if base_right_name else "-"
                                if right_group and (right_base, base_name) not in [
                                    (value, name) for value, name in right_group
                                ]:
                                    right_group.insert(0, (right_base, base_name))
                                if len(left_group) >= 1 and len(right_group) >= 1:
                                    if _validate_split_groups(left_group, right_group):
                                        split_groups = (left_group, right_group)
                            if split_groups is not None:
                                left_group, right_group = split_groups
                                left_group, right_group = _sanitize_split_group_tokens(
                                    left_group,
                                    right_group,
                                )
                                left_rng = encoding_range_cls(
                                    encoding_range_type.MODIFIER,
                                    rng.start,
                                    left_len,
                                    group_id=None,
                                )
                                right_rng = encoding_range_cls(
                                    encoding_range_type.MODIFIER,
                                    rng.start + best_split,
                                    right_len,
                                    group_id=None,
                                )
                                new_ranges_list.append(left_rng)
                                new_ranges_list.append(right_rng)
                                new_modifier_values.append(left_group)
                                new_modifier_values.append(right_group)
                                mod_idx += 1
                                split_done = True
                                break
                        if split_done:
                            continue

            new_ranges_list.append(rng)
            if cur_vals is not None:
                new_modifier_values.append(cur_vals)
            mod_idx += 1

        ranges.ranges = new_ranges_list
        return new_modifier_values, ranges
    except Exception:
        return modifier_values, ranges


def attach_half_pair_overlay_operand_modifiers(
    spec,
    disassembler,
    *,
    encoding_range_type,
    set_bit_range_fn,
    parse_instruction_fn,
    split_token_parts_fn=split_token_parts,
    clean_modifier_row_name_fn=clean_modifier_row_name,
    get_operand_modifier_rows_fn=get_operand_modifier_rows,
    is_placeholder_modifier_fn=is_placeholder_modifier,
):
    def _extract_operand_modifier_tokens_all(inst_bytes, op_idx):
        asm = disassembler.disassemble(inst_bytes)
        if not asm:
            return None, None
        try:
            parsed = parse_instruction_fn(asm)
        except Exception:
            return asm, None
        if parsed.get_key() != spec.parsed.get_key():
            return asm, None
        try:
            ops = parsed.get_flat_operands()
        except Exception:
            return asm, None
        if op_idx < 0 or op_idx >= len(ops):
            return asm, None
        tokens = set()
        try:
            for raw in getattr(ops[op_idx], "modifiers", []) or []:
                for tok in split_token_parts_fn(raw):
                    if tok and not is_placeholder_modifier_fn(tok):
                        tokens.add(tok)
        except Exception:
            return asm, None
        return asm, tokens

    try:
        opmod_ranges = [
            rng
            for rng in spec.ranges._find(encoding_range_type.OPERAND_MODIFIER)
            if int(getattr(rng, "length", 0) or 0) == 2
        ]
        flag_ranges = [
            rng
            for rng in spec.ranges._find(encoding_range_type.OPERAND_FLAG)
            if int(getattr(rng, "length", 0) or 0) == 1
        ]
        opmod_1bit = [
            rng
            for rng in spec.ranges._find(encoding_range_type.OPERAND_MODIFIER)
            if int(getattr(rng, "length", 0) or 0) == 1
        ]
        for rng in opmod_1bit:
            if getattr(rng, "operand_index", None) is not None:
                flag_ranges.append(rng)
    except Exception:
        return
    if not opmod_ranges or not flag_ranges:
        return

    try:
        next_group_id = (
            max(
                [
                    int(getattr(rng, "group_id", 0) or 0)
                    for rng in (getattr(spec.ranges, "ranges", []) or [])
                    if getattr(rng, "group_id", None) is not None
                ]
                + [0]
            )
            + 1
        )
    except Exception:
        next_group_id = 1

    try:
        inst_base = bytearray(spec.ranges.inst)
    except Exception:
        return

    for main_rng in opmod_ranges:
        op_idx = getattr(main_rng, "operand_index", None)
        if op_idx is None:
            continue
        main_start = main_rng.start
        main_end = main_rng.start + main_rng.length
        base_rows = get_operand_modifier_rows_fn(spec.operand_modifiers, op_idx, main_rng)
        row_map = {int(v): clean_modifier_row_name_fn(n) for v, n in base_rows}

        for flag_rng in flag_ranges:
            if getattr(flag_rng, "operand_index", None) != op_idx:
                continue
            if main_start <= flag_rng.start < main_end:
                continue
            flag_start = flag_rng.start

            combo_tokens = {}
            t00 = t01 = t11 = t21 = t31 = None
            for main_val in range(4):
                for overlay in (0, 1):
                    inst_b = bytearray(inst_base)
                    set_bit_range_fn(inst_b, main_start, main_end, main_val)
                    set_bit_range_fn(inst_b, flag_start, flag_start + 1, overlay)
                    asm, tokens = _extract_operand_modifier_tokens_all(bytes(inst_b), op_idx)
                    if asm and "INVALID" in asm:
                        tokens = set()
                    if tokens is None:
                        tokens = set()
                    combo_tokens[(main_val, overlay)] = set(tokens)
                    if main_val == 0 and overlay == 0:
                        t00 = tokens
                    elif main_val == 0 and overlay == 1:
                        t01 = tokens
                    elif main_val == 1 and overlay == 1:
                        t11 = tokens
                    elif main_val == 2 and overlay == 1:
                        t21 = tokens
                    elif main_val == 3 and overlay == 1:
                        t31 = tokens

            if t01 is None:
                t01 = set()
            if t00 is None:
                t00 = set()
            overlay_token = None
            for token in t01:
                if token in t00:
                    continue
                if token in (t11 or set()):
                    continue
                if token in (t21 or set()):
                    continue
                if token in (t31 or set()):
                    continue
                overlay_token = token
                break
            if overlay_token is None:
                continue

            group_rows = []
            for value in range(4):
                if value == 0:
                    group_rows.append((0, overlay_token + "."))
                else:
                    clean = row_map.get(value, "")
                    if clean:
                        group_rows.append((value, clean + "."))
                    else:
                        group_rows.append((value, ""))

            group_id = next_group_id
            next_group_id += 1
            group_key = ("group", op_idx, group_id)

            main_rng.group_id = group_id
            flag_rng.group_id = group_id
            main_rng.name = None
            flag_rng.type = encoding_range_type.OPERAND_MODIFIER
            flag_rng.name = "__OVL__"
            spec.operand_modifiers[group_key] = group_rows
            try:
                composite_rows = []
                for main_val in range(4):
                    for overlay in (0, 1):
                        tokens = combo_tokens.get((main_val, overlay), set())
                        token_list = sorted(
                            tok
                            for tok in tokens
                            if tok and not is_placeholder_modifier_fn(tok)
                        )
                        if not token_list:
                            fallback = row_map.get(main_val, "") if overlay == 0 else ""
                            if fallback:
                                token_list = [fallback]
                        if not token_list:
                            continue
                        composite_rows.append(
                            {
                                "main_value": main_val,
                                "overlay_value": overlay,
                                "tokens": token_list,
                            }
                        )
                if composite_rows:
                    existing = list(getattr(spec, "operand_modifier_composites", []) or [])
                    existing.append(
                        {
                            "operand_index": op_idx,
                            "group_id": group_id,
                            "main_width": int(getattr(main_rng, "length", 0) or 0),
                            "overlay_width": 1,
                            "rows": composite_rows,
                        }
                    )
                    spec.operand_modifier_composites = existing
            except Exception:
                pass
            return


def emit_modifier_constant_segments(
    ranges,
    rng,
    group,
    meaningful_vals,
    bit_kinds,
    new_ranges_list,
    new_modifier_values,
    *,
    encoding_range_type,
    encoding_range_cls,
    get_bit_range_fn,
    is_placeholder_modifier_fn,
):
    del meaningful_vals
    length = len(bit_kinds)
    var_positions = [idx for idx, (kind, _value) in enumerate(bit_kinds) if kind == "var"]
    if not var_positions:
        new_ranges_list.append(rng)
        new_modifier_values.append(group)
        return

    runs = []
    for position in var_positions:
        if not runs or position != runs[-1][-1] + 1:
            runs.append([position])
        else:
            runs[-1].append(position)

    base = rng.start
    for run_idx, run in enumerate(runs):
        run_start = run[0]
        run_len = len(run)
        mod_start = base + run_start
        new_ranges_list.append(
            encoding_range_cls(
                encoding_range_type.MODIFIER,
                mod_start,
                run_len,
                operand_index=rng.operand_index,
                name=rng.name,
                group_id=rng.group_id,
            )
        )

        def _project_to_run(value: int) -> int:
            out = 0
            for dst, src in enumerate(run):
                if (value >> src) & 1:
                    out |= 1 << dst
            return out

        proj_map = {}
        for value, name in group:
            try:
                projected_value = _project_to_run(int(value))
            except Exception:
                projected_value = 0
            existing = proj_map.get(projected_value)
            if existing is None:
                proj_map[projected_value] = name
            else:
                try:
                    old_ok = bool(
                        existing
                        and isinstance(existing, str)
                        and not is_placeholder_modifier_fn(existing)
                    )
                    new_ok = bool(
                        name
                        and isinstance(name, str)
                        and not is_placeholder_modifier_fn(name)
                    )
                except Exception:
                    old_ok = False
                    new_ok = False
                if (not old_ok) and new_ok:
                    proj_map[projected_value] = name

        try:
            projected = [(pv, proj_map[pv]) for pv in sorted(proj_map.keys())]
        except Exception:
            projected = list(proj_map.items())
        new_modifier_values.append(projected)

        if run_idx + 1 < len(runs):
            next_run = runs[run_idx + 1]
            gap_start = run[-1] + 1
            gap_end = next_run[0]
            gap_len = gap_end - gap_start
            c_start = base + gap_start
            try:
                c_val = get_bit_range_fn(ranges.inst, c_start, c_start + gap_len)
            except Exception:
                c_val = 0
            new_ranges_list.append(
                encoding_range_cls(
                    encoding_range_type.CONSTANT,
                    c_start,
                    gap_len,
                    constant=c_val,
                )
            )


def factorize_modifier_groups_from_rows(
    ranges,
    modifier_values,
    *,
    encoding_range_type,
    encoding_range_cls,
    get_bit_range_fn,
    is_placeholder_modifier_fn,
    find_modifier_difference_fn,
):
    try:
        def _clean_name(name):
            try:
                if not name or not isinstance(name, str):
                    return ""
                clean = name.rstrip(".").strip()
                if not clean or clean == "-":
                    return ""
                kept = [
                    part.strip()
                    for part in clean.split(".")
                    if part.strip() and not is_placeholder_modifier_fn(part.strip())
                ]
                if not kept:
                    return ""
                return ".".join(kept) + "."
            except Exception:
                return ""

        def _name_tokens(name):
            clean = _clean_name(name)
            if not clean:
                return []
            return [part for part in clean.rstrip(".").split(".") if part]

        def _signed_name_map(name):
            out = {}
            for token in _name_tokens(name):
                out[token] = out.get(token, 0) + 1
            return out

        def _signed_sub(lhs, rhs):
            out = {}
            for token in set(lhs) | set(rhs):
                delta = int(lhs.get(token, 0)) - int(rhs.get(token, 0))
                if delta:
                    out[token] = delta
            return out

        def _signed_add(*maps):
            out = {}
            for mapping in maps:
                for token, count in (mapping or {}).items():
                    out[token] = out.get(token, 0) + int(count)
                    if out[token] == 0:
                        out.pop(token, None)
            return out

        def _sanitize_split_group_tokens(left_rows, right_rows, left_base, right_base):
            try:
                left_controlled = set()
                right_controlled = set()
                for value, name in left_rows:
                    if int(value) == int(left_base):
                        continue
                    left_controlled.update(_name_tokens(name))
                for value, name in right_rows:
                    if int(value) == int(right_base):
                        continue
                    right_controlled.update(_name_tokens(name))

                def _strip(name, banned):
                    tokens = [token for token in _name_tokens(name) if token not in banned]
                    return ".".join(tokens) + ("." if tokens else "")

                new_left = [(value, _strip(name, right_controlled)) for value, name in left_rows]
                new_right = [(value, _strip(name, left_controlled)) for value, name in right_rows]
                return new_left, new_right
            except Exception:
                return left_rows, right_rows

        new_ranges_list = []
        new_modifier_values = []
        mod_idx = 0
        for rng in ranges.ranges:
            if rng.type != encoding_range_type.MODIFIER:
                new_ranges_list.append(rng)
                continue

            group = modifier_values[mod_idx] if mod_idx < len(modifier_values) else []
            mod_idx += 1
            if not group or rng.length <= 1:
                new_ranges_list.append(rng)
                new_modifier_values.append(group)
                continue

            try:
                base_val = get_bit_range_fn(ranges.inst, rng.start, rng.start + rng.length)
            except Exception:
                base_val = 0
            full_name_map = {}
            for value, name in group:
                try:
                    full_name_map[int(value)] = _clean_name(name)
                except Exception:
                    continue
            if base_val not in full_name_map:
                full_name_map[base_val] = ""

            observed_values = sorted(int(value) for value in full_name_map.keys())
            split_groups = None
            split_point = None
            for split in range(1, int(rng.length)):
                left_len = split
                right_len = int(rng.length) - split
                left_mask = (1 << left_len) - 1
                left_base = int(base_val) & left_mask
                right_base = int(base_val) >> split
                left_values = sorted({int(value) & left_mask for value in observed_values})
                right_values = sorted({int(value) >> split for value in observed_values})
                if (left_base not in left_values) or (right_base not in right_values):
                    continue
                if len(left_values) < 2 or len(right_values) < 2:
                    continue

                base_name = full_name_map.get(int(base_val), "")
                base_tokens = _name_tokens(base_name)
                base_signed = _signed_name_map(base_name)
                left_rows = []
                right_rows = []
                left_delta = {}
                right_delta = {}
                ok = True

                for left_v in left_values:
                    full_v = int(left_v) | (int(right_base) << split)
                    if full_v not in full_name_map:
                        ok = False
                        break
                    full_name = full_name_map[full_v]
                    left_rows.append(
                        (
                            left_v,
                            find_modifier_difference_fn(base_tokens, _name_tokens(full_name)),
                        )
                    )
                    left_delta[left_v] = _signed_sub(
                        _signed_name_map(full_name), base_signed
                    )
                if not ok:
                    continue

                for right_v in right_values:
                    full_v = int(left_base) | (int(right_v) << split)
                    if full_v not in full_name_map:
                        ok = False
                        break
                    full_name = full_name_map[full_v]
                    right_rows.append(
                        (
                            right_v,
                            find_modifier_difference_fn(base_tokens, _name_tokens(full_name)),
                        )
                    )
                    right_delta[right_v] = _signed_sub(
                        _signed_name_map(full_name), base_signed
                    )
                if not ok:
                    continue

                for left_v in left_values:
                    for right_v in right_values:
                        full_v = int(left_v) | (int(right_v) << split)
                        full_name = full_name_map.get(full_v)
                        if full_name is None:
                            ok = False
                            break
                        expected = _signed_add(
                            base_signed,
                            left_delta.get(int(left_v), {}),
                            right_delta.get(int(right_v), {}),
                        )
                        if expected != _signed_name_map(full_name):
                            ok = False
                            break
                    if not ok:
                        break
                if not ok:
                    continue

                left_rows, right_rows = _sanitize_split_group_tokens(
                    left_rows,
                    right_rows,
                    left_base,
                    right_base,
                )
                if len({name for _, name in left_rows}) < 2 or len({name for _, name in right_rows}) < 2:
                    continue
                split_groups = (left_rows, right_rows)
                split_point = split
                break

            if split_groups is None or split_point is None:
                new_ranges_list.append(rng)
                new_modifier_values.append(group)
                continue

            left_rows, right_rows = split_groups
            left_rng = encoding_range_cls(
                encoding_range_type.MODIFIER,
                rng.start,
                split_point,
                operand_index=rng.operand_index,
                name=rng.name,
                group_id=rng.group_id,
            )
            right_rng = encoding_range_cls(
                encoding_range_type.MODIFIER,
                rng.start + split_point,
                int(rng.length) - split_point,
                operand_index=rng.operand_index,
                name=rng.name,
                group_id=rng.group_id,
            )
            new_ranges_list.append(left_rng)
            new_ranges_list.append(right_rng)
            new_modifier_values.append(left_rows)
            new_modifier_values.append(right_rows)

        new_ranges_list.sort(key=lambda rng: rng.start)
        ranges.ranges = new_ranges_list
        return new_modifier_values, ranges
    except Exception:
        return modifier_values, ranges


def compress_modifier_constant_bits(
    ranges,
    modifier_values,
    *,
    encoding_range_type,
    encoding_range_cls,
    get_bit_range_fn,
    emit_modifier_constant_segments_fn,
    is_placeholder_modifier_fn,
):
    try:
        def _normalize_name(name):
            try:
                if not name or not isinstance(name, str):
                    return None
                clean = name.rstrip(".").strip()
                if (not clean) or clean == "-":
                    return None
                kept = [
                    part.strip()
                    for part in clean.split(".")
                    if part.strip() and not is_placeholder_modifier_fn(part.strip())
                ]
                if not kept:
                    return None
                return ".".join(kept)
            except Exception:
                return None

        def _project_bits(value: int, keep_start: int, keep_end: int) -> int:
            try:
                value_int = int(value)
            except Exception:
                value_int = 0
            new_value = 0
            dst = 0
            for src in range(keep_start, keep_end + 1):
                if ((value_int >> src) & 1) != 0:
                    new_value |= 1 << dst
                dst += 1
            return new_value

        def _find_alias_window(group, length: int):
            meaningful = []
            unnamed_values = []
            for value, name in group or []:
                try:
                    value_int = int(value)
                except Exception:
                    continue
                normalized_name = _normalize_name(name)
                if normalized_name is None:
                    unnamed_values.append(value_int)
                    continue
                meaningful.append((value_int, normalized_name))
            if len({name for _, name in meaningful}) < 2:
                return None

            for win_len in range(1, int(length)):
                for keep_start in range(0, int(length) - win_len + 1):
                    keep_end = keep_start + win_len - 1
                    code_to_name = {}
                    name_to_code = {}
                    ok = True
                    for value, name in meaningful:
                        projected_value = _project_bits(value, keep_start, keep_end)
                        prev_name = code_to_name.get(projected_value)
                        if prev_name is not None and prev_name != name:
                            ok = False
                            break
                        code_to_name[projected_value] = name
                        prev_code = name_to_code.get(name)
                        if prev_code is not None and prev_code != projected_value:
                            ok = False
                            break
                        name_to_code[name] = projected_value
                    if ok and unnamed_values:
                        used_codes = set(code_to_name.keys())
                        for value in unnamed_values:
                            if _project_bits(value, keep_start, keep_end) in used_codes:
                                ok = False
                                break
                    if ok:
                        return keep_start, keep_end
            return None

        if not modifier_values:
            return modifier_values, ranges

        new_ranges_list = []
        new_modifier_values = []
        mod_idx = 0
        for rng in ranges.ranges:
            if rng.type != encoding_range_type.MODIFIER:
                new_ranges_list.append(rng)
                continue

            group = modifier_values[mod_idx] if mod_idx < len(modifier_values) else []
            mod_idx += 1
            try:
                addrspace_like = False
                if rng.length is not None and rng.length >= 4 and group:
                    for _value, name in group:
                        if not name or not isinstance(name, str):
                            continue
                        normalized_name = name.rstrip(".").upper()
                        if any(token in normalized_name for token in ("CONSTANT", "MMIO", "GPU")):
                            addrspace_like = True
                            break
                if addrspace_like:
                    new_ranges_list.append(rng)
                    new_modifier_values.append(group)
                    continue
            except Exception:
                pass

            if not group or rng.length <= 1:
                new_ranges_list.append(rng)
                new_modifier_values.append(group)
                continue

            meaningful_vals = []
            meaningful_rows = []
            for value, name in group:
                try:
                    normalized_name = _normalize_name(name)
                    if normalized_name is not None:
                        value_int = int(value)
                        meaningful_vals.append(value_int)
                        meaningful_rows.append((value_int, normalized_name))
                except Exception:
                    continue

            if len(set(meaningful_vals)) < 2:
                new_ranges_list.append(rng)
                new_modifier_values.append(group)
                continue

            length = rng.length
            bit_kinds = []
            for bit_off in range(length):
                try:
                    bits = {(value >> bit_off) & 1 for value in meaningful_vals}
                except Exception:
                    bits = set()
                if len(bits) == 1:
                    bit_kinds.append(("const", next(iter(bits))))
                else:
                    bit_kinds.append(("var", None))

            var_positions = [idx for idx, (kind, _constant) in enumerate(bit_kinds) if kind == "var"]
            if not var_positions:
                new_ranges_list.append(rng)
                new_modifier_values.append(group)
                continue

            first_var = var_positions[0]
            last_var = var_positions[-1]
            keep_start = first_var
            keep_end = last_var
            alias_mode = False
            alias_window = _find_alias_window(group, length)
            if alias_window is not None:
                alias_start, alias_end = alias_window
                if (alias_end - alias_start) < (keep_end - keep_start):
                    keep_start = alias_start
                    keep_end = alias_end
                    alias_mode = True

            gaps = [
                (var_positions[idx] + 1, var_positions[idx + 1] - var_positions[idx] - 1)
                for idx in range(len(var_positions) - 1)
                if var_positions[idx + 1] - var_positions[idx] > 1
            ]
            if gaps:
                emit_modifier_constant_segments_fn(
                    ranges,
                    rng,
                    group,
                    meaningful_vals,
                    bit_kinds,
                    new_ranges_list,
                    new_modifier_values,
                )
                continue

            prefix_len = keep_start
            suffix_len = length - 1 - keep_end
            mid_len = length - prefix_len - suffix_len
            if prefix_len == 0 and suffix_len == 0 or mid_len <= 0:
                new_ranges_list.append(rng)
                new_modifier_values.append(group)
                continue

            try:
                unique_meaningful = sorted(set(meaningful_vals))
            except Exception:
                unique_meaningful = meaningful_vals

            try:
                if alias_mode:
                    meaningful_name_count = len({name for _, name in meaningful_rows})
                    over_capacity = meaningful_name_count > (1 << mid_len)
                else:
                    over_capacity = len(unique_meaningful) > (1 << mid_len)
                if mid_len < 0 or over_capacity:
                    new_ranges_list.append(rng)
                    new_modifier_values.append(group)
                    continue
            except Exception:
                new_ranges_list.append(rng)
                new_modifier_values.append(group)
                continue

            def _project_for_check(value: int) -> int:
                return _project_bits(value, keep_start, keep_end)

            if alias_mode:
                try:
                    code_to_name = {}
                    name_to_code = {}
                    for value, name in meaningful_rows:
                        projected_value = _project_for_check(value)
                        prev_name = code_to_name.get(projected_value)
                        if prev_name is not None and prev_name != name:
                            raise ValueError("alias collision across distinct names")
                        code_to_name[projected_value] = name
                        prev_code = name_to_code.get(name)
                        if prev_code is not None and prev_code != projected_value:
                            raise ValueError("same name still maps to multiple projected codes")
                        name_to_code[name] = projected_value
                except Exception:
                    new_ranges_list.append(rng)
                    new_modifier_values.append(group)
                    continue
            else:
                try:
                    projected_set = {_project_for_check(value) for value in unique_meaningful}
                    if len(projected_set) < len(unique_meaningful):
                        new_ranges_list.append(rng)
                        new_modifier_values.append(group)
                        continue
                except Exception:
                    new_ranges_list.append(rng)
                    new_modifier_values.append(group)
                    continue

            if prefix_len > 0:
                c_start = rng.start
                c_end = c_start + prefix_len
                try:
                    c_val = get_bit_range_fn(ranges.inst, c_start, c_end)
                except Exception:
                    c_val = 0
                new_ranges_list.append(
                    encoding_range_cls(
                        encoding_range_type.CONSTANT,
                        c_start,
                        prefix_len,
                        constant=c_val,
                    )
                )

            mid_start = rng.start + prefix_len
            new_ranges_list.append(
                encoding_range_cls(
                    encoding_range_type.MODIFIER,
                    mid_start,
                    mid_len,
                    operand_index=rng.operand_index,
                    name=rng.name,
                    group_id=rng.group_id,
                )
            )

            if suffix_len > 0:
                suffix_start = mid_start + mid_len
                suffix_end = suffix_start + suffix_len
                try:
                    suffix_val = get_bit_range_fn(ranges.inst, suffix_start, suffix_end)
                except Exception:
                    suffix_val = 0
                new_ranges_list.append(
                    encoding_range_cls(
                        encoding_range_type.CONSTANT,
                        suffix_start,
                        suffix_len,
                        constant=suffix_val,
                    )
                )

            def _project(value: int) -> int:
                return _project_bits(value, keep_start, keep_end)

            proj_map = {}
            for value, name in group:
                try:
                    projected_value = _project(value)
                except Exception:
                    projected_value = 0
                existing = proj_map.get(projected_value)
                if existing is None:
                    proj_map[projected_value] = name
                else:
                    try:
                        old_ok = bool(
                            existing
                            and isinstance(existing, str)
                            and not is_placeholder_modifier_fn(existing)
                        )
                        new_ok = bool(
                            name
                            and isinstance(name, str)
                            and not is_placeholder_modifier_fn(name)
                        )
                    except Exception:
                        old_ok = False
                        new_ok = False
                    if (not old_ok) and new_ok:
                        proj_map[projected_value] = name

            try:
                projected_group = [
                    (projected_value, proj_map[projected_value])
                    for projected_value in sorted(proj_map.keys())
                ]
            except Exception:
                projected_group = [(projected_value, name) for projected_value, name in proj_map.items()]

            new_modifier_values.append(projected_group)

        try:
            new_ranges_list.sort(key=lambda rng: rng.start)
        except Exception:
            pass
        ranges.ranges = new_ranges_list
        return new_modifier_values, ranges
    except Exception:
        return modifier_values, ranges
