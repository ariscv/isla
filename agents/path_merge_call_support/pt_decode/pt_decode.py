#!/usr/bin/env python3
"""独立的 RV64 LOAD 页表样本后处理；不调用 Isla 或求解器。"""
import argparse
from collections import Counter
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import re
import sys
import time


MASK64 = (1 << 64) - 1
SAMPLE_FIELDS = set("schema_version sample_id mode path_signature class_id truncated pre_registers "
                    "post_registers isa_state pre_memory post_memory result ret_val".split())
LOAD_FIELDS = [f"tuple#%bv12_%bv5_%bv5_%bool_%i64{i}" for i in range(5)]
EXCEPTION_FIELDS = [f"tuple#%bv64_%union zExceptionType{i}" for i in range(2)]
INFERENCE_NOTE = "位约束仅由本形状的已导出样本推断，非求解器约束；free 位不可独立任意组合。"


class DecodeError(ValueError):
    """输入、模型配置或重建路径不满足已支持的严格协议。"""


@dataclass(frozen=True)
class Config:
    svrsw60t59b: bool
    dirty_update: bool

    def __post_init__(self):
        if type(self.svrsw60t59b) is not bool or type(self.dirty_update) is not bool:
            raise DecodeError("模型配置必须是布尔值")


def exact(obj, fields, where):
    if not isinstance(obj, dict) or set(obj) != set(fields):
        raise DecodeError(f"{where}: 字段不符，要求 {sorted(fields)}，实际 {obj!r}")
    return obj


def uint(value, width, where):
    if type(value) is not int or not 0 <= value < (1 << width):
        raise DecodeError(f"{where}: 要求 {width} 位无符号整数，实际 {value!r}")
    return value


def bit_value(value, width):
    exact(value, ["bits"], "位串")
    s = value["bits"]
    if not isinstance(s, str) or len(s) != width or re.fullmatch("[01]+", s) is None:
        raise DecodeError(f"要求 {width} 位二进制串，实际 {s!r}")
    return int(s, 2)


def struct_value(value):
    exact(value, ["struct"], "结构体")
    if not isinstance(value["struct"], dict):
        raise DecodeError("struct 载荷必须是对象")
    return value["struct"]


def parse_satp(value):
    uint(value, 64, "satp")
    mode = value >> 60
    modes = {0: ("Bare", 0, 64), 8: ("Sv39", 3, 39), 9: ("Sv48", 4, 48), 10: ("Sv57", 5, 57)}
    if mode not in modes:
        raise DecodeError(f"不支持 satp.MODE={mode}；仅接受 RV64 Bare/Sv39/Sv48/Sv57")
    name, levels, va_bits = modes[mode]
    return dict(mode=name, levels=levels, va_bits=va_bits, asid=(value >> 44) & 0xffff,
                root_paddr=(value & ((1 << 44)-1)) << 12)


def decode_pte(value):
    uint(value, 64, "PTE")
    fields = {name: (value >> i) & 1 for i, name in enumerate("VRWXUGAD")}
    # vmem_pte.sail: PTE_Ext 是 pte[63:54]，其中 reserved=4:0、RSW_60t59b=6:5。
    for name, lo, width in [("RSW", 8, 2), ("PPN", 10, 44), ("reserved", 54, 5),
                            ("RSW_60t59b", 59, 2), ("PBMT", 61, 2), ("N", 63, 1)]:
        fields[name] = (value >> lo) & ((1 << width)-1)
    return fields


def classify_pte(value, level, config):
    uint(level, 3, "level")
    if level > 4:
        raise DecodeError("level 超过 Sv57 上限")
    f = decode_pte(value)
    # 顺序严格对应 Sail pte_is_invalid 的短路 OR。
    invalid = [(not f["V"], "v_zero"), (f["W"] and not f["R"], "write_without_read"),
               (f["N"], "n_disabled"), (f["PBMT"], "pbmt_disabled"),
               (f["RSW_60t59b"] and not config.svrsw60t59b, "rsw60t59b_disabled"),
               (f["reserved"], "reserved_nonzero")]
    for condition, reason in invalid:
        if condition:
            return dict(role="invalid", kind=f"invalid_{reason}", fields=f,
                        failure_reason=reason, page_size=None)
    if not (f["X"] or f["W"] or f["R"]):
        return dict(role="pointer", kind="pointer", fields=f,
                    failure_reason="pointer_at_level0" if level == 0 else None, page_size=None)
    permissions = "".join(c.lower() if f[c] else "-" for c in "RWX")
    return dict(role="leaf", kind=f"leaf_{permissions}_u{f['U']}", fields=f,
                failure_reason="superpage_misaligned" if f["PPN"] & ((1 << (9*level))-1) else None,
                page_size=1 << (12+9*level))


def memory_bytes(cells):
    if not isinstance(cells, list):
        raise DecodeError("内存必须是字节单元数组")
    memory = {}
    for cell in cells:
        exact(cell, ["address", "value", "bytes"], "内存单元")
        address = uint(cell["address"], 64, "内存地址")
        if type(cell["bytes"]) is not int or cell["bytes"] != 1:
            raise DecodeError("只支持 samples v1 的逐字节内存单元")
        value = uint(cell["value"], 8, "内存字节；null 不是已知初值")
        if address in memory:
            raise DecodeError(f"重复内存地址 {address:#x}")
        memory[address] = value
    return memory


def read_word(memory, address):
    uint(address, 64, "读取地址")
    if address > MASK64-7:
        raise DecodeError("8 字节读取越过 RV64 地址空间")
    missing = [address+i for i in range(8) if address+i not in memory]
    if missing:
        raise DecodeError("missing_memory: 缺少地址 " + ", ".join(f"{a:#x}" for a in missing))
    return sum(memory[address+i] << (i*8) for i in range(8))


def effective_address(sample, va=None, va_register=None, offset=0):
    if va is not None:
        if va_register is not None or offset:
            raise DecodeError("--va 不能与 --va-register/--offset 同用")
        return uint(va, 64, "--va")
    registers = sample["pre_registers"]
    if va_register is not None:
        if va_register == "x0":
            base = 0
        else:
            if va_register not in registers:
                raise DecodeError(f"缺少取址寄存器 {va_register}")
            base = bit_value(registers[va_register], 64)
        if type(offset) is not int or not -(1 << 63) <= offset < (1 << 63):
            raise DecodeError("--offset 必须是有符号 64 位整数")
        return (base+offset) & MASK64
    if offset:
        raise DecodeError("--offset 要求同时指定 --va-register")
    if "$instruction" in registers:
        instruction = exact(registers["$instruction"], ["ctor", "value"], "$instruction")
        if instruction["ctor"] != "LOAD":
            raise DecodeError("仅支持 LOAD(ld)；其他指令请显式使用 --va")
        fields = exact(struct_value(instruction["value"]), LOAD_FIELDS, "LOAD 参数")
        immediate = bit_value(fields[LOAD_FIELDS[0]], 12)
        rs1 = bit_value(fields[LOAD_FIELDS[1]], 5)
        bit_value(fields[LOAD_FIELDS[2]], 5)
        unsigned = exact(fields[LOAD_FIELDS[3]], ["bool"], "LOAD 无符号标记")["bool"]
        if type(unsigned) is not bool:
            raise DecodeError("LOAD 无符号标记必须为布尔值")
        width = exact(fields[LOAD_FIELDS[4]], ["i64"], "LOAD 宽度")["i64"]
        if unsigned or width != "8":
            raise DecodeError("当前仅支持 RV64 ld，要求 LOAD(is_unsigned=false,width=8)")
        if rs1 and f"x{rs1}" not in registers:
            raise DecodeError(f"缺少取址寄存器 x{rs1}；请传入 --va")
        base = 0 if rs1 == 0 else bit_value(registers[f"x{rs1}"], 64)
        return (base + (immediate-4096 if immediate & 0x800 else immediate)) & MASK64
    state = sample["isa_state"]
    if "$instruction" in state:
        text = state["$instruction"]
        if not isinstance(text, str):
            raise DecodeError("isa_state.$instruction 必须为汇编字符串")
        match = re.fullmatch(r"ld\s+x(?:[0-9]|[12][0-9]|3[01]),\s*([+-]?(?:0x[0-9a-fA-F]+|[0-9]+))\(x([0-9]|[12][0-9]|3[01])\)", text)
        if not match:
            raise DecodeError("无法解析 isa_state.$instruction；请使用 --va")
        imm_text, rs1 = match.groups()
        imm = int(imm_text, 16 if "0x" in imm_text else 10)
        if not -2048 <= imm <= 2047:
            raise DecodeError("ld 立即数超出有符号 12 位范围")
        return effective_address(sample, va_register=f"x{rs1}", offset=imm)
    raise DecodeError("缺少可解析的指令；请传入 --va，或 --va-register 与 --offset")


def result_category(result, va):
    exact(result, ["ctor", "value"], "result")
    name = result["ctor"]
    if name == "Retire_Success":
        if result["value"] != {"unit": True}:
            raise DecodeError("Retire_Success 载荷不是 unit")
        return name, None
    if name != "Memory_Exception":
        raise DecodeError(f"未知结果构造子 {name!r}")
    payload = exact(struct_value(result["value"]), EXCEPTION_FIELDS, "Memory_Exception 参数")
    if bit_value(payload[EXCEPTION_FIELDS[0]], 64) != va:
        raise DecodeError("Memory_Exception 地址与计算的 VA 不符")
    exception = exact(payload[EXCEPTION_FIELDS[1]], ["ctor", "value"], "异常类型")
    if exception["ctor"] not in {"E_Load_Page_Fault", "E_Load_Access_Fault", "E_Load_Addr_Align"}:
        raise DecodeError(f"未知 ld 异常类型 {exception['ctor']!r}")
    if exception["value"] != {"unit": True}:
        raise DecodeError("异常类型载荷不是 unit")
    return name, exception["ctor"]


def pma_readable(registers, address):
    """只用样本中的 PMA 证明提前终止；不猜测未记录的 PMP/设备行为。"""
    if "pma_regions" not in registers:
        return None
    regions = exact(registers["pma_regions"], ["list"], "pma_regions")["list"]
    if not isinstance(regions, list):
        raise DecodeError("pma_regions.list 必须是数组")
    known_attributes = set("cacheable coherent executable misaligned_fault read_idempotent readable "
                           "reservability supports_cbo_zero writable write_idempotent".split())
    for item in regions:
        region = exact(struct_value(item), ["base", "size", "attributes", "include_in_device_tree"], "PMA 区域")
        base, size = bit_value(region["base"], 64), bit_value(region["size"], 64)
        attrs = struct_value(region["attributes"])
        if set(attrs) - known_attributes or "readable" not in attrs:
            raise DecodeError(f"未知或不完整的 PMA 属性 {sorted(attrs)}")
        readable = exact(attrs["readable"], ["bool"], "PMA readable")["bool"]
        if type(readable) is not bool:
            raise DecodeError("PMA readable 必须为布尔值")
        if base <= address and address+8 <= base+size <= (1 << 64):
            return readable
    return False


def decode_sample(sample, config, va=None, va_register=None, offset=0):
    registers = sample["pre_registers"]
    satp = bit_value(registers["satp"], 64)
    translation = parse_satp(satp)
    address = effective_address(sample, va, va_register, offset)
    result, exception = result_category(sample["result"], address)
    status = bit_value(exact(struct_value(registers["mstatus"]), ["bits"], "mstatus")["bits"], 64)
    privilege = exact(registers["cur_privilege"], ["enum"], "cur_privilege")["enum"]
    if status & (1 << 17):
        mpp = (status >> 11) & 3
        if mpp not in {0, 1, 3}:
            raise DecodeError("mstatus.MPP 为保留值")
        privilege = {0: "User", 1: "Supervisor", 3: "Machine"}[mpp]
    if privilege not in {"User", "Supervisor", "Machine"}:
        raise DecodeError(f"不支持的有效权限 {privilege!r}")
    mode = "Bare" if privilege == "Machine" else translation["mode"]
    levels = 0 if mode == "Bare" else translation["levels"]
    vpn = [(address >> (12+9*i)) & 511 for i in range(levels)]
    memory = memory_bytes(sample["pre_memory"])
    decoded = dict(sample_id=sample["sample_id"], satp=f"0x{satp:016x}", mode=mode,
                   satp_mode=translation["mode"], root_paddr=translation["root_paddr"],
                   va=address, vpn=vpn, effective_privilege=privilege, mxr=bool(status & (1 << 19)),
                   sum=bool(status & (1 << 18)), entries=[], sequence=[], leaf_level=None,
                   page_size=None, result=result, exception_type=exception, failure_reason=None,
                   translated_paddr=None, paddr_if_success=None, termination=None)
    entries = decoded["entries"]
    used = set()
    failure = None
    physical = address if mode == "Bare" else None
    if address & 7:
        raise DecodeError("不支持非 8 字节对齐的 ld；跨页/未对齐平台策略需单独实现")
    if levels:
        width = translation["va_bits"]
        low = address & ((1 << width)-1)
        canonical = low | (MASK64 ^ ((1 << width)-1)) if low & (1 << (width-1)) else low
        if address != canonical:
            failure = "noncanonical_va"
        table = translation["root_paddr"]
        for level in reversed(range(levels)):
            if failure:
                break
            paddr = table + vpn[level]*8
            readable = pma_readable(registers, paddr)
            if readable is False:
                if any(paddr+i in memory for i in range(8)):
                    raise DecodeError(f"PMA 拒绝的 PTE 地址却出现在 pre_memory: {paddr:#x}")
                failure = "pte_read_pma_access_fault"
                decoded["termination"] = dict(level=level, paddr=paddr, evidence="sample_pma_no_read")
                break
            value = read_word(memory, paddr)
            used.update(range(paddr, paddr+8))
            entry = classify_pte(value, level, config)
            entry.update(level=level, paddr=paddr, value=f"0x{value:016x}")
            entries.append(entry)
            decoded["sequence"].append(dict(level=level, kind=entry["kind"]))
            failure = entry["failure_reason"]
            if entry["role"] == "leaf":
                decoded["leaf_level"], decoded["page_size"] = level, entry["page_size"]
            if failure:
                break
            fields = entry["fields"]
            if entry["role"] == "pointer":
                table = fields["PPN"] << 12
                continue
            if (privilege == "User" and not fields["U"]) or (
                    privilege == "Supervisor" and fields["U"] and not decoded["sum"]):
                failure = "privilege_permission"
            elif not (fields["R"] or (fields["X"] and decoded["mxr"])):
                failure = "load_permission"
            elif not fields["A"] and not config.dirty_update:
                failure = "accessed_update_disabled"
            if failure:
                entry["failure_reason"] = failure
                break
            page_size = entry["page_size"]
            physical = ((fields["PPN"] << 12) & ~(page_size-1)) | (address & (page_size-1))
            if not fields["A"]:
                post = memory_bytes(sample["post_memory"])
                if read_word(post, paddr) != value | (1 << 6):
                    raise DecodeError("A 位更新与 post_memory 不符；不支持未证实的写回失败")
            break
    if failure is None:
        if physical is None:
            raise DecodeError("内部不变量违反：遍历结束但没有物理地址")
        decoded["translated_paddr"] = physical
        if pma_readable(registers, physical) is False:
            if any(physical+i in memory and physical+i not in used for i in range(8)):
                raise DecodeError("PMA 拒绝的数据地址却有读取字节")
            failure = "data_read_pma_access_fault"
            decoded["termination"] = dict(level=None, paddr=physical, evidence="sample_pma_no_read")
        else:
            value = read_word(memory, physical)
            used.update(range(physical, physical+8))
            entries.append(dict(level=None, paddr=physical, value=f"0x{value:016x}",
                                role="data", fields={}, kind="data", failure_reason=None, page_size=None))
            decoded["paddr_if_success"] = physical
    if failure in {"pte_read_pma_access_fault", "data_read_pma_access_fault"}:
        predicted = "E_Load_Access_Fault"
    elif failure:
        predicted = "E_Load_Page_Fault"
    else:
        predicted = None
    if exception != predicted:
        raise DecodeError(f"result_mismatch: 解码预测 {predicted or 'Retire_Success'}，样本为 {exception or result}")
    extra = sorted(set(memory)-used)
    if extra:
        raise DecodeError(f"无法归属到页表/数据读取的 pre_memory 地址: {[hex(a) for a in extra[:8]]}")
    decoded["failure_reason"] = failure
    return decoded


def shape_key(decoded):
    return json.dumps(dict(mode=decoded["mode"], sequence=decoded["sequence"],
                           leaf_level=decoded["leaf_level"], result=decoded["result"],
                           exception_type=decoded["exception_type"], failure_reason=decoded["failure_reason"]),
                      sort_keys=True, separators=(",", ":"))


def shape_name(key):
    shape = json.loads(key)
    sequence = "--".join(f"l{e['level']}-{e['kind']}" for e in shape["sequence"]) or "no-pte"
    leaf = "no-leaf" if shape["leaf_level"] is None else f"leaf-l{shape['leaf_level']}"
    return "--".join([shape["mode"].lower(), sequence, leaf, shape["exception_type"] or shape["result"],
                      shape["failure_reason"] or "success"])


def aggregate(samples):
    groups = {}
    for decoded in samples:
        key = shape_key(decoded)
        values = [int(e["value"], 16) for e in decoded["entries"]]
        context = (decoded["satp"], decoded["root_paddr"], decoded["va"], decoded["effective_privilege"],
                   decoded["mxr"], decoded["sum"])
        if key not in groups:
            groups[key] = dict(count=0, representative=decoded, and_values=values[:], or_values=values[:],
                               context=context, context_varies=False, addresses_varied=[False]*len(values))
        group = groups[key]
        rep = group["representative"]
        if len(values) != len(group["and_values"]) or [e["role"] for e in decoded["entries"]] != [e["role"] for e in rep["entries"]]:
            raise DecodeError("同形状的条目角色或数量不同，无法形成逐层位约束")
        group["count"] += 1
        group["context_varies"] |= context != group["context"]
        for i, value in enumerate(values):
            group["and_values"][i] &= value
            group["or_values"][i] |= value
            group["addresses_varied"][i] |= decoded["entries"][i]["paddr"] != rep["entries"][i]["paddr"]
        # 代表由最小 sample_id 决定，与 JSONL 的并发落盘顺序无关。
        if decoded["sample_id"] < rep["sample_id"]:
            group["representative"] = decoded
    shapes = []
    for key, group in groups.items():
        rep = dict(group["representative"])
        rep["entries"] = [dict(e) for e in rep["entries"]]
        for i, entry in enumerate(rep["entries"]):
            free = group["and_values"][i] ^ group["or_values"][i]
            entry.update(free_mask=f"0x{free:016x}", fixed_mask=f"0x{MASK64 ^ free:016x}",
                         fixed_value=f"0x{group['and_values'][i]:016x}",
                         paddr_varies=group["addresses_varied"][i])
        shapes.append(dict(name=shape_name(key), key=json.loads(key), count=group["count"],
                           sequence=rep["sequence"], result=rep["result"], exception_type=rep["exception_type"],
                           leaf_level=rep["leaf_level"], failure_reason=rep["failure_reason"],
                           context_varies=group["context_varies"], representative=rep, notes=[INFERENCE_NOTE]))
    return sorted(shapes, key=lambda s: (-s["count"], s["name"]))


def compare_distributions(fork, merge):
    same, different = [], []
    for key in sorted(set(fork) | set(merge)):
        f = fork[key] if key in fork else 0
        m = merge[key] if key in merge else 0
        item = dict(shape=key, fork_count=f, merge_count=m, delta_merge_minus_fork=m-f)
        (same if f == m else different).append(item)
    return dict(equal=not different, same=same, different=different)


def unique_object(pairs):
    obj = {}
    for key, value in pairs:
        if key in obj:
            raise DecodeError(f"重复 JSON 字段 {key!r}")
        obj[key] = value
    return obj


def reject_constant(value):
    raise DecodeError(f"不接受非标准 JSON 常量 {value}")


def validate_concrete(value):
    """复用 samples v1 的具体值协议；未知标签即使暂不参与遍历也拒绝。"""
    if not isinstance(value, dict):
        raise DecodeError(f"具体值必须是带类型的对象: {value!r}")
    if "ctor" in value:
        exact(value, ["ctor", "value"], "构造子")
        if not isinstance(value["ctor"], str):
            raise DecodeError("构造子名字必须是字符串")
        validate_concrete(value["value"])
        return
    if len(value) != 1:
        raise DecodeError(f"具体值必须有一个类型标签: {value!r}")
    tag, payload = next(iter(value.items()))
    if tag == "bits":
        if not isinstance(payload, str) or re.fullmatch("[01]+", payload) is None:
            raise DecodeError("非法具体位串")
    elif tag in {"bool", "unit"}:
        if type(payload) is not bool or (tag == "unit" and not payload):
            raise DecodeError(f"非法 {tag} 具体值")
    elif tag in {"i64", "i128"}:
        if not isinstance(payload, str) or re.fullmatch(r"-?(0|[1-9][0-9]*)", payload) is None:
            raise DecodeError(f"非法 {tag} 整数串")
        width = 64 if tag == "i64" else 128
        if not -(1 << (width-1)) <= int(payload) < (1 << (width-1)):
            raise DecodeError(f"{tag} 具体值越界")
    elif tag in {"enum", "string"}:
        if not isinstance(payload, str):
            raise DecodeError(f"非法 {tag} 具体值")
    elif tag == "struct":
        if not isinstance(payload, dict):
            raise DecodeError("struct 载荷必须是对象")
        for child in payload.values():
            validate_concrete(child)
    elif tag in {"vector", "list"}:
        if not isinstance(payload, list):
            raise DecodeError(f"{tag} 载荷必须是数组")
        for child in payload:
            validate_concrete(child)
    else:
        raise DecodeError(f"未知具体值类型标签 {tag!r}")


def load_samples(path, metadata=None):
    digest = hashlib.sha256()
    ids = set()
    truncated = 0
    modes = Counter()
    with Path(path).open("rb") as stream:
        for line_number, line in enumerate(stream, 1):
            digest.update(line)
            try:
                sample = json.loads(line, object_pairs_hook=unique_object, parse_constant=reject_constant)
                exact(sample, SAMPLE_FIELDS, "样本")
                if type(sample["schema_version"]) is not int or sample["schema_version"] != 1:
                    raise DecodeError("只支持 sample schema_version=1")
                sample_id = uint(sample["sample_id"], 64, "sample_id")
                if sample_id in ids:
                    raise DecodeError(f"重复 sample_id={sample_id}")
                ids.add(sample_id)
                uint(sample["path_signature"], 64, "path_signature")
                if sample["class_id"] is not None:
                    uint(sample["class_id"], 64, "class_id")
                if type(sample["truncated"]) is not bool:
                    raise DecodeError("truncated 必须是布尔值")
                if sample["mode"] not in {"fork", "merge"}:
                    raise DecodeError("未知 mode")
                for name in ["pre_registers", "post_registers", "isa_state"]:
                    if not isinstance(sample[name], dict):
                        raise DecodeError(f"{name} 必须是对象")
                for name in ["pre_registers", "post_registers"]:
                    for value in sample[name].values():
                        validate_concrete(value)
                validate_concrete(sample["result"])
                if any(not isinstance(value, str) for value in sample["isa_state"].values()):
                    raise DecodeError("isa_state 的值必须是字符串")
                memory_bytes(sample["post_memory"])
                if not isinstance(sample["ret_val"], str):
                    raise DecodeError("ret_val 必须是字符串")
                truncated += sample["truncated"]
                modes[sample["mode"]] += 1
                yield sample
            except (DecodeError, ValueError, TypeError, KeyError) as error:
                raise DecodeError(f"{Path(path).name}:{line_number}: {error}") from error
    if not ids:
        raise DecodeError(f"空样本文件 {path}")
    if metadata is not None:
        metadata.update(input_name=Path(path).name, sha256=digest.hexdigest(), sample_count=len(ids),
                        truncated_count=truncated, modes=dict(modes))


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")


def write_outputs(directory, shapes, metadata):
    directory.mkdir(parents=True, exist_ok=True)
    common = dict(schema_version=1, metadata=metadata)
    write_json(directory/"shapes.json", dict(**common, shapes=shapes))
    tables = []
    for shape in shapes:
        rep = shape["representative"]
        tables.append(dict(name=shape["name"], count=shape["count"], satp=rep["satp"],
                           mode=rep["mode"], root_paddr=rep["root_paddr"], va=rep["va"], vpn=rep["vpn"],
                           context=dict(effective_privilege=rep["effective_privilege"], mxr=rep["mxr"], sum=rep["sum"]),
                           leaf_level=rep["leaf_level"], page_size=rep["page_size"], entries=rep["entries"],
                           expected=dict(result=rep["result"], exception_type=rep["exception_type"],
                                         paddr_if_success=rep["paddr_if_success"]),
                           failure_reason=rep["failure_reason"], termination=rep["termination"],
                           representative_sample_id=rep["sample_id"], context_varies=shape["context_varies"],
                           notes=[INFERENCE_NOTE, "satp、地址、权限上下文和 expected 是代表样本的具体值。"
                                  "data 条目不是 PTE，其 fields 为空。未读取的下级页表不补零。"] ))
    write_json(directory/"page_tables.json", dict(**common, page_tables=tables))
    total = metadata["sample_count"]
    results, leaves = Counter(), Counter()
    lines = ["# 页表形状分布", "", f"样本 {total}；形状 {len(shapes)}；处理耗时 {metadata['elapsed_seconds']:.3f} 秒。",
             "", f"truncated=true：{metadata['truncated_count']}。计数表示导出代表样本频数，不表示全部具体状态的概率。",
             "", "| 形状 | 计数 | 占比 |", "| --- | ---: | ---: |"]
    for shape in shapes:
        lines.append(f"| `{shape['name']}` | {shape['count']} | {shape['count']/total:.4%} |")
        results[shape["exception_type"] or shape["result"]] += shape["count"]
        label = "无叶子" if shape["leaf_level"] is None else f"L{shape['leaf_level']}"
        leaves[label] += shape["count"]
    for title, counts in [("结果类别", results), ("叶子层（包括叶子处失败）", leaves)]:
        lines += ["", f"## {title}", "", "| 类别 | 计数 | 占比 |", "| --- | ---: | ---: |"]
        lines += [f"| {key} | {count} | {count/total:.4%} |" for key, count in counts.most_common()]
    lines += ["", INFERENCE_NOTE, ""]
    (directory/"distribution.md").write_text("\n".join(lines), encoding="utf-8")


def process(path, mode, config, va, va_register, offset):
    start = time.perf_counter()
    metadata = dict(config=asdict(config), addressing=dict(va=va, va_register=va_register, offset=offset),
                    python_version=sys.version.split()[0],
                    decoder_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())

    def decoded_samples():
        for sample in load_samples(path, metadata):
            if sample["mode"] != mode:
                raise DecodeError(f"{Path(path).name}: sample_id={sample['sample_id']}，要求 mode={mode}")
            try:
                yield decode_sample(sample, config, va, va_register, offset)
            except (DecodeError, KeyError, TypeError) as error:
                raise DecodeError(f"{Path(path).name}: sample_id={sample['sample_id']}: {error}") from error

    shapes = aggregate(decoded_samples())
    metadata["elapsed_seconds"] = round(time.perf_counter()-start, 6)
    return shapes, metadata


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fork", type=Path, required=True, help="分叉样本 JSONL")
    parser.add_argument("--merge", type=Path, required=True, help="合并样本 JSONL")
    parser.add_argument("--out", type=Path, required=True, help="报告目录")
    parser.add_argument("--svrsw60t59b", choices=["enabled", "disabled"], required=True, help="模型中的扩展开关")
    parser.add_argument("--dirty-update", choices=["enabled", "disabled"], required=True, help="模型的平台 A/D 更新开关")
    addresses = parser.add_mutually_exclusive_group()
    addresses.add_argument("--va", type=lambda s: int(s, 0), help="显式 RV64 虚拟地址；覆盖指令解码")
    addresses.add_argument("--va-register", help="显式取址寄存器（完整名字）")
    parser.add_argument("--offset", type=lambda s: int(s, 0), default=0, help="寄存器取址的有符号字节偏移")
    args = parser.parse_args(argv)
    if args.offset and not args.va_register:
        parser.error("--offset 要求 --va-register")
    config = Config(args.svrsw60t59b == "enabled", args.dirty_update == "enabled")
    start = time.perf_counter()
    try:
        fork, fm = process(args.fork, "fork", config, args.va, args.va_register, args.offset)
        print(f"fork：{fm['sample_count']} 样本，{len(fork)} 形状，{fm['elapsed_seconds']:.3f} 秒", flush=True)
        merge, mm = process(args.merge, "merge", config, args.va, args.va_register, args.offset)
        print(f"merge：{mm['sample_count']} 样本，{len(merge)} 形状，{mm['elapsed_seconds']:.3f} 秒", flush=True)
        # 两组完整解码后再写报告，避免输入错误留下半组新产物。
        write_outputs(args.out, fork, fm)
        write_outputs(args.out/"fork", fork, fm)
        write_outputs(args.out/"merge", merge, mm)
        comparison = compare_distributions({shape_key(s['representative']): s['count'] for s in fork},
                                            {shape_key(s['representative']): s['count'] for s in merge})
        for group in [comparison["same"], comparison["different"]]:
            for row in group:
                row["key"] = json.loads(row["shape"])
                row["shape"] = shape_name(row["shape"])
        comparison.update(schema_version=1, fork=fm, merge=mm,
                          elapsed_seconds=round(time.perf_counter()-start, 6),
                          notes=["只比较形状计数；不证明具体页表集合、全部可行解或寄存器后态等价。",
                                 "一级类内仅保留代表模型；truncated 不会被当作完整具体值枚举。"])
        write_json(args.out/"crosscheck.json", comparison)
        lines = ["# 分叉与合并的页表形状交叉检验", "",
                 f"结论：{'相同' if comparison['equal'] else '不同'}。相同计数的形状 {len(comparison['same'])}，差异形状 {len(comparison['different'])}。",
                 "", f"fork：{fm['sample_count']} 行，{len(fork)} 形状，{fm['elapsed_seconds']:.3f} 秒。",
                 f"merge：{mm['sample_count']} 行，{len(merge)} 形状，{mm['elapsed_seconds']:.3f} 秒。",
                 f"总流程：{comparison['elapsed_seconds']:.3f} 秒。", "",
                 f"truncated=true：fork {fm['truncated_count']}，merge {mm['truncated_count']}。",
                 "", "根目录分布与模板取自 fork；两组各自的完整摘要位于 fork/、merge/。", "",
                 "| 形状 | fork | merge | merge − fork |", "| --- | ---: | ---: | ---: |"]
        rows = comparison["different"]+comparison["same"]
        for row in sorted(rows, key=lambda r: (-max(r["fork_count"], r["merge_count"]), r["shape"])):
            lines.append(f"| `{row['shape']}` | {row['fork_count']} | {row['merge_count']} | {row['delta_merge_minus_fork']} |")
        lines += ["", *comparison["notes"], ""]
        if not comparison["equal"]:
            lines += ["可能原因需另查：一级守卫类与原分叉路径并非一一对应；代表模型选择改变具体失败原因；"
                      "输入截断、运行配置或合并行为存在差异。此报告没有调整分类来消除差异。", ""]
        (args.out/"crosscheck.md").write_text("\n".join(lines), encoding="utf-8")
        print(f"交叉检验：{'相同' if comparison['equal'] else '不同'}；总耗时 {comparison['elapsed_seconds']:.3f} 秒")
        return 0 if comparison["equal"] else 1
    except (DecodeError, OSError) as error:
        print(f"解码失败：{error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
