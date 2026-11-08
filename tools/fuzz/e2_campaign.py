"""只读复用 E2 场景接口，准备 campaign 配置及编码空间对照。"""
import json
import os
from pathlib import Path
import random
import sys


def prepare(root, experiment, source, scenario, output, random_seed, control_count=150):
    sys.path.insert(0, os.environ.get('DIFFTEST_XIANGSHAN_DIR',
        str(root.parent / 'replay-p0/difftest-xiangshan')))
    import paging_fuzz as fuzz
    import paging_replay as replay
    import replay_symbolic_prestate as symbolic

    corpus, template, config = symbolic.scenario_inputs(experiment, scenario)
    files = symbolic.read_json(source / 'files.json')
    files.update(isarch=str(root / 'target/release/isarch'), config=str(config))
    command = symbolic.bound_template(symbolic.read_json(template)['command'],
                                     {key: Path(value) for key, value in files.items()}, scenario)
    command[0] = files['isarch']
    for flag in ('--check-samples', '--check-samples-report'):
        index = command.index(flag)
        del command[index:index+2]
    profile = symbolic.scenario_profile(symbolic.read_json(source / 'profile.json'), scenario)
    profile['isla'].pop('isarch_sha256', None)
    profile['isla']['config_toml_sha256'] = replay.sha256(config)
    profile['ir']['input_constraint'] = 'cur_privilege in {User,Supervisor}; SUM/MXR symbolic in E2.toml'
    generation, environment = replay.platform_hashes(profile)
    lock = dict(schema_version=2, platform_gen_sha256=generation, platform_env_sha256=environment,
        ir_sha256=profile['ir']['ir_sha256'], config_toml_sha256=profile['isla']['config_toml_sha256'],
        emu_sha256=profile['env']['emu_sha256'], nemu_sha256=profile['env']['nemu_sha256'])
    for name, value in [('profile.json', profile), ('profile.lock.json', lock), ('files.json', files)]:
        fuzz.write_json(output / name, value)
    replay.verify_platform_lock(profile, lock, {})
    decoder, provenance = replay.load_decoder(os.environ.get('PT_DECODE_DIR',
        str(root.parent / 'isla-enumerate/agents/path_merge_call_support/pt_decode')), standard_paging=True)
    parents = [json.loads(line) for line in corpus.read_text().splitlines()]
    rng = random.Random(random_seed)
    rng.shuffle(parents)
    controls, records, rejected = [], [], []
    # 对照重新从 E2 corpus 生成；E0 的类号和固定前态不能移植。
    for attempt in range(control_count * 20):
        if len(controls) == control_count:
            break
        parent = parents[attempt % len(parents)]
        operator = fuzz.OPERATORS[len(controls) % len(fuzz.OPERATORS)]
        try:
            sample, decoded, change = fuzz.mutate(parent, operator, rng, decoder, profile, len(controls))
        except fuzz.MutationRejected as error:
            rejected.append(dict(attempt=attempt, operator=operator, reason=str(error)))
            continue
        change['sample_id'] = sample['sample_id']
        controls.append(sample)
        records.append(change)
    assert len(controls) == control_count, 'E2 编码空间对照生成预算耗尽'
    (output / 'control-inputs.jsonl').write_text(''.join(
        json.dumps(row, ensure_ascii=False, separators=(',', ':'))+'\n' for row in controls))
    fuzz.write_json(output / 'controls.json', records)
    fuzz.write_json(output / 'controls-audit.json', dict(generated=len(controls), rejected=rejected,
        decoder=provenance, corpus=str(corpus), config=str(config), scenario_config_id=scenario+'-e2'))
    return command, corpus, output / 'controls.json'
