#!/usr/bin/env python3

import yaml
import pathlib

# 获取当前脚本所在目录的绝对路径
script_dir = pathlib.Path(__file__).parent.resolve()

# 构建 YAML 文件的绝对路径
yaml_file = script_dir / 'args.yaml'

print(f"YAML 文件路径: {yaml_file}")

if yaml_file.exists():
    with open(yaml_file, 'r', encoding='utf-8') as f:
        result = yaml.load(f.read(), Loader=yaml.FullLoader)
    print(result, type(result))
else:
    print(f"错误: 文件不存在: {yaml_file}")

