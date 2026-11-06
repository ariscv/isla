"""汇总predict路径报告；读取取消的F11文件完整块下界，不修改旧样本。"""
import argparse
import json
import math
from pathlib import Path
import struct


def unfinished_binary_lower_bound(path):
    size=path.stat().st_size
    total=blocks=0
    paths={}
    normal=False
    with path.open('rb') as source:
        assert source.read(8)==b'ISLASB1\0'
        version,header,record,metadata=struct.unpack('<IIII',source.read(16))
        assert version in (1,2) and (header,record)==(24,40)
        source.seek(metadata,1)
        end=source.tell()
        while source.tell()+40<=size:
            signature,cls,count,length,flags=struct.unpack('<QQQQQ',source.read(40))
            if flags==(1<<64)-1:
                normal=source.tell()==size
                end=source.tell()
                break
            if flags==2:
                assert version==2
                if source.tell()+length>size:break
                source.seek(length,1)
                end=source.tell()
                continue
            assert flags in (0,1) and count>0
            if source.tell()+length>size:break
            source.seek(length,1)
            total+=count
            blocks+=1
            key=str(signature)
            paths[key]=paths.get(key,0)+count
            end=source.tell()
    return dict(combinations=total,paths=paths,complete_blocks=blocks,normal_end=normal,
                file_bytes=size,complete_prefix_bytes=end,unread_tail_bytes=size-end)


def bounded_class_count(path):
    """按规范类序证明有界输出的类数；未能确定时明确返回未知。"""
    scope=path.get('bounded_output',{})
    if not path.get('guard_class_catalog_complete',True) or 'guard_classes' not in path or scope.get('sample_stride',1)!=1:return None
    total=classes=0
    for cls in path['guard_classes']:
        if total>=scope['path_cap']:return classes
        if 'exact' in cls:
            total+=min(scope['class_cap'],int(cls['exact']))
            classes+=1
        else:
            lower=min(scope['class_cap'],int(cls['lower_bound']))
            return classes+1 if total+lower>=scope['path_cap'] else None
    return classes


def aggregate(paths):
    assert len({p['path_signature'] for p in paths})==len(paths)
    mean=sum(p['total']['mean'] for p in paths)
    se=math.sqrt(sum(p['total']['standard_error']**2 for p in paths))
    confidence=[max(0,mean-1.96*se),mean+1.96*se]
    bounded=[p.get('bounded_output',{}).get('exact') for p in paths]
    exacts=[p['total'].get('exact') for p in paths]
    bounded_classes=[bounded_class_count(p) for p in paths]
    total=dict(mean=mean,standard_error=se,confidence_95=confidence,
               exact=str(sum(map(int,exacts))) if all(v is not None for v in exacts) else None,
               interval_method='independent_path_variances_normal_approximation')
    return dict(total=total,bounded_classes_exact=sum(bounded_classes) if all(v is not None for v in bounded_classes) else None,bounded_output_exact=str(sum(map(int,bounded))) if all(v is not None for v in bounded) else None,
                binary_bytes_at_1300=dict(mean=mean*1300,confidence_95=[v*1300 for v in confidence]),
                paths=paths)


def read_paths(stderr):
    marker='[MERGE_PREDICT_RESULT] '
    paths=[]
    for line in stderr.read_bytes().splitlines(keepends=True):
        if line.startswith(marker.encode()) and line.endswith(b'\n'):
            paths.append(json.loads(line[len(marker):]))
    return paths


def constrain_lower_bound(total, lower):
    """保留未经修饰的蒙特卡洛均值；另列满足已知事实的点预测及区间交集。"""
    assert total['confidence_95'][1]>=lower, '95%区间仍低于已写下界，预测校验失败'
    total['known_lower_bound']=lower
    total['point_prediction']=max(total['mean'],lower)
    total['confidence_95_with_lower_bound']=[max(total['confidence_95'][0],lower),total['confidence_95'][1]]


def report(directory,old_samples=None,complete=False):
    paths=read_paths(directory/'stderr.txt')
    result=aggregate(paths)
    result['completed']=complete
    result['total_scope']='whole_scenario' if complete else 'completed_paths_only'
    starts=[]
    data=(directory/'stderr.txt').read_bytes()
    partial_result=bool(data and not data.endswith(b'\n') and data.split(b'\n')[-1].startswith(b'[MERGE_PREDICT_RESULT] '))
    result['incomplete_result_record']=partial_result
    if complete:assert not partial_result,'正常退出不得缺少报告记录尾部'
    for line in data.splitlines(keepends=True):
        marker=b'[MERGE_PREDICT_START] '
        if line.startswith(marker) and line.endswith(b'\n'):starts.append(json.loads(line[len(marker):]))
    result['completed_paths']=len(paths)
    result['started_paths']=len(starts)
    finished={p['path_signature'] for p in paths}
    result['unfinished_paths']=[dict(start,status='not_completed') for start in starts if start['path_signature'] not in finished]
    if old_samples:
        lower=unfinished_binary_lower_bound(old_samples)
        result['f11_lower_bound']=lower
        checks=[]
        for p in paths:
            bound=lower['paths'].get(str(p['path_signature']),0)
            constrain_lower_bound(p['total'],bound)
            checks.append(dict(path_signature=p['path_signature'],f11_lower_bound=bound,
                               raw_mean_at_least_lower_bound=p['total']['mean']>=bound,
                               prediction_at_least_lower_bound=p['total']['point_prediction']>=bound))
        result['f11_path_checks']=checks
        if complete:
            constrain_lower_bound(result['total'],lower['combinations'])
            assert all(check['prediction_at_least_lower_bound'] for check in checks),'路径预测低于已写下界'
    result['completed_paths_total']=result['total'].copy()
    result['completed_paths_binary_bytes_at_1300']=result['binary_bytes_at_1300'].copy()
    if not complete:
        result['total']=None
        result['binary_bytes_at_1300']=None
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory',type=Path,required=True)
    parser.add_argument('--f11-samples',type=Path)
    parser.add_argument('--completed',action='store_true')
    args=parser.parse_args()
    result=report(args.directory,args.f11_samples,args.completed)
    (args.directory/'prediction.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(dict(total=result['total'],completed_paths=result['completed_paths'],
                          started_paths=result['started_paths']),ensure_ascii=False))

if __name__=='__main__':main()
