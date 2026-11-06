"""输出后端读回：保留完整样本类型、位宽、空值及任意字段增删。"""
import copy
import io
import json
import unittest

from sample_outputs import apply_delta, compact_samples, binary_samples


class SampleOutputTests(unittest.TestCase):
    def test_增量保留嵌套数组与对象字段增删(self):
        base = dict(sample_id=1, pre_registers={'a/b~c': {'bits': '0'*129}},
                    pre_memory=[dict(address=10,value=None,bytes=1)], obsolete=True)
        delta = dict(set={'/sample_id': 2, '/pre_registers/a~1b~0c/bits': '1'+'0'*128,
                          '/pre_memory/0/value': 255, '/added': {'bool': False}}, remove=['/obsolete'])
        old = copy.deepcopy(base)
        result = apply_delta(base, delta)
        self.assertEqual(base, old)
        self.assertEqual(result['pre_registers']['a/b~c']['bits'], '1'+'0'*128)
        self.assertIsNone(base['pre_memory'][0]['value'])
        self.assertEqual(result['pre_memory'][0]['value'],255)
        self.assertNotIn('obsolete', result)
        with self.assertRaises((KeyError, AssertionError)):
            apply_delta(base, dict(set={}, remove=['/absent']))

    def test_紧凑文本逐条展开且校验组合个数(self):
        skeleton = dict(schema_version=1,sample_id=10,path_signature=7,class_id=0,truncated=False)
        record = dict(compact_schema_version=1,path_signature=7,class_id=0,skeleton=skeleton,
                      solution_count=2,guard_assignment={'1':True},
                      increments=[dict(solution_index=0,delta=dict(set={},remove=[])),
                                  dict(solution_index=1,delta=dict(set={'/sample_id':11},remove=[]))])
        text = json.dumps(record)+'\n'
        self.assertEqual([row['sample_id'] for row in compact_samples(io.StringIO(text))],[10,11])
        record['solution_count']=3
        with self.assertRaises((ValueError, AssertionError)):
            list(compact_samples(io.StringIO(json.dumps(record))))

    def test_二进制损坏头与截断必须拒绝(self):
        for data in [b'',b'ISLASB1\0',b'not a sample format']:
            with self.assertRaises((ValueError, AssertionError, EOFError)):
                list(binary_samples(io.BytesIO(data)))

    def test_紧凑长类逐值读取跨块数字和转义(self):
        class TinyRead(io.StringIO):
            def read(self,size=-1):
                return super().read(min(size,3))
        skeleton=dict(schema_version=1,sample_id=100,path_signature=7,class_id=0,truncated=False,text='\"中文\\')
        record=dict(compact_schema_version=1,path_signature=7,class_id=0,skeleton=skeleton,solution_count=12,
                    increments=[dict(solution_index=i,delta=dict(set={'/sample_id':100+i},remove=[])) for i in range(12)])
        rows=list(compact_samples(TinyRead(json.dumps(record)+'\n'+json.dumps(record)+'\n')))
        self.assertEqual([row['sample_id'] for row in rows],list(range(100,112))*2)


if __name__ == '__main__':
    unittest.main()
