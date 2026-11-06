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

class BudgetOutputTests(unittest.TestCase):
    def test_流式二进制正常尾及路径类截断标记(self):
        import struct
        from sample_outputs import binary_summary
        def encode(item):
            if item is None: return b'\0'
            if isinstance(item,bool): return bytes([2 if item else 1])
            if isinstance(item,int): return b'\3'+struct.pack('<Q',item)
            if isinstance(item,str):
                text=item.encode()
                return b'\6'+struct.pack('<I',len(text))+text
            if isinstance(item,list): return b'\7'+struct.pack('<I',len(item))+b''.join(map(encode,item))
            return b'\10'+struct.pack('<I',len(item))+b''.join(encode(k)+encode(v) for k,v in item.items())
        fields=[['path_signature','u64',0],['class_id','u64',8],['solution_count','u64',16],
                ['payload_bytes','u64',24],['flags','u64',32]]
        metadata=json.dumps(dict(schema_version=2,sample_schema_version=1,endianness='little',
                                 payload_codec='typed-json-v1',fields=fields)).encode()
        prefix=b'ISLASB1\0'+struct.pack('<IIII',2,24,40,len(metadata))+metadata
        skeleton=dict(schema_version=1,sample_id=0,path_signature=7,class_id=0,truncated=False)
        header=dict(compact_schema_version=1,path_nonce=3,path_signature=7,class_id=0,solution_count=1,skeleton=skeleton)
        payload=encode(header)+encode(dict(solution_index=0,delta=dict(set={},remove=[])))
        data=prefix+struct.pack('<QQQQQ',7,0,1,len(payload),0)+payload
        offset=len(data)
        # 原因/组合/路径数/类数 + 路径和类各32字节。
        summary=struct.pack('<'+'Q'*12,1,1,1,1,3,7,1,1,3,0,1,1)
        data+=struct.pack('<QQQQQ',0,0,0,len(summary),2)+summary+struct.pack('<QQQQQ',0,0,0,offset,(1<<64)-1)
        self.assertEqual(binary_summary(io.BytesIO(data))['combinations'],1)
        rows=list(binary_samples(io.BytesIO(data)))
        self.assertEqual(rows,[dict(skeleton,truncated=True)])
        with self.assertRaises((AssertionError,EOFError)):
            list(binary_samples(io.BytesIO(data[:-1])))


if __name__ == '__main__':
    unittest.main()
