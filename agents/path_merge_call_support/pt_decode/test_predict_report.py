"""预测报告汇总和未收尾F11块的只读下界检查。"""
import json,struct,tempfile,unittest
from pathlib import Path
from predict_report import unfinished_binary_lower_bound, aggregate, constrain_lower_bound, bounded_class_count, read_paths, report

class PredictReportTests(unittest.TestCase):
    def test_汇总只对独立路径方差相加且有界真值单列(self):
        paths=[dict(path_signature=7,total=dict(mean=100,standard_error=3),bounded_output=dict(exact='20')),
               dict(path_signature=9,total=dict(mean=200,standard_error=4),bounded_output=dict(exact='24'))]
        report=aggregate(paths)
        self.assertEqual(report['total']['mean'],300)
        self.assertEqual(report['total']['standard_error'],5)
        self.assertEqual(report['bounded_output_exact'],'44')
        self.assertEqual(report['binary_bytes_at_1300']['mean'],390000)

    def test_下界约束保留原始统计且区间矛盾直接失败(self):
        total=dict(mean=100,standard_error=10,confidence_95=[80,120])
        constrain_lower_bound(total,110)
        self.assertEqual(total['mean'],100)
        self.assertEqual(total['point_prediction'],110)
        self.assertEqual(total['confidence_95_with_lower_bound'],[110,120])
        with self.assertRaises(AssertionError):constrain_lower_bound(total,121)

    def test_有界类数仅在域下界已足够时确定(self):
        path=dict(bounded_output=dict(class_cap=512,path_cap=256),guard_classes=[
            dict(exact='20'),dict(lower_bound='257')])
        self.assertEqual(bounded_class_count(path),2)
        path['guard_classes'][1]['lower_bound']='1'
        self.assertIsNone(bounded_class_count(path))

    def test_截止中断时只读取完整报告记录(self):
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory)/'stderr.txt'
            p.write_bytes(b'[MERGE_PREDICT_RESULT] {"path_signature":7}\n[MERGE_PREDICT_RESULT] {"path_signature":9')
            self.assertEqual(read_paths(p),[dict(path_signature=7)])

    def test_路径未完成时不把小计当成全场景总数(self):
        with tempfile.TemporaryDirectory() as directory:
            d=Path(directory)
            path=dict(path_signature=7,total=dict(mean=100,standard_error=1),bounded_output=dict(exact='10'))
            text='[MERGE_PREDICT_START] {"path_signature":7}\n[MERGE_PREDICT_START] {"path_signature":9}\n'
            text+='[MERGE_PREDICT_RESULT] '+json.dumps(path)+'\n'
            (d/'stderr.txt').write_text(text)
            result=report(d,complete=False)
            self.assertIsNone(result['total'])
            self.assertEqual(result['completed_paths_total']['mean'],100)
            self.assertEqual(result['unfinished_paths'][0]['path_signature'],9)

    def test_被终止文件只计完整块且不要求正常文件尾(self):
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory)/'samples.bin'
            # 扫描下界仅依索引和完整载荷边界；不展开样本。
            data=b'ISLASB1\0'+struct.pack('<IIII',2,24,40,2)+b'{}'
            data+=struct.pack('<QQQQQ',7,0,256,3,0)+b'abc'
            data+=struct.pack('<QQQQQ',7,0,256,3,0)+b'ab'
            p.write_bytes(data)
            result=unfinished_binary_lower_bound(p)
            self.assertEqual(result['combinations'],256)
            self.assertEqual(result['paths'],{'7':256})
            self.assertEqual(result['complete_blocks'],1)
            self.assertFalse(result['normal_end'])

if __name__=='__main__':unittest.main()
