"""完整位组合测量的下界汇总，不以日志行数估计进度。"""
import unittest

from count_measure import CountMeasurement


class CountMeasurementTests(unittest.TestCase):
    def test_分区快照替换且完成路径不重复累加(self):
        measure = CountMeasurement()
        for entry in [
            dict(path_signature=7, phase="started", partitions=2),
            dict(path_signature=8, phase="started", partitions=1),
            dict(path_signature=7, phase="progress", partition_id=0, counted_classes=0, counted_paths=4096),
            dict(path_signature=7, phase="progress", partition_id=0, counted_classes=1, counted_paths=8192),
            dict(path_signature=7, phase="partition_complete", partition_id=1, counted_classes=1, counted_paths=12),
        ]:
            measure.observe(entry)
        report = measure.report()
        self.assertEqual(report["lower_bound"], 8204)
        self.assertEqual(report["completed_paths"], 0)
        self.assertEqual(report["started_paths"], 2)
        measure.observe(dict(path_signature=7, phase="complete", counted_classes=2, counted_paths=8207,
                             path_truncated=False, truncated_classes=0))
        measure.observe(dict(path_signature=8, phase="complete", counted_classes=1, counted_paths=3,
                             path_truncated=False, truncated_classes=0))
        report = measure.report()
        self.assertEqual(report["lower_bound"], 8210)
        self.assertEqual(report["completed_paths"], 2)
        self.assertTrue(report["complete"])

    def test_倒退快照与伪完整必须报错(self):
        measure = CountMeasurement()
        measure.observe(dict(path_signature=1, phase="started", partitions=1))
        measure.observe(dict(path_signature=1, phase="progress", partition_id=0, counted_classes=0, counted_paths=10))
        with self.assertRaises(AssertionError):
            measure.observe(dict(path_signature=1, phase="progress", partition_id=0, counted_classes=0, counted_paths=9))
        with self.assertRaises(AssertionError):
            measure.observe(dict(path_signature=1, phase="complete", counted_classes=1, counted_paths=10,
                                 path_truncated=False, truncated_classes=1))


if __name__ == "__main__":
    unittest.main()
