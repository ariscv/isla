//! 历史共享的克隆隔离、回滚和逻辑序列特征化。
use super::*;
fn record(id: usize) -> RegionMergeRecord<B64> {
    RegionMergeRecord {
        record_id: id,
        parent_record: None,
        arm: "root",
        function: TOP_LEVEL_LET,
        branch_pc: 0,
        join: crate::ir::regions::RegionPoint::FunctionExit,
        condition: Sym::from_u32(id as u32),
        source_loc: info(),
        depth: 1,
        dead: false,
        value_symbols: Default::default(),
        input_symbols: Default::default(),
        single_arm_reads: Default::default(),
        memory_reads: Default::default(),
    }
}
#[test]
fn shared_history_frame_clone_and_rollback() {
    let mut frame = make_frame(vec![Instr::End]);
    frame.region_merge_records.push(record(1));
    let saved = freeze_frame(&frame);
    let mut cloned = frame.clone();
    assert!(
        std::ptr::eq(
            frame.region_merge_records.iter().next().unwrap(),
            cloned.region_merge_records.iter().next().unwrap()
        ),
        "克隆必须共享原记录段"
    );
    cloned.region_merge_records.last_mut().unwrap().record_id = 2;
    cloned.region_merge_records.push(record(3));
    assert_eq!(frame.region_merge_records.len(), 1);
    assert_eq!(frame.region_merge_records[0].record_id, 1);
    let restored = unfreeze_frame(&saved);
    assert_eq!(restored.region_merge_records.len(), 1);
    assert_eq!(restored.region_merge_records[0].record_id, 1);
    assert!(std::ptr::eq(
        frame.region_merge_records.iter().next().unwrap(),
        restored.region_merge_records.iter().next().unwrap()
    ));
}

#[test]
fn shared_history_fold_suffix_matches_vec_and_shares_read_payloads() {
    use crate::executor::path_cache::Record;
    use crate::executor::MergeHistory;
    let mut accumulated = MergeHistory::default();
    let mut continuation = MergeHistory::default();
    let mut expected = Vec::<RegionMergeRecord<B64>>::new();
    for round in 1..=32 {
        let mut new = record(round);
        new.single_arm_reads = vec![GuardedRegisterRead {
            register: test_name(round as u32),
            accessor: vec![crate::smt::Accessor::Field(test_name(99))],
            value: Val::Vector(vec![Val::I64(round as i64); 128]),
            guard: smtlib::Exp::Var(new.condition),
        }]
        .into();
        continuation.push(new);
        let mut next = continuation.clone();
        next.edit_suffix(0, |records| {
            for record in records {
                record.record_id += round * 1000;
                record.parent_record = Some(round * 100000);
                record.arm = "else";
            }
        });
        // 旧 Vec 折叠的参考：保留每个出现、按顺序复制后缀，再只改位置元数据。
        let mut suffix = continuation.iter().cloned().collect::<Vec<_>>();
        for record in &mut suffix {
            record.record_id += round * 1000;
            record.parent_record = Some(round * 100000);
            record.arm = "else";
        }
        expected.extend(suffix);
        accumulated.append_suffix(&next, 0);
        assert_eq!(accumulated.len(), round * (round + 1) / 2);
        let actual = accumulated.iter().cloned().map(Record::from).collect::<Vec<_>>();
        let reference = expected.iter().cloned().map(Record::from).collect::<Vec<_>>();
        assert_eq!(actual, reference, "第 {round} 轮全部字段与顺序必须相同");
        let unique =
            accumulated.iter().map(|r| r.single_arm_reads.as_ptr() as usize).collect::<std::collections::HashSet<_>>();
        assert_eq!(unique.len(), round, "二次逻辑记录只持有线性数量的读取载荷");
    }
}

#[test]
fn shared_history_clone_cost_is_independent_of_prefix_length() {
    use crate::executor::MergeHistory;
    assert_eq!(std::mem::size_of::<MergeHistory<B64>>(), std::mem::size_of::<Arc<()>>());
    let mut history = MergeHistory::default();
    for id in 0..2048 {
        history.push(record(id));
        let copy = history.clone();
        assert!(std::ptr::eq(history.iter().next().unwrap(), copy.iter().next().unwrap()));
    }
    let copy = history.clone();
    history.edit_suffix(0, |_| ());
    assert!(std::ptr::eq(history.iter().next().unwrap(), copy.iter().next().unwrap()));
    let tail = history.len() - 1;
    history.edit_suffix(tail, |records| records[0].record_id = 99999);
    assert!(std::ptr::eq(history.iter().next().unwrap(), copy.iter().next().unwrap()), "修改后缀不得复制前缀");
    assert_eq!(copy.iter().last().unwrap().record_id, 2047);
    assert_eq!(history.iter().last().unwrap().record_id, 99999);
    // 迭代视图和连续消费视图必须逐项相同，空区间不得保留记录。
    assert_eq!(
        history.iter().map(|r| r.record_id).collect::<Vec<_>>(),
        history[..].iter().map(|r| r.record_id).collect::<Vec<_>>()
    );
    let mut empty = MergeHistory::default();
    empty.append_suffix(&copy, copy.len());
    assert!(empty.is_empty());
}

#[test]
fn shared_history_sparse_updates_keep_linear_metadata_capacity() {
    let mut history = crate::executor::MergeHistory::default();
    for id in 0..64 {
        history.push(record(id));
        history.edit_suffix(0, |records| records.last_mut().unwrap().arm = "then");
    }
    assert!(
        history.retained_record_slots() <= 64 * 4,
        "稀疏修改不得为单条新记录保留整段临时 Vec 的容量：{}",
        history.retained_record_slots()
    );
}

#[test]
fn shared_history_terminal_snapshots_do_not_flatten_or_copy_records() {
    let mut frame = make_frame(vec![Instr::End]);
    let mut saved = Vec::new();
    for id in 0..128 {
        frame.region_merge_records.push(record(id));
        saved.push(frame.region_merge_records().clone());
    }
    for (index, history) in saved.iter().enumerate() {
        assert_eq!(history.len(), index + 1);
        assert_eq!(history.iter().last().unwrap().record_id, index);
        assert!(
            std::ptr::eq(history.iter().next().unwrap(), saved.last().unwrap().iter().next().unwrap()),
            "终态必须保留同一历史段"
        );
    }
    assert!(saved.last().unwrap().retained_record_slots() <= 128 * 4, "终态保留不得隐式建立逐路径连续副本");
}
