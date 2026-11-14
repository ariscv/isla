use super::*;

#[test]
fn 深度优先调度保留全部布尔路径并限制驻留队列() {
    const DEPTH: usize = 6;
    for workers in [1, 4] {
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut instructions = Vec::new();
        let conditions: Vec<_> = (0..DEPTH)
            .map(|index| (test_name(9000 + index as u32), solver.declare_const(smtlib::Ty::Bool, info())))
            .collect();
        for (name, _) in &conditions {
            let pc = instructions.len();
            instructions.push(Instr::Jump(Exp::Id(*name), pc + 2, info()));
            instructions.push(Instr::Goto(pc + 3));
            instructions.push(Instr::Goto(pc + 3));
        }
        instructions.push(Instr::End);
        let mut frame = make_frame(instructions);
        for (name, condition) in &conditions {
            frame.vars_mut().insert(*name, UVal::Init(Val::Symbolic(*condition)));
        }
        let state = TaskState::new();
        let output = Arc::new(Mutex::new(Vec::new()));
        let task = frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver));
        start_multi(workers, None, vec![task], &shared, output.clone(), &|_, _, result, _, mut solver, output| {
            assert!(matches!(result, Ok((Run::Finished(_), _))), "每条布尔路径必须正常结束");
            assert!(solver.check_sat(info()).is_sat().unwrap());
            let mut model = crate::smt::Model::new(&solver);
            let mut assignment = 0usize;
            for (index, (_, condition)) in conditions.iter().enumerate() {
                let smtlib::Exp::Bool(value) = model.get_var(*condition).unwrap().unwrap_exp() else {
                    panic!("布尔分支必须由本条完整路径唯一确定")
                };
                assignment |= usize::from(value) << index;
            }
            output.lock().unwrap().push(assignment);
        });
        let mut actual = output.lock().unwrap().clone();
        actual.sort_unstable();
        assert_eq!(actual, (0..1 << DEPTH).collect::<Vec<_>>(), "不得遗漏或重复任何可达赋值");
        let snapshot = shared.execution_stats.merge_json();
        let runtime = &snapshot["runtime"];
        assert_eq!(runtime["submitted_tasks"], 1 << DEPTH);
        assert_eq!(runtime["completed_tasks"], 1 << DEPTH);
        assert_eq!(runtime["queued_tasks"], 0);
        let peak = runtime["queued_tasks_peak"].as_u64().unwrap();
        eprintln!("调度驻留：workers={workers}，全部路径={}，队列峰值={peak}", actual.len());
        if workers == 1 {
            assert!(peak <= DEPTH as u64, "单工作线程深度优先仅需保留各层兄弟任务：{peak}");
        }
    }
}
