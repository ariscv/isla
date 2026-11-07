from pathlib import Path
import difflib,json
ROOT=Path(__file__).resolve().parents[2];base=ROOT/'output/sym-prestate';source=ROOT.parent/'replay-p0/output/ecfg4b'
original=(source/'rv64d.ir').read_text()
# 包装入口使原函数体及其所有数字跳转位置逐字保留。
oldval='val zexecute : (%union zinstruction) ->  %union zExecutionResult'
newval=oldval+'\n\nval zsym_prestate_execute_body : (%union zinstruction) ->  %union zExecutionResult\n\nval zsym_prestate_assume = "assume" : (%bool) -> %unit'
oldfn='fn zexecute(zmergez3var) {'
wrapper='''fn zexecute(zmergez3var) {
  zsym_prestate_constraint : %unit;
  zsym_prestate_constraint = zsym_prestate_assume(@or(@eq(zcur_privilege, zUser), @eq(zcur_privilege, zSupervisor)));
  return = zsym_prestate_execute_body(zmergez3var);
  end;
}

fn zsym_prestate_execute_body(zmergez3var) {'''
assert original.count(oldval)==original.count(oldfn)==1
modified=original.replace(oldval,newval).replace(oldfn,wrapper)
assert modified.replace(newval,oldval).replace(wrapper,oldfn)==original
(base/'rv64d-us.ir').write_text(modified)
(base/'rv64d-us.diff').write_text(''.join(difflib.unified_diff(original.splitlines(True),modified.splitlines(True),fromfile='ecfg4b/rv64d.ir',tofile='sym-prestate/rv64d-us.ir')))
config=(source/'config-xs.toml').read_text()
for name,free in [('E0',0),('E1',0),('E2',(1<<18)|(1<<19)),('E3',(1<<18)|(1<<19)|(1<<17)|(1<<11))]:
 text=config
 if name!='E0':text=text.replace('[registers.defaults]','[registers.defaults]\ncur_privilege = \"Supervisor\"')
 if free:
  text=text.replace('mstatus = "{ bits = 0x0000000000000600 }"\n','')
  text+=f'\n[symbolic_registers.mstatus]\npin_mask = "0x{((1<<64)-1)^free:016x}"\npin_value = "0x{0xa00040000 & ~free:016x}"\n'
 (base/(name+'.toml')).write_text(text)
(base/'ir-source.json').write_text(json.dumps(dict(source='../replay-p0/output/ecfg4b/rv64d.ir',copy='output/sym-prestate/rv64d-us.ir',original_function_line=original[:original.index(oldfn)].count('\n')+1,body_unchanged=True,assumption='cur_privilege == User OR cur_privilege == Supervisor',proof='删除新增声明和包装函数并恢复原函数名后，全文与原 IR 逐字一致；未计算哈希。'),ensure_ascii=False,indent=2))
