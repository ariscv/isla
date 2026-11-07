import json,os,signal,subprocess,time,sys,datetime
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]; BASE=ROOT/'output/sym-prestate'; SOURCE=ROOT.parent/'replay-p0/output/ecfg4b'
name=sys.argv[1]; checking='--check' in sys.argv
out=BASE/(name+('-check' if checking else ''));out.mkdir(exist_ok=False)
old=json.loads((SOURCE/'sv39-load/done.json').read_text());cmd=old['command'].copy()
cmd[cmd.index('-T')+1]='64'
config=BASE/(name+'.toml')
if not config.exists():config.write_text((SOURCE/'config-xs.toml').read_text())
cmd[cmd.index('-C')+1]=str(config)
if name!='E0':
 cmd[cmd.index('-A')+1]=str(BASE/'rv64d-us.ir')
 i=cmd.index('cur_privilege=Supervisor'); del cmd[i-1:i+1]
if name in ('E2','E3'):
 i=cmd.index('mstatus={bits=0x0000000a00040000}');del cmd[i-1:i+1]
cmd[cmd.index('--execution-limits-config')+1]=str(SOURCE/'enumeration.toml')
if checking:
 i=cmd.index('--execution-limits-config');del cmd[i:i+2]
 cmd[-3:-3]=['--check-samples',str(BASE/name/'samples.jsonl'),'--check-samples-report',str(out/'check.json')]
env=os.environ.copy();env.update(TMPDIR=str(BASE),XDG_CACHE_HOME=str(BASE/'cache'),PYTHONDONTWRITEBYTECODE='1',ISLA_STATS='1')
env.pop('LD_PRELOAD',None)
if checking:
 (out/'badread').mkdir()
 env.update(LD_PRELOAD=str(SOURCE/'observe.so'),BADREAD_DUMP=str(out/'badread'))
if not checking:env['ISLA_EXPORT_SAMPLES']=str(out/'samples.jsonl')
record=dict(command=cmd,started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),environment={k:env[k] for k in ('TMPDIR','XDG_CACHE_HOME','ISLA_STATS')})
(out/'running.json').write_text(json.dumps(record,indent=2))
t=time.monotonic()
with (out/'stdout.txt').open('w') as stdout,(out/'stderr.txt').open('w') as stderr:
 p=subprocess.Popen(cmd,cwd=out,env=env,stdout=stdout,stderr=stderr,start_new_session=True)
 try:record.update(returncode=p.wait(timeout=900),timed_out=False)
 except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);record.update(returncode=p.wait(),timed_out=True)
record['seconds']=time.monotonic()-t
(out/'done.json').write_text(json.dumps(record,indent=2))
print(json.dumps(record))
