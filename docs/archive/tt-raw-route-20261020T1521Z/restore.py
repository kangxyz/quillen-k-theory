#!/usr/bin/env python3
"""Restore archived sources without overwriting any differing live file."""
import argparse, hashlib, json, shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('repository',type=Path);p.add_argument('--staging',action='store_true',help='Restore only the separate exact-duplicate tmp batch');args=p.parse_args()
a=Path(__file__).resolve().parent;r=args.repository.resolve();m=json.loads((a/'MANIFEST.json').read_text())
files=json.loads((a/'STAGING-MANIFEST.json').read_text())['files'] if args.staging else [x for x in m['files'] if x['action']=='move_after_verification']
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for x in files:
 s=a/x['archive_path'];d=r/x['path']
 if not s.is_file() or h(s)!=x['sha256']:raise SystemExit('Archive checksum mismatch: '+str(s))
 if d.exists() and h(d)!=x['sha256']:raise SystemExit('Refusing overwrite: '+str(d))
for x in files:
 s=a/x['archive_path'];d=r/x['path'];d.parent.mkdir(parents=True,exist_ok=True)
 if not d.exists():shutil.copy2(s,d)
print(f'Restored {len(files)} sources (staging mode: {args.staging}).')
if not args.staging:
 print('Run python3 scripts/generate_imports.py in the repository, then validate affected imports. Historical doc snapshots are preserved separately, not automatically overwritten.')
