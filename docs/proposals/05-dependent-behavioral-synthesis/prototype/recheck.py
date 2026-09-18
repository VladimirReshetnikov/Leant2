#!/usr/bin/env python3
"""Recheck either supplied Lean file through AXLE. Python 3.9+, standard library.

Network access is required. The file's actual imports are retained. A service
success is insufficient: errors, source rewriting, and sorryAx are rejected.
Raw response JSON is saved for independent examination, even after rejection.
An axiom inventory still needs interpretation under the user's chosen policy.
"""
import argparse
import json
from pathlib import Path
import sys
import urllib.error
import urllib.request

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('source',type=Path)
    p.add_argument('--environment',default='lean-4.34.0')
    p.add_argument('--timeout',type=int,default=60)
    p.add_argument('--receipt',type=Path)
    a=p.parse_args()
    if a.timeout <= 0:
        p.error('--timeout must be positive')
    source=a.source.read_text(encoding='utf-8')
    payload=dict(content=source, environment=a.environment, ignore_imports=False,
                 theorems_only=False, timeout_seconds=a.timeout)
    request=urllib.request.Request('https://axle.axiommath.ai/api/v1/check',
        data=json.dumps(payload,ensure_ascii=False).encode('utf-8'),
        headers={'Content-Type':'application/json'},method='POST')
    try:
        with urllib.request.urlopen(request,timeout=a.timeout+30) as r:
            response=json.load(r)
    except (urllib.error.URLError,TimeoutError,json.JSONDecodeError) as error:
        raise SystemExit('Check service did not return a usable response: '+str(error))
    destination=a.receipt or a.source.with_suffix('.remote.json')
    destination.write_text(json.dumps(response,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    reasons=[]
    if response.get('okay') is not True:
        reasons.append('Service did not report successful compilation.')
    if response.get('failed_declarations'):
        reasons.append('Failed declarations were reported.')
    for field in ('lean_messages','tool_messages'):
        if response.get(field,{}).get('errors'):
            reasons.append(field+' contains errors.')
    echo=response.get('content')
    if echo not in (source,source+'\n'):
        reasons.append('Processed source differs beyond the observed appended terminal LF.')
    infos='\n'.join(response.get('lean_messages',{}).get('infos',[]))
    if 'sorryAx' in infos:
        reasons.append('An audited declaration depends on sorryAx.')
    names=[]
    for line in source.splitlines():
        if line.startswith('#print axioms '):
            names.append(line.removeprefix('#print axioms ').strip())
    for name in names:
        if not any(("."+name+"'") in text or ("'"+name+"'") in text
                   for text in response.get('lean_messages',{}).get('infos',[])):
            reasons.append('Missing requested axiom report: '+name)
    print('Receipt:',destination)
    print(infos)
    if reasons:
        raise SystemExit('\n'.join(reasons))
    print('Compilation and source/diagnostic checks passed; inspect the axiom inventory above.')

if __name__=='__main__':
    main()
