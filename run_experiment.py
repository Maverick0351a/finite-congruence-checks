"""Reproduce the bounded search and both independent checks, using only stdlib."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

import verify_witness


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8', newline='\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=Path('runs/reproduction'),
                        help='New or empty output directory; default runs/reproduction')
    args = parser.parse_args()
    output = args.out.resolve()
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        parser.error('output must be a new or empty directory; choose another --out path')
    output.mkdir(parents=True, exist_ok=True)
    root = Path(__file__).resolve().parent
    started = time.perf_counter()
    evidence = dict(started_utc=datetime.now(timezone.utc).isoformat(), python=sys.version,
                    platform=platform.platform(), commands=[], passed=False,
                    path_convention='Machine-specific paths in commands/logs are replaced by {python}, {out}, {repo}.',
                    code_sha256={path.name: digest(path) for path in sorted(root.glob('*.py'))})

    def portable(value):
        for path, placeholder in ((sys.executable, '{python}'), (str(output), '{out}'), (str(root), '{repo}')):
            value = value.replace(path.replace('\\', '\\\\'), placeholder)
            value = value.replace(path, placeholder).replace(path.replace('\\', '/'), placeholder)
        return value

    def run(script_args, label):
        command = [sys.executable, *script_args]
        then = time.perf_counter()
        process = subprocess.run(command, cwd=root, capture_output=True, text=True, encoding='utf-8')
        (output / f'{label}.log').write_text(portable(process.stdout + process.stderr), encoding='utf-8', newline='\n')
        evidence['commands'].append(dict(argv=[portable(arg) for arg in command], exit_code=process.returncode,
                                         seconds=round(time.perf_counter() - then, 6), log=f'{label}.log'))
        if process.returncode:
            raise RuntimeError(f'{label} failed; see {output / (label + ".log")}')
        print(f'{label}: passed', flush=True)

    try:
        run(['-m', 'unittest', 'discover', '-s', str(root), '-p', 'test_*.py', '-v'], 'unit-tests')
        run([str(root / 'search.py'), '--max-vertices', '4', '--out', str(output)], 'search')
        record = json.loads((output / 'search-results.json').read_text(encoding='utf-8'))
        certificates = []
        for entry in record['certificates']:
            path = output / entry['path']
            if path.parent.resolve() != output or digest(path) != entry['sha256']:
                raise ValueError('certificate path or SHA-256 mismatch')
            certificates.append(path)
            run([str(root / 'verify_witness.py'), str(path), '--output',
                 str(output / (path.stem + '.verification.json'))], path.stem + '-verification')
        if len(certificates) != 7:
            raise ValueError('the fixed eight-lattice experiment must produce seven certificates')
        print('independent exhaustive replay: running', flush=True)
        replay = verify_witness.verify_search_record(record)
        replay['search_record_file_sha256'] = digest(output / 'search-results.json')
        save(output / 'independent-review-results.json', replay)
        if not replay['all_expected_outcomes']:
            raise RuntimeError('independent full-search replay disagrees with search')
        print('independent exhaustive replay: passed', flush=True)
        run([str(root / 'verify_algebra.py'), *map(str, certificates), '--out',
             str(output / 'verified-algebras.json')], 'algebra-verification')
        run([str(root / 'minimize_operations.py'), *map(str, certificates), '--out',
             str(output / 'minimized-algebras.json')], 'operation-minimization')
        evidence['passed'] = True
    except (OSError, ValueError, KeyError, RuntimeError) as exc:
        evidence['error'] = portable(str(exc))
        print(str(exc), file=sys.stderr)
    finally:
        evidence['finished_utc'] = datetime.now(timezone.utc).isoformat()
        evidence['seconds'] = round(time.perf_counter() - started, 6)
        evidence['output_sha256'] = {p.name: digest(p) for p in sorted(output.iterdir())
                                     if p.is_file() and p.name != 'run-evidence.json'}
        save(output / 'run-evidence.json', evidence)
    print(f'passed={evidence["passed"]}; output={output}', flush=True)
    return 0 if evidence['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
