"""Thin adapter of lean-pkg's unchanged build-history predicate plus exact source coverage."""
from pathlib import Path
import sys
from lake_hygiene import job_lines, restored_jobs

def main():
    log, *roots = sys.argv[1:]
    assert roots, "At least one module root is required"
    expected = set()
    for root in roots:
        base = Path(root.replace('.', '/'))
        source = base.with_suffix('.lean')
        if source.is_file(): expected.add(root)
        if base.is_dir():
            expected.update(str(p.with_suffix('')).replace('/', '.') for p in base.rglob('*.lean'))
    assert expected, "No expected source modules"
    jobs = job_lines(Path(log).read_text())
    def owned(name): return any(name == r or name.startswith(r + '.') for r in roots)
    restored = [(v, n) for v, n in restored_jobs(jobs) if owned(n)]
    missing = sorted(expected - {n for v, n in jobs if v == 'Built'})
    if restored or missing:
        print('fresh build refused: restored=', restored, 'missing Built=', missing, file=sys.stderr)
        return 1
    print(f'fresh build check: PASS ({len(expected)} exact source modules built; subsequent same-module replay only)')
    return 0

if __name__ == '__main__': raise SystemExit(main())
