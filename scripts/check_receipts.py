#!/usr/bin/env python3
"""Print operational fields from guard receipts; retain full data at each locator."""
import argparse
import json
import os
from pathlib import Path


FIELDS = ('state', 'exit_code', 'owned_group_gone', 'compiler_count', 'compiler_launches',
          'peak_active_lean', 'peak_rss_bytes', 'peak_rss_mb', 'peak_memory_bytes',
          'duration_seconds')


def project(path: Path, root: Path):
    phase = path.relative_to(root).with_suffix('').as_posix() if path.is_relative_to(root) else path.stem
    summary = dict(phase=phase, receipt=str(path))
    try:
        data = json.loads(path.read_text())
    except (OSError, ValueError) as error:
        summary['failure_summary'] = str(error)[:300]
        return summary
    if not isinstance(data, dict) or not any(key in data for key in ('state', 'exit_code', 'guard_failure')):
        return None  # Scope plans and other JSON are not process receipts.
    summary.update((key, data[key]) for key in FIELDS if key in data)
    if data.get('guard_failure'):
        summary['failure_summary'] = str(data['guard_failure'])[:300]
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('--limit', type=int, default=20,
                        help='maximum individual receipt records to print (default: 20)')
    args = parser.parse_args()
    if args.limit < 0:
        parser.error('--limit must be nonnegative')
    root = args.root.resolve()
    paths = sorted(root.rglob('*.json'))
    cache = Path(str(root) + '-cache.json')
    if cache.is_file():
        paths.append(cache)
    records = []
    for path in paths:
        if (summary := project(path, root)) is not None:
            records.append(summary)

    def failure(record):
        code = record.get('exit_code')
        return bool(record.get('failure_summary')) or record.get('owned_group_gone') is False or (
            isinstance(code, (int, float)) and code != 0) or record.get('state') in {'failed', 'error'}

    records.sort(key=lambda record: not failure(record))  # Stable within each priority.
    selected = records[:args.limit]
    locator = {'directory': str(root)}
    if cache.is_file():
        locator['cache_receipt'] = str(cache)
    run_id, attempt = os.environ.get('GITHUB_RUN_ID'), os.environ.get('GITHUB_RUN_ATTEMPT')
    if run_id and attempt:
        locator['artifact_name'] = f'quillen-check-receipts-{run_id}-{attempt}'
        repository = os.environ.get('GITHUB_REPOSITORY')
        server = os.environ.get('GITHUB_SERVER_URL')
        if repository and server:
            locator['artifact_run_url'] = f'{server}/{repository}/actions/runs/{run_id}#artifacts'
    print(json.dumps({'receipt_counts': {'total': len(records), 'emitted': len(selected),
                                         'omitted': len(records) - len(selected)},
                      'full_receipts': locator}, sort_keys=True))
    for record in selected:
        print(json.dumps(record, sort_keys=True))


if __name__ == '__main__':
    main()
