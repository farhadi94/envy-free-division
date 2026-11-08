"""Bounded DAG scheduler used only by the staged frozen-closure auditor."""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

class BuildFailure(RuntimeError):
    pass

def run_dag(dependencies, jobs, build, record, abort=lambda: None):
    if not 1 <= jobs <= 4:
        raise ValueError('jobs must be between1 and4')
    deps = {name: set(ds) for name, ds in dependencies.items()}
    if any(not ds <= deps.keys() for ds in deps.values()):
        raise ValueError('Unknown local dependency')
    pending, completed, running = set(deps), set(), {}
    pool = ThreadPoolExecutor(max_workers=jobs)
    failure = None
    try:
        while pending or running:
            ready = sorted(n for n in pending if deps[n] <= completed)
            for name in ready[:jobs-len(running)]:
                pending.remove(name)
                running[pool.submit(build, name)] = name
            if not running:
                raise BuildFailure('Dependency cycle or unsatisfied dependency')
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in sorted(done, key=lambda f: running[f]):
                name = running.pop(future)
                try:
                    row = future.result()
                except BaseException as exc:
                    row = {'module': name, 'exit_code': -1, 'error': repr(exc)}
                record(name, row)
                if row['exit_code'] != 0:
                    failure = BuildFailure('Compilation failed: ' + name)
                else:
                    completed.add(name)
            if failure is not None:
                raise failure
    except BaseException:
        abort()
        # Drain already-started jobs and record their actual exits. Never launch
        # descendants or additional independent jobs after detecting failure.
        for future, name in sorted(running.items(), key=lambda item: item[1]):
            if future.cancel():
                record(name, {'module': name, 'exit_code': -1, 'cancelled': True})
            else:
                try:
                    record(name, future.result())
                except BaseException as exc:
                    record(name, {'module': name, 'exit_code': -1, 'error': repr(exc)})
        raise
    finally:
        pool.shutdown(wait=True, cancel_futures=True)
    return completed
