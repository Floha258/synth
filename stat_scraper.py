from smtlib import SupportedSolvers
from test import Tests
import json

csv = {}
all_tests = list(filter(lambda i: i[0:5] == 'test_', dir(Tests)))
all_test_names = set()
for solver in SupportedSolvers:
    csv[solver.value] = {}
    for test in all_tests:
        name = test.split('test_')[1]
        all_test_names.add(name)
        try:
            with open(f'stats/{name}_{solver.value}.json') as statsFile:
                stats = json.load(statsFile)
                if not type(stats) is list and stats['error']:
                    csv[solver.value][name] = stats['error']
                else:
                    total = sum(s['time'] for s in stats)
                    csv[solver.value][name] = f'{total / 1e9:.3f}s'
        except:
            csv[solver.value][name] = 'DNR'

with open('stats.csv', 'w') as resFile:
    print('Solver;' + ';'.join(all_test_names), file=resFile)
    for solver in SupportedSolvers:
        d = csv[solver.value]
        print(f'{solver.value};' + ';'.join(d[test] for test in all_test_names), file=resFile)


