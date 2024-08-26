from smtlib import SupportedSolvers
from test import Tests
import sys
from hackdel import BvBench
import json


suite = Tests
if len(sys.argv) > 1 and sys.argv[1] == '-h':
    suite = BvBench

csv = {}
all_tests = list(filter(lambda i: i[0:5] == 'test_', dir(suite)))
all_test_names = []
for solver in SupportedSolvers:
    csv[solver.value] = {}
    for test in all_tests:
        name = test.split('test_')[1]
        if name not in all_test_names:
            all_test_names.append(name)
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

filename = 'stats.csv' if suite == Tests else 'hack_stats.csv'
with open(filename, 'w') as resFile:
    print('Solver;' + ';'.join(all_test_names), file=resFile)
    for solver in SupportedSolvers:
        d = csv[solver.value]
        print(f'{solver.value};' + ';'.join(d[test] for test in all_test_names), file=resFile)


