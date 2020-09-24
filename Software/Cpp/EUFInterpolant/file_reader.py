import numpy as np
import matplotlib.pyplot as plt

def parse_info(file_name, num_tests):
    _file = open(file_name, "r")
    _data = np.zeros(num_tests, dtype=float)
    current_entry = 0

    for line in _file.readlines():
        _line = line.split()
        if(len(_line) == 2):
            if(_line[0] == 'user'):
                m , _s = _line[1].split('m')
                s = _s[:-1]
                _data[current_entry] = 60*float(m) + float(s)
            if(_line[0] == 'test:'):
                current_entry = int(_line[1])
    _file.close()
    return _data

num_tests = 10000

steps = np.arange(0, num_tests)
data_iz3 = parse_info("iz3_results.txt", num_tests)
data_mathsat = parse_info("mathsat_results.txt", num_tests)

fig, ax = plt.subplots()
ax.plot(steps, data_iz3    , 'r', label='iZ3')
ax.plot(steps, data_mathsat, 'g', label='Mathsat')

ax.set_xlabel('# Test')
ax.set_ylabel('Time in seconds')
ax.set_title('Performance comparison of interpolant generation algorithms for EUF')

legend = ax.legend(loc='upper left', shadow=True, fontsize='x-large')

plt.show()
