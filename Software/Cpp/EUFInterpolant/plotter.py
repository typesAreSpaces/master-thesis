import numpy as np
import matplotlib.pyplot as plt
plt.style.use('seaborn-whitegrid')

def parse_info(file_name, _data, num_tests):
    _file = open(file_name, "r")
    current_entry = 0

    for line in _file.readlines():
        if(current_entry >= num_tests):
            break
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

def parse_info_chunks(file_names, _data, num_test):
    for file_name in file_names:
        parse_info(file_name, _data, num_tests)
    return _data


num_tests = 10000
# num_tests = 6000

steps = np.arange(0, num_tests)
data_iz3 = parse_info("results/iz3_results.txt", 
        np.zeros(num_tests, dtype=float), num_tests)
data_mathsat = parse_info("results/mathsat_results.txt", 
        np.zeros(num_tests, dtype=float), num_tests)
data_eufi = parse_info_chunks([
    "results/eufi_results_0_upto_6000.txt", 
    "results/eufi_results_1_upto_6000.txt", 
    "results/eufi_results_2_upto_6000.txt",  
    "results/eufi_results_3_upto_6000.txt", 
    "results/eufi_results_0.txt",
    "results/eufi_results_1.txt",
    "results/eufi_results_2.txt",
    "results/eufi_results_3.txt",
    "results/eufi_results_4.txt",
    "results/eufi_results_5.txt",
    "results/eufi_results_6.txt",
    "results/eufi_results_7.txt",
    "results/eufi_results_8.txt",
    "results/eufi_results_9.txt",
    "results/eufi_results_10.txt",
    "results/eufi_results_11.txt",
    "results/eufi_results_12.txt",
    "results/eufi_results_13.txt",
    "results/eufi_results_14.txt",
    "results/eufi_results_15.txt",
    "results/eufi_results_16.txt",
    "results/eufi_results_17.txt",
    ],np.zeros(num_tests, dtype=float), num_tests)

fig, ax = plt.subplots()
ax.scatter(steps, data_eufi, marker='x', color='red', label='EUF Uniform Interpolator')
ax.scatter(steps, data_iz3, marker='+', color='green', label='iZ3')
ax.scatter(steps, data_mathsat, marker='o', color='blue', label='Mathsat')

ax.set_xlabel('# Test')
ax.set_ylabel('Time in seconds')
ax.set_title('Performance comparison of interpolant generation algorithms for EUF using parametrized problem from section 3.2.2.')

legend = ax.legend(loc='upper left', shadow=True, fontsize='x-large')

plt.savefig("results/eufi_performance_graph.png")
