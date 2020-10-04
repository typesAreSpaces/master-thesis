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


num_tests = 9

steps = np.arange(0, num_tests)
data_iz3 = parse_info("results/iz3_results_small.txt", 
        np.zeros(num_tests, dtype=float), num_tests)
data_mathsat = parse_info("results/mathsat_results_small.txt", 
        np.zeros(num_tests, dtype=float), num_tests)
data_octi = parse_info_chunks([
    "results/thci_results_0_small.txt",
    "results/thci_results_1_small.txt",
    "results/thci_results_2_small.txt",
    ],np.zeros(num_tests, dtype=float), num_tests)

fig, ax = plt.subplots()
ax.scatter(steps, data_octi, marker='x', color='red', label='EUF + OCT Interpolator')
ax.scatter(steps, data_mathsat, marker='o', color='blue', label='Mathsat')
ax.scatter(steps, data_iz3, marker='+', color='green', label='iZ3')

ax.set_xlabel('Parameter n')
ax.set_ylabel('Time in seconds')
# ax.set_title('Performance comparison of interpolant generation algorithms for EUF using parametrized problem from section 3.2.2.')

legend = ax.legend(loc='upper left', shadow=True, fontsize='x-large')

plt.savefig("results/thci_performance_graph_small.png")

print("data iZ3")
print(data_iz3)
print("data Mathsat")
print(data_mathsat)
print("data EUF + OCT")
print(data_octi)

# fit_iz3_deg_2 = np.polyfit(steps, data_iz3, 2)
# fit_mathsat_deg_2 = np.polyfit(steps, data_mathsat, 2)
# fit_octi_deg_2 = np.polyfit(steps, data_octi, 2)
# fit_iz3_deg_1 = np.polyfit(steps, data_iz3, 1)
# fit_mathsat_deg_1 = np.polyfit(steps, data_mathsat, 1)
# fit_octi_deg_1 = np.polyfit(steps, data_octi, 1)

# print("Fit iz3 deg 2:")
# print(fit_iz3_deg_2)
# print("Error:")
# print(np.sum(np.polyval(fit_iz3_deg_2, steps)- data_iz3)**2)
# print("Fit iz3 deg 1:")
# print(fit_iz3_deg_1)
# print("Error:")
# print(np.sum(np.polyval(fit_iz3_deg_1, steps)- data_iz3)**2)
# print("Fit mathsat deg 2:")
# print(fit_mathsat_deg_2)
# print("Error:")
# print(np.sum(np.polyval(fit_mathsat_deg_2, steps)- data_mathsat)**2)
# print("Fit mathsat deg 1:")
# print(fit_mathsat_deg_1)
# print("Error:")
# print(np.sum(np.polyval(fit_mathsat_deg_1, steps)- data_mathsat)**2)
# print("Fit octi deg 2:")
# print(fit_octi_deg_2)
# print("Error:")
# print(np.sum(np.polyval(fit_octi_deg_2, steps)- data_octi)**2)
# print("Fit octi deg 1:")
# print(fit_octi_deg_1)
# print("Error:")
# print(np.sum(np.polyval(fit_octi_deg_1, steps)- data_octi)**2)
