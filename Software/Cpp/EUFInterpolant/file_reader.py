import numpy as np
import matplotlib.pyplot as plt

num_tests = 10000

iz3_file = open("iz3_results.txt", "r")
steps = np.arange(0, num_tests)
data_iz3 = np.zeros(num_tests, dtype=float)
current_entry = 0

for line in iz3_file.readlines():
    line_ = line.split()
    if(len(line_) == 2):
        if(line_[0] == 'user'):
            m, s_ = line_[1].split('m')
            s = s_[:-1]
            data_iz3[current_entry] = 60*m + s
        if(line_[0] == 'test:'):
            current_entry = int(line_[1])
iz3_file.close()

fig, ax = plt.subplots()
ax.plot(steps, data_iz3)

ax.set_xlabel('# Test')
ax.set_ylabel('Time in seconds')
ax.set_title('Performance comparison of interpolant generation algorithms for EUF')

legend = ax.legend(loc='upper center', shadow=True, fontsize='x-large')
legend.get_frame().set_facecolor('C0')

plt.show()
