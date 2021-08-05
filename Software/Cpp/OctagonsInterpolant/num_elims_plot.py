import numpy as np
import matplotlib.pyplot as plt
plt.style.use('seaborn-whitegrid')

def read_data(file_name):
    z3_data = np.arange(0)
    octi_data = np.arange(0)
    _file = open(file_name, "r")
    new_entry = False
    last_entry = ["last", "last"]
    for line in _file.readlines():
        _line = line.split()
        if(("interpolants" in _line[0] and new_entry) or ("rm" in _line[0])):
            new_entry = False
            if("rm" in _line[0]):
                octi_data = np.append(int(last_entry[0]), octi_data)
            else:
                octi_data = np.append(int(last_entry[1]), octi_data)
        if("arith-add-rows" in _line[0]):
            new_entry = True
            z3_data = np.append(int(_line[1]), z3_data)
        if(new_entry):
            last_entry[1] = last_entry[0]
            last_entry[0] = _line[0]
    return (z3_data, octi_data)

if __name__ == "__main__":
    num_tests = 100
    num_constants = 10
    num_ineqs = 20
    num_vars_to_elim = 10

    z3_data, octi_data = read_data("./results/num_elims.txt")

    count_z3_more_adds = 0
    count_octi_more_adds = 0

    for i in range(len(z3_data)):
        if(z3_data[i] > octi_data[i]):
            count_z3_more_adds += 1
        if(z3_data[i] < octi_data[i]):
            count_octi_more_adds += 1

    print (count_z3_more_adds, count_octi_more_adds)

    fig, ax = plt.subplots()
    num_test_points = np.arange(0, len(z3_data))

    ax.plot(num_test_points, octi_data, marker='x', color='red', label='OCT Uniform Interpolator')
    ax.plot(num_test_points, z3_data, marker='+', color='green', label='iZ3')

    ax.set_xlabel('# of random cases used')
    ax.set_ylabel('Uppder Bound on Number of Additions')
    ax.set_title('Upper bound on the number of additions \n\
            Number of Constants: ' + str(num_constants) + ' Number of Inequalities: ' + str(num_ineqs))
    # ax.set_ylim(0, 70)
    legend = ax.legend(bbox_to_anchor=(1.05, 1), loc='upper left', borderaxespad=0.)
    plt.savefig("results/plots/octi_performance_add_ops_" 
            + str(num_constants) + "_" 
            + str(num_ineqs) + "_" 
            + str(num_tests) + ".png", dpi=400, bbox_inches='tight')
