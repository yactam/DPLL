import sys
from pycosat import solve

# Read the CNF formula from a file
def read_cnf_file(file_path):
    cnf = []
    with open(file_path, 'r') as file:
        for line in file:
            if line.startswith('c') or line.startswith('p'):
                continue
            clause = [int(x) for x in line.split() if x != '0']
            cnf.append(clause)
    return cnf

# Read the interpretation from a file
def read_interpretation_file(file_path):
    with open(file_path, 'r') as file:
        next(file)
        interpretation = [int(x) for x in file.read().split()]
    return interpretation

# Check if an interpretation satisfies a CNF formula
def is_satisfying(cnf, interpretation):
    for clause in cnf:
        satisfied = False
        for literal in clause:
            if literal in interpretation:
                satisfied = True
                break
        if not satisfied:
            return False
    return True

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python check_satisfiability.py <cnf_file> <interpretation_file>")
        sys.exit(1)

    cnf_file = sys.argv[1]
    interpretation_file = sys.argv[2]

    cnf = read_cnf_file(cnf_file)
    interpretation = read_interpretation_file(interpretation_file)

    if is_satisfying(cnf, interpretation):
        print("The interpretation satisfies the CNF formula.")
    else:
        print("The interpretation does not satisfy the CNF formula.")

