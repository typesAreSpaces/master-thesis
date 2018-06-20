import random

nVar = 100
result = "["

for i in range(1000):
    result = result + "Ineq (Expr (" + str(random.randint(-1, 1)) + ") \"x" + str(random.randint(0, nVar)) + "\") (Expr (" + str(random.randint(-1, 1)) + ") \"x" + str(random.randint(0, nVar)) + "\") (" + str(random.randint(-100, 100)) + "),"

result = result + "Ineq (Expr (" + str(random.randint(-1, 1)) + ") \"x" + str(random.randint(0, nVar)) + "\") (Expr (" + str(random.randint(-1, 1)) + ") \"x" + str(random.randint(0, nVar)) + "\") (" + str(random.randint(-100, 100)) + ")]"

print result
