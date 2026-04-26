#!/usr/bin/python3
# alc25 - 6 - project2 
# DO NOT remove or edit the lines above. Thank you.

# PROBLEM VARIABLES
# D - Number of days
# S - Number of shifts in each day. E.g. if S = 4 then there are 4 shifts each day, each one during 6 hours
# R(s, d) - Minimum number of nurses necessary to work in shift s (1 <= s <= S) of day d (1 <= d <= D)
# N/Nk - Set of all nurses / kth nurse
# M - Set of nurses that have managerial qualification (N contains M)
# L(k)min/L(k)max - Minimum/Maximum number of shifts nurse k can do each day
# Hk - Maximum number of shifts that each nurse can do during the D days
# P(k,s,d) - cost of assigning nurse k to shift s in day d

# RESTRICTIONS
# [X] Each shift has a minimum number of necessary nurses to be present
# [X] Work schedule of a nurse in each day must be continuous, that is, there cannot exist a pause between two shifts in a single day
# [X] Each nurse has a minimum and maximum number of shifts it can do each day
# [X] Each nurse can only do Hk shifts throughout the D days
# [X] Each shift must have a nurse with managerial qualifications
# [X] A nurse is never assigned to a shift in which she said she was unavailable
# [X] The cost of assignment is minimized

from sys import stdin
from z3 import Solver, Optimize, PbLe, PbGe
from z3 import Bool, sat, And, Not, Implies, Or, Sum, If, Int

# Reads the problem specification from the standard input
def bool_load_input():
    input = {"nurses_managerial": [], "min_nurses": [], "nurse_shifts": [], "costs": [], "vars": []}

    input["days"], input["shifts"] = map(int, stdin.readline().split())

    for _ in range(input["days"]):
        input["min_nurses"].append([int(n) for n in stdin.readline().split()])
    
    input["nurses"] = int(stdin.readline().split()[0])

    input["vars"] = [[[Bool(str(d*input["shifts"]*input["nurses"] + s*input["nurses"] + n + 1)) for n in range(input["nurses"])] for s in range(input["shifts"])] for d in range(input["days"])]

    for _ in range(input["nurses"]):
        line = stdin.readline().split()
        input["nurses_managerial"].append(1 if line[0] == "Y" else 0)
        input["nurse_shifts"].append((int(line[1]), int(line[2]), int(line[3])))
    
    for _ in range(input["days"]):
        input["costs"].append([[int(c) for c in stdin.readline().split()] for _ in range(input["shifts"])])
    
    return input

# Each variable x_k,s,d tells us if nurse k is assigned to shift s in day d

# Negate shifts that are impossible for a nurse to work on due to the L_min restriction
def precompute(input):
    shifts = input["shifts"]
    for d in range(input["days"]):
        for n in range(input["nurses"]):
            p1 = 0
            
            while p1 < shifts:
                while p1 < shifts and input["costs"][d][p1][n] == -1:
                    p1 += 1

                p2 = p1
                while p2 < shifts and input["costs"][d][p2][n] != -1:
                    p2 += 1
                
                if p2 - p1 < input["nurse_shifts"][n][0]:
                    while p1 != p2:
                        input["costs"][d][p1][n] = -1
                        p1 += 1
                    p1 += 1
                else:
                    p1 = p2 + 1

# Each shift has a minimum number of necessary nurses to be present
def bool_encode_min_nurses(input, enc):
    for d in range(input["days"]):
        for s in range(input["shifts"]):
            # Get list of available nurses
            available = []

            for n in range(input["nurses"]):
                if input["costs"][d][s][n] != -1:
                    available.append(input["vars"][d][s][n])
            
            # Create cardinality constraint
            enc.add(PbGe([(v, 1) for v in available], input["min_nurses"][d][s]))
    return enc

# Work schedule of a nurse in each day must be continuous, that is, there cannot exist a pause between two shifts in a single day
def bool_encode_continous_shifts(input, enc):
    for d in range(input["days"]):
        for n in range(input["nurses"]):
            for s1 in range(0, input["shifts"]-2):
                if input["costs"][d][s1][n] == -1:
                    continue
                for s2 in range(s1 + 2, input["shifts"]):
                    if input["costs"][d][s2][n] == -1:
                        continue
                    enc.add(Implies(And([input["vars"][d][s1][n], Not(input["vars"][d][s1+1][n])]), Not(input["vars"][d][s2][n])))
    return enc


# Each nurse has a minimum and maximum number of shifts it can do each day
def bool_encode_shifts_per_day(input, enc):
    for d in range(input["days"]):
        for n in range(input["nurses"]):
            lits = [input["vars"][d][s][n] for s in range(input["shifts"]) if input["costs"][d][s][n] != -1]
            enc.add(PbGe([(v, 1) for v in lits], input["nurse_shifts"][n][0]))
            enc.add(PbLe([(v, 1) for v in lits], input["nurse_shifts"][n][1]))
    return enc

# Each nurse can only do Hk shifts throughout the D days
def bool_encode_max_shifts(input, enc):
    for n in range(input["nurses"]):
        lits = [input["vars"][d][s][n] for d in range(input["days"]) for s in range(input["shifts"]) if input["costs"][d][s][n] != -1]
        enc.add(PbLe([(v, 1) for v in lits], input["nurse_shifts"][n][2]))
    return enc

# Each shift must have at least one nurse with managerial qualifications
def bool_encode_min_managerial(input, enc):
    for d in range(input["days"]):
        for s in range(input["shifts"]):
            enc.add(Or([input["vars"][d][s][n] for n in range(input["nurses"]) if input["costs"][d][s][n] != -1 and input["nurses_managerial"][n]]))
    return enc

# A nurse is never assigned to a shift in which she said she was unavailable
# The cost of assignment is minimized
def bool_encode_costs(input, enc):
    for d in range(input["days"]):
        for s in range(input["shifts"]):
            for n in range(input["nurses"]):
                if input["costs"][d][s][n] == -1:
                    enc.add(Not(input["vars"][d][s][n]))
    total_cost = Sum([
        If(input["vars"][d][s][n], input["costs"][d][s][n], 0)
        for d in range(input["days"])
        for s in range(input["shifts"])
        for n in range(input["nurses"])
        if input["costs"][d][s][n] != -1
    ])
    enc.minimize(total_cost)
    return enc

def bool_print_output(enc, D, S, N, input):
    total_cost = Sum([
        If(input["vars"][d][s][n], input["costs"][d][s][n], 0)
        for d in range(input["days"])
        for s in range(input["shifts"])
        for n in range(input["nurses"])
        if input["costs"][d][s][n] != -1
    ])
    
    if enc.check() != sat:
        print("Problem not satisfiable")
        return

    model = enc.model()
    print(model.evaluate(total_cost))
    for d in range(D):
        for s in range(S):
            shift_nurses = [n+1 for n in range(N) if model.evaluate(input["vars"][d][s][n])]
            print(len(shift_nurses), end='')
            for nurse in shift_nurses:
                print(" " + str(nurse), end='')
            print()

def first_solution():
    input = bool_load_input()
    enc = Optimize()
    
    precompute(input)
    enc = bool_encode_min_nurses(input, enc)
    enc = bool_encode_continous_shifts(input, enc)
    enc = bool_encode_shifts_per_day(input, enc)
    enc = bool_encode_max_shifts(input, enc)
    enc = bool_encode_min_managerial(input, enc)
    enc = bool_encode_costs(input, enc)
    
    bool_print_output(enc, input["days"], input["shifts"], input["nurses"], input)

# Reads the problem specification from the standard input
def int_load_input():
    input = {"nurses_managerial": [], "min_nurses": [], "nurse_shifts": [], "costs": [], "vars": []}

    input["days"], input["shifts"] = map(int, stdin.readline().split())

    for _ in range(input["days"]):
        input["min_nurses"].append([int(n) for n in stdin.readline().split()])
    
    input["nurses"] = int(stdin.readline().split()[0])

    input["vars"] = [[[Int("nurse_start_" + str(n) + "_" + str(d)), Int("nurse_end_" + str(n) + "_" + str(d))] for n in range(input["nurses"])] for d in range(input["days"])]

    for _ in range(input["nurses"]):
        line = stdin.readline().split()
        input["nurses_managerial"].append(1 if line[0] == "Y" else 0)
        input["nurse_shifts"].append((int(line[1]), int(line[2]), int(line[3])))
    
    for _ in range(input["days"]):
        input["costs"].append([[int(c) for c in stdin.readline().split()] for _ in range(input["shifts"])])
    
    return input

def int_encode_possible_workloads(input, enc):
    for d in range(input["days"]):
        for n in range(input["nurses"]):
            enc.add(Or(
                    And(input["vars"][d][n][0] == 0, input["vars"][d][n][1] == 0),
                    And(input["vars"][d][n][0] >= 1, input["vars"][d][n][0] <= input["shifts"],
                        input["vars"][d][n][1] >= 2, input["vars"][d][n][1] <= input["shifts"] + 1,
                        input["vars"][d][n][0] < input["vars"][d][n][1]
                    )
                ))
    return enc

def int_encode_shifts_per_day(input, enc):
    for d in range(input["days"]):
        for n in range(input["nurses"]):
            enc.add(input["vars"][d][n][1] - input["vars"][d][n][0] >= input["nurse_shifts"][n][0])
            enc.add(input["vars"][d][n][1] - input["vars"][d][n][0] <= input["nurse_shifts"][n][1])
    return enc

def int_encode_min_nurses(input, enc):
    for d in range(input["days"]):
        for s in range(1, input["shifts"] + 1):
            sum_conditions = [If(And(s >= input["vars"][d][n][0], s < input["vars"][d][n][1]), 1, 0) for n in range(input["nurses"]) if input["costs"][d][s-1][n] != -1]
            man_sum_conditions = [If(And(s >= input["vars"][d][n][0], s < input["vars"][d][n][1]), 1, 0) for n in range(input["nurses"]) if input["nurses_managerial"][n] and input["costs"][d][s-1][n] != -1]
            enc.add(Sum(sum_conditions) >= input["min_nurses"][d][s-1])
            enc.add(Sum(man_sum_conditions) >= 1)

    return enc

def int_encode_max_shifts(input, enc):
    for n in range(input["nurses"]):
        worked_shifts = []
        for d in range(input["days"]):
            worked_shifts.append(input["vars"][d][n][1] - input["vars"][d][n][0])
        enc.add(Sum(worked_shifts) <= input["nurse_shifts"][n][2])

    return enc

def int_encode_costs(input, enc):
    costs = []
    for d in range(input["days"]):
        for s in range(1, input["shifts"] + 1):
            for n in range(input["nurses"]):
                if input["costs"][d][s-1][n] == -1:
                    # The nurse either starts its first shift after the unavailable one or ends its last shift before the unavailable one
                    if s <= input["nurse_shifts"][n][0]:
                        enc.add(input["vars"][d][n][0] > s)
                    elif s > input["shifts"] - input["nurse_shifts"][n][0]:
                        enc.add(input["vars"][d][n][1] <= s)
                    else:
                        enc.add(Not(And(s >= input["vars"][d][n][0], s < input["vars"][d][n][1])))
                else:
                    costs.append(If(And(s >= input["vars"][d][n][0], s < input["vars"][d][n][1]), input["costs"][d][s-1][n], 0))
    enc.minimize(Sum(costs))
    return enc

def int_print_output(enc, D, S, N, input):
    total_cost = Sum([
        If(And(s >= input["vars"][d][n][0], s < input["vars"][d][n][1]), input["costs"][d][s-1][n], 0)
        for d in range(input["days"])
        for s in range(1, input["shifts"] + 1)
        for n in range(input["nurses"])
        if input["costs"][d][s-1][n] != -1
    ])
    
    if enc.check() != sat:
        print("Problem not satisfiable")
        return

    model = enc.model()
    output = [[[False for n in range(N)] for s in range(S)] for d in range(D)]
    for d in range(D):
        for n in range(N):
            start = model.evaluate(input["vars"][d][n][0]).as_long()
            end = model.evaluate(input["vars"][d][n][1]).as_long()
            for s in range(start, end):
                output[d][s-1][n] = True

    print(model.evaluate(total_cost))
    for d in range(D):
        for s in range(S):
            shift_nurses = [n+1 for n in range(N) if output[d][s][n]]
            print(len(shift_nurses), end='')
            for nurse in shift_nurses:
                print(" " + str(nurse), end='')
            print()
    

def second_solution():
    input = int_load_input()
    enc = Optimize()

    enc = int_encode_possible_workloads(input, enc)
    enc = int_encode_min_nurses(input, enc)
    enc = int_encode_shifts_per_day(input, enc)
    enc = int_encode_max_shifts(input, enc)
    enc = int_encode_costs(input, enc)
    
    int_print_output(enc, input["days"], input["shifts"], input["nurses"], input)

def main():
    second_solution()


if __name__ == "__main__":
    main()
