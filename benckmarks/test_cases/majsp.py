from itertools import product

from unified_planning.shortcuts import *
from unified_planning.test import TestCase

#Setting up Types
Robot = UserType("Robot")
Pallet = UserType("Pallet")
Position = UserType("Position")
Treatment = UserType("Treatment")

#Setting up Fluents
robot_at = Fluent("robot_at", BoolType(), r=Robot, p=Position)
robot_has = Fluent("robot_has",BoolType(),r=Robot, p=Pallet)
pallet_at = Fluent("pallet_at", BoolType(), p=Pallet, pos=Position)
robot_free = Fluent("robot_free",BoolType(), r=Robot)
position_free = Fluent("position_free",BoolType(),p=Position)
can_do = Fluent("can_do",BoolType(),p=Position, t=Treatment)
treated = Fluent("treated",BoolType(),p=Pallet,t=Treatment)
ready = Fluent("ready",BoolType(),p=Pallet,pos=Position,t=Treatment)
is_depot = Fluent("is_depot",BoolType(),p=Position)

#Setting up Actions:
move = DurativeAction("move", r=Robot,frompos=Position,topos=Position)
r = move.parameter("r")
frompos =move.parameter("frompos")
topos =move.parameter("topos")
move.set_fixed_duration(1)
move.add_condition(StartTiming(),Not(Equals(frompos,topos)))
move.add_condition(StartTiming(),robot_at(r,frompos))
move.add_effect(StartTiming(),robot_at(r,topos),True)
move.add_effect(StartTiming(),robot_at(r,frompos),False)

unload_at_depot = DurativeAction("unload_at_depot", r=Robot,pallet=Pallet,pos=Position)
r = unload_at_depot.parameter("r")
pallet =unload_at_depot.parameter("pallet")
pos =unload_at_depot.parameter("pos")
unload_at_depot.set_fixed_duration(1)
unload_at_depot.add_condition(StartTiming(),is_depot(pos))
unload_at_depot.add_condition(StartTiming(),robot_at(r,pos))
unload_at_depot.add_condition(StartTiming(),robot_has(r,pallet))
unload_at_depot.add_effect(StartTiming(),pallet_at(pallet,pos),True)
unload_at_depot.add_effect(StartTiming(),robot_free(r),True)
unload_at_depot.add_effect(StartTiming(),robot_has(r,pallet),False)

load_at_depot = DurativeAction("load_at_depot", r=Robot,pallet=Pallet,pos=Position)
r = load_at_depot.parameter("r")
pallet =load_at_depot.parameter("pallet")
pos =load_at_depot.parameter("pos")
load_at_depot.set_fixed_duration(1)
load_at_depot.add_condition(StartTiming(),is_depot(pos))
load_at_depot.add_condition(StartTiming(),robot_at(r,pos))
load_at_depot.add_condition(StartTiming(),robot_free(r))
load_at_depot.add_condition(StartTiming(),pallet_at(pallet,pos))
load_at_depot.add_effect(StartTiming(),robot_free(r),False)
load_at_depot.add_effect(StartTiming(),robot_has(r,pallet),True)
load_at_depot.add_effect(StartTiming(),pallet_at(pallet,pos),False)

make_treat = DurativeAction("make_treat", r=Robot,pallet=Pallet,pos=Position,t =Treatment)
r = make_treat.parameter("r")
pallet =make_treat.parameter("pallet")
pos =make_treat.parameter("pos")
t = make_treat.parameter("t")
make_treat.set_fixed_duration(20)
make_treat.add_condition(StartTiming(),can_do(pos,t))
make_treat.add_condition(StartTiming(),position_free(pos))
make_treat.add_condition(StartTiming(),robot_at(r,pos))
make_treat.add_condition(StartTiming(),robot_has(r,pallet))
make_treat.add_condition(StartTiming(),Not(treated(pallet,t)))
make_treat.add_condition(EndTiming(),treated(pallet,t))
make_treat.add_condition(EndTiming(),position_free(pos))
make_treat.add_effect(StartTiming(),position_free(pos),False)
make_treat.add_effect(StartTiming(),robot_has(r,pallet),False)
make_treat.add_effect(StartTiming(),pallet_at(pallet,pos),True)
make_treat.add_effect(StartTiming(),robot_free(r),True)
make_treat.add_effect(StartTiming(10),ready(pallet,pos,t),True)

load = DurativeAction("load", r=Robot, pallet = Pallet, pos = Position,t = Treatment)
r = load.parameter("r")
pallet = load.parameter("pallet")
pos = load.parameter("pos")
t = load.parameter("t")
load.set_fixed_duration(1)
load.add_condition(StartTiming(),ready(pallet,pos,t))
load.add_condition(StartTiming(),robot_at(r,pos))
load.add_condition(StartTiming(),robot_free(r))
load.add_condition(StartTiming(),pallet_at(pallet,pos))
load.add_effect(StartTiming(),robot_free(r),False)
load.add_effect(StartTiming(),ready(pallet,pos,t),False)
load.add_effect(StartTiming(),pallet_at(pallet,pos),False)
load.add_effect(StartTiming(),robot_has(r,pallet),True)
load.add_effect(StartTiming(),treated(pallet,t),True)
load.add_effect(StartTiming(),position_free(pos),True)

#Setting up the number of robots, positions, pallets and treatments
# nRob = 1 # to 3
# nPos = 2 # to 6
# nPall = 1 # to 4
# nTreatment = 1 # to 4

ALL_PARAMS = list(product(range(1,4), range(2,7), range(1,5), range(1,5)))

def get_problem(problem_id):

    nRob, nPos, nPall, nTreatment = ALL_PARAMS[problem_id]

    p = Problem("problem")
    for f in [robot_at, robot_free, robot_has, ready,
              position_free, treated, pallet_at, can_do, is_depot]:
        p.add_fluent(f, default_initial_value=False)

    p.add_objects([Object(f"r{i}",Robot) for i in range(nRob)])
    p.add_objects([Object(f"p{i}",Position) for i in range(nPos)])
    p.add_objects([Object(f"plt{i}",Pallet) for i in range(nPall)])
    p.add_objects([Object(f"t{i}",Treatment) for i in range(nTreatment)])

    p.add_action(move)
    p.add_action(load)
    p.add_action(load_at_depot)
    p.add_action(unload_at_depot)
    p.add_action(make_treat)

    #All robots stay at the same position, and so do the pallets
    for i in range(nRob):
        p.set_initial_value(robot_at(p.object(f"r{i}"),p.object("p0")),True)
        p.set_initial_value(robot_free(p.object(f"r{i}")),True)
    for i in range(nPall):
        p.set_initial_value(pallet_at(p.object(f"plt{i}"),p.object("p0")),True)

    #Position p0 is the depot
    p.set_initial_value(is_depot(p.object("p0")),True)
    for i in range(nPos):
        p.set_initial_value(position_free(p.object(f"p{i}")),True)

    #Treatments are done over the various positions
    for i in range(0,nTreatment):
        if i == 0:
            j = (i+1) % nPos #this is to avoid the the treatment is done at the depot
        else:
            j = i % nPos
        p.set_initial_value(can_do(p.object(f"p{j}"),p.object(f"t{i}")),True)
        for k in range(nPall):
            p.add_goal(treated(p.object(f"plt{k}"),p.object(f"t{i}")))

    return p

def get_test_cases():
    problems = {f"majsp_{i}": TestCase(get_problem(i), True) for i in range(1)}
    return problems
