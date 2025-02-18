from unified_planning.shortcuts import *
from unified_planning.test import TestCase

#Setting up Types
Robot = UserType('Robot')
Pallet = UserType('Pallet')
Position = UserType('Position')
Treatment = UserType('Treatment')

#Setting up Fluents
robot_at = Fluent('robot_at', BoolType(), r=Robot, p=Position)
robot_has = Fluent('robot_has',BoolType(),r=Robot, p=Pallet)
pallet_at = Fluent('pallet_at', BoolType(), p=Pallet, pos=Position)
robot_free = Fluent('robot_free',BoolType(), r=Robot)
position_free = Fluent('position_free',BoolType(),p=Position)
can_do = Fluent('can_do',BoolType(),p=Position, t=Treatment)
treated = Fluent('treated',BoolType(),p=Pallet,t=Treatment)
ready = Fluent('ready',BoolType(),p=Pallet,pos=Position,t=Treatment)
is_depot = Fluent('is_depot',BoolType(),p=Position)
battery_level = Fluent('battery_level', IntType(0, 100), r=Robot)
distance = Fluent('distance', IntType(), pfrom=Position, pto=Position)

#Setting up Actions:
move = InstantaneousAction('move', r=Robot, frompos=Position, topos=Position)
move.add_precondition(Not(Equals(move.frompos, move.topos)))
move.add_precondition(robot_at(move.r, move.frompos))
move.add_precondition(GE(battery_level(move.r), distance(move.frompos, move.topos)))
move.add_effect(robot_at(move.r, move.topos), True)
move.add_effect(robot_at(move.r, move.frompos), False)
move.add_decrease_effect(battery_level(move.r), distance(move.frompos, move.topos))

unload_at_depot = InstantaneousAction('unload_at_depot', r=Robot, pallet=Pallet, pos=Position)
unload_at_depot.add_precondition(is_depot(unload_at_depot.pos))
unload_at_depot.add_precondition(robot_at(unload_at_depot.r, unload_at_depot.pos))
unload_at_depot.add_precondition(robot_has(unload_at_depot.r, unload_at_depot.pallet))
unload_at_depot.add_effect(pallet_at(unload_at_depot.pallet, unload_at_depot.pos),True)
unload_at_depot.add_effect(robot_free(unload_at_depot.r),True)
unload_at_depot.add_effect(robot_has(unload_at_depot.r, unload_at_depot.pallet),False)

load_at_depot = InstantaneousAction('load_at_depot', r=Robot, pallet=Pallet, pos=Position)
load_at_depot.add_precondition(is_depot(load_at_depot.pos))
load_at_depot.add_precondition(robot_at(load_at_depot.r, load_at_depot.pos))
load_at_depot.add_precondition(robot_free(load_at_depot.r))
load_at_depot.add_precondition(pallet_at(load_at_depot.pallet, load_at_depot.pos))
load_at_depot.add_effect(robot_free(load_at_depot.r), False)
load_at_depot.add_effect(robot_has(load_at_depot.r, load_at_depot.pallet), True)
load_at_depot.add_effect(pallet_at(load_at_depot.pallet, load_at_depot.pos), False)

make_treat = DurativeAction('make_treatment', r=Robot, pallet=Pallet, pos=Position, t=Treatment)
make_treat.set_fixed_duration(20)
make_treat.add_condition(StartTiming(), can_do(make_treat.pos, make_treat.t))
make_treat.add_condition(StartTiming(), position_free(make_treat.pos))
make_treat.add_condition(StartTiming(), robot_at(make_treat.r, make_treat.pos))
make_treat.add_condition(StartTiming(), robot_has(make_treat.r, make_treat.pallet))
make_treat.add_condition(StartTiming(), Not(treated(make_treat.pallet, make_treat.t)))
make_treat.add_condition(EndTiming(), treated(make_treat.pallet, make_treat.t))
make_treat.add_condition(EndTiming(), position_free(make_treat.pos))
make_treat.add_effect(StartTiming(), position_free(make_treat.pos), False)
make_treat.add_effect(StartTiming(), robot_has(make_treat.r, make_treat.pallet), False)
make_treat.add_effect(StartTiming(), pallet_at(make_treat.pallet, make_treat.pos), True)
make_treat.add_effect(StartTiming(), robot_free(make_treat.r), True)
make_treat.add_effect(StartTiming(10), ready(make_treat.pallet, make_treat.pos, make_treat.t), True)

load = InstantaneousAction('load', r=Robot, pallet=Pallet, pos=Position, t=Treatment)
load.add_precondition(ready(load.pallet, load.pos, load.t))
load.add_precondition(robot_at(load.r, load.pos))
load.add_precondition(robot_free(load.r))
load.add_precondition(pallet_at(load.pallet, load.pos))
load.add_effect(robot_free(load.r), False)
load.add_effect(ready(load.pallet, load.pos, load.t), False)
load.add_effect(pallet_at(load.pallet, load.pos), False)
load.add_effect(robot_has(load.r, load.pallet), True)
load.add_effect(treated(load.pallet, load.t), True)
load.add_effect(position_free(load.pos), True)


def get_problems(nRob, nPall, nPos, nTreatment):

    name_suffix = '_'.join(map(str, [nRob, nPall, nPos, nTreatment]))
    p = Problem(f'majsp_{name_suffix}')

    for f in [robot_at, robot_free, robot_has, ready,
              position_free, treated, pallet_at, can_do, is_depot]:
        p.add_fluent(f, default_initial_value=False)
    p.add_fluent(battery_level, default_initial_value=0)
    p.add_fluent(distance, default_initial_value=0)

    p.add_objects([Object(f'r{i}',Robot) for i in range(nRob)])
    p.add_objects([Object(f'p{i}',Position) for i in range(nPos)])
    p.add_objects([Object(f'plt{i}',Pallet) for i in range(nPall)])
    p.add_objects([Object(f't{i}',Treatment) for i in range(nTreatment)])

    p.add_action(move)
    p.add_action(load)
    p.add_action(load_at_depot)
    p.add_action(unload_at_depot)
    p.add_action(make_treat)

    last_position = p.object(f'p{nPos-1}')
    #All robots stay at the same position, and so do the pallets
    for i in range(nRob):
        p.set_initial_value(robot_at(p.object(f'r{i}'), last_position),True)
        p.set_initial_value(robot_free(p.object(f'r{i}')),True)
    for i in range(nPall):
        p.set_initial_value(pallet_at(p.object(f'plt{i}'), last_position),True)


    for i in range(nRob):
        p.set_initial_value(battery_level(p.object(f'r{i}')), nPos*nPall*2)

    for i in range(nPos):
        p.set_initial_value(distance(p.object(f'p{i}'), p.object(f'p{i}')), 0)
        for j in range(i+1, nPos):
            p.set_initial_value(distance(p.object(f'p{i}'), p.object(f'p{j}')), j-i)
            p.set_initial_value(distance(p.object(f'p{j}'), p.object(f'p{i}')), j-i)

    #last position is the depot
    p.set_initial_value(is_depot(last_position),True)
    for i in range(nPos):
        p.set_initial_value(position_free(p.object(f'p{i}')),True)

    #Treatments are done over the various positions
    for i in range(nTreatment):
        treatment_position = i % (nPos-1)
        p.set_initial_value(can_do(p.object(f'p{treatment_position}'),p.object(f't{i}')),True)
        for k in range(nPall):
            p.add_goal(treated(p.object(f'plt{k}'),p.object(f't{i}')))

    p.add_quality_metric(MinimizeMakespan())

    return p


def get_test_cases():
    parameters_optimum = [
        ([1, 1, 2, 1], Fraction(2002, 100)),
    ]
    test_cases = {}
    for params, optimum in parameters_optimum:
        problem = get_problems(*params)
        test_cases[problem.name] = TestCase(problem, True, optimum)
    return test_cases
