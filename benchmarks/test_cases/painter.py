from unified_planning.shortcuts import *
from unified_planning.test import TestCase

Item = UserType("Item")
Treatment = UserType("Treatment")

busy = Fluent("busy")
treated = Fluent("treated", BoolType(), i=Item, t=Treatment)
started = Fluent("started", BoolType(), i=Item, t=Treatment)
ready = Fluent("ready", BoolType(), i=Item, t=Treatment)
counter = Fluent("counter", IntType(0, 31), t=Treatment)
item_id = Fluent("item_id", IntType(0, 31), i=Item)
consecutive = Fluent("consecutive", BoolType(), t1=Treatment, t2=Treatment)

make_treatment = DurativeAction("make_treatment", i=Item, t=Treatment, next=Treatment)
make_treatment.set_fixed_duration(15)
make_treatment.add_condition(StartTiming(), Equals(item_id(make_treatment.i), counter(make_treatment.t)))
make_treatment.add_condition(StartTiming(), consecutive(make_treatment.t, make_treatment.next))
make_treatment.add_condition(StartTiming(), Not(busy))
make_treatment.add_condition(StartTiming(), Not(treated(make_treatment.i, make_treatment.t)))
make_treatment.add_condition(StartTiming(), Not(started(make_treatment.i, make_treatment.t)))
make_treatment.add_condition(StartTiming(), ready(make_treatment.i, make_treatment.t))
make_treatment.add_increase_effect(StartTiming(), counter(make_treatment.t), 1)
make_treatment.add_effect(StartTiming(), busy, True)
make_treatment.add_effect(StartTiming(), started(make_treatment.i, make_treatment.t), True)
make_treatment.add_effect(StartTiming(4), treated(make_treatment.i, make_treatment.t), True)
make_treatment.add_effect(StartTiming(4), busy, False)
make_treatment.add_effect(StartTiming(10), ready(make_treatment.i, make_treatment.next), True)
make_treatment.add_condition(EndTiming(), started(make_treatment.i, make_treatment.next))


def get_problems(n_t, n_i):
    p = Problem('problem')

    for f in [busy, treated, started, ready, consecutive]:
        p.add_fluent(f, default_initial_value=False)
    for f in [counter, item_id]:
        p.add_fluent(f, default_initial_value=0)

    p.add_objects([Object(f't{i}', Treatment) for i in range(n_t)])
    p.add_objects([Object(f'i{i}', Item) for i in range(n_i)])

    p.add_action(make_treatment)

    for i in range(n_i):
        p.set_initial_value(item_id(p.object(f"i{i}")), i)

    for t in range(n_t-1):
        p.set_initial_value(consecutive(p.object(f"t{t}"), p.object(f"t{t+1}")), True)

    for i in range(n_i):
        p.set_initial_value(started(p.object(f"i{i}"), p.object(f"t{n_t-1}")), True)
        p.set_initial_value(ready(p.object(f"i{i}"), p.object("t0")), True)

    for i in range(n_i):
        for t in range(n_t-1):
            p.add_goal(treated(p.object(f"i{i}"), p.object(f"t{t}")))

    p.add_quality_metric(MinimizeMakespan())

    return p


def get_test_cases():
    problems = {f"painter_{i}": TestCase(get_problems(i, i), True, optimum = 1) for i in range(1, 2)}
    return problems
