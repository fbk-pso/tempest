from typing import OrderedDict
from pysmt.environment import get_env
from unittest import TestCase
from unified_planning.shortcuts import *

from tempest.encoders.symbol_encoder import SymbolEncoder
from tempest.converter import SMTConverter

class TestConverter(TestCase):
    def test_converter(self):

        # problem definition
        problem = Problem("counter")
        CounterType = UserType("CounterType")

        # int fluents
        counter = problem.add_fluent("counter", IntType(), default_initial_value=0)
        counter_param = problem.add_fluent("counter_param", IntType(), default_initial_value=0, param=CounterType)
        static = problem.add_fluent("static", IntType(), default_initial_value=5)
        static_param = problem.add_fluent("static_param", IntType(), default_initial_value=1, param=CounterType)

        # real fluents
        real_counter = problem.add_fluent("real_counter", RealType(), default_initial_value=0)
        real_counter_param = problem.add_fluent("real_counter_param", RealType(), default_initial_value=0, param=CounterType)
        real_static = problem.add_fluent("real_static", RealType(), default_initial_value=5)
        real_static_param = problem.add_fluent("real_static_param", RealType(), default_initial_value=1, param=CounterType)

        # bool fluents
        bool_counter = problem.add_fluent("bool_counter", BoolType(), default_initial_value=False)
        bool_counter_param = problem.add_fluent("bool_counter_param", BoolType(), default_initial_value=False, param=CounterType)
        bool_static = problem.add_fluent("bool_static", BoolType(), default_initial_value=False)
        bool_static_param = problem.add_fluent("bool_static_param", BoolType(), default_initial_value=False, param=CounterType)

        increase_counter = DurativeAction("increase counter")
        increase_counter.set_fixed_duration(1)
        increase_counter.add_increase_effect(EndTiming(), counter, 1)
        increase_counter.add_increase_effect(EndTiming(), real_counter, 1)
        increase_counter.add_effect(EndTiming(), bool_counter, Not(bool_counter))

        problem.add_action(increase_counter)

        increase_counter_param = DurativeAction("increase counter param", counter_obj=CounterType)
        counter_obj_param = increase_counter_param.counter_obj
        increase_counter_param.set_fixed_duration(1)
        increase_counter_param.add_increase_effect(EndTiming(), counter_param(counter_obj_param), 1)
        increase_counter.add_increase_effect(EndTiming(), real_counter_param(counter_obj_param), 1)
        increase_counter.add_effect(EndTiming(), bool_counter_param(counter_obj_param), Not(bool_counter_param(counter_obj_param)))

        problem.add_action(increase_counter_param)

        c1, c2, c3 = (problem.add_object(f"c_{i}", CounterType) for i in range(1, 4))

        problem.set_initial_value(static_param(c2), 2)
        problem.set_initial_value(static_param(c3), 3)

        problem.set_initial_value(real_static_param(c2), 2)
        problem.set_initial_value(real_static_param(c3), 3)

        problem.set_initial_value(bool_static_param(c2), True)
        problem.set_initial_value(bool_static_param(c3), True)

        problem.add_goal(Equals(counter, 3))
        problem.add_goal(Equals(counter_param(c1), 1))
        problem.add_goal(Equals(counter_param(c2), 2))
        problem.add_goal(Equals(counter_param(c3), 3))

        objects = OrderedDict()
        i = 0
        for ut in problem.user_types:
            for obj in problem.objects(ut):
                objects[obj] = i
                i += 1

        # expressions definition
        expressions_oracle_scope = [
            # Tuple of the expression, the oracle str and the scope in which the expression is evaluated
            # In the oracle str, {{i}} and {{w}} will be substituted with the i and w values
            # int expressions
            (static(), "5.0", None),
            (static_param(c1), "1.0", None),
            (static_param(c2), "2.0", None),
            (static_param(c3), "3.0", None),
            (
                static_param(counter_obj_param),
                f"(('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 2.0) ? 3.0 : (('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 1.0) ? 2.0 : 1.0))",
                increase_counter_param
            ),
            (counter(), f"fluent_{counter.name}@{{i}}", None),
            (counter_param(c1), f"fluent_{counter_param.name}_{c1.name}@{{i}}", None),
            (counter_param(c2), f"fluent_{counter_param.name}_{c2.name}@{{i}}", None),
            (counter_param(c3), f"fluent_{counter_param.name}_{c3.name}@{{i}}", None),
            (counter_param(counter_obj_param), f"(('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 2.0) ? fluent_{counter_param.name}_{c3.name}@{{i}} : (('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 1.0) ? fluent_{counter_param.name}_{c2.name}@{{i}} : fluent_{counter_param.name}_{c1.name}@{{i}}))", increase_counter_param),
            (static + static_param(c1), "(5.0 + 1.0)", None),
            (static_param(c2) - static, "(2.0 - 5.0)", None),
            (static_param(c3) / static, "(3.0 * 1/5)", None),
            (static_param(c1) * static, "(1.0 * 5.0)", None),
            (
                static + static_param(counter_obj_param),
                f"(5.0 + (('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 2.0) ? 3.0 : (('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 1.0) ? 2.0 : 1.0)))",
                increase_counter_param
            ),
            (static_param(c2).Equals(static_param(c1)), "(2.0 = 1.0)", None),
            (
                static_param(counter_obj_param).Equals(static_param(c1)),
                f"((('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 2.0) ? 3.0 : (('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 1.0) ? 2.0 : 1.0)) = 1.0)",
                increase_counter_param
            ),
            (counter + counter_param(c1), f"(fluent_{counter.name}@{{i}} + fluent_{counter_param.name}_{c1.name}@{{i}})", None),
            (counter / counter_param(counter_obj_param), f"(fluent_{counter.name}@{{i}} / (('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 2.0) ? fluent_{counter_param.name}_{c3.name}@{{i}} : (('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 1.0) ? fluent_{counter_param.name}_{c2.name}@{{i}} : fluent_{counter_param.name}_{c1.name}@{{i}})))", increase_counter_param),

            # real expressions
            (real_static(), "5.0", None),
            (real_static_param(c1), "1.0", None),
            (real_static_param(c2), "2.0", None),
            (real_static_param(c3), "3.0", None),
            (
                real_static_param(counter_obj_param),
                f"(('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 2.0) ? 3.0 : (('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 1.0) ? 2.0 : 1.0))",
                increase_counter_param
            ),
            (real_counter(), f"fluent_{real_counter.name}@{{i}}", None),
            (real_counter_param(c1), f"fluent_{real_counter_param.name}_{c1.name}@{{i}}", None),
            (real_counter_param(c2), f"fluent_{real_counter_param.name}_{c2.name}@{{i}}", None),
            (real_counter_param(c3), f"fluent_{real_counter_param.name}_{c3.name}@{{i}}", None),
            (real_counter_param(counter_obj_param), f"(('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 2.0) ? fluent_{real_counter_param.name}_{c3.name}@{{i}} : (('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 1.0) ? fluent_{real_counter_param.name}_{c2.name}@{{i}} : fluent_{real_counter_param.name}_{c1.name}@{{i}}))", increase_counter_param),
            (real_static + real_static_param(c1), "(5.0 + 1.0)", None),
            (real_static_param(c2) - real_static, "(2.0 - 5.0)", None),
            (real_static_param(c3) / real_static, "(3.0 * 1/5)", None),
            (real_static_param(c1) * real_static, "(1.0 * 5.0)", None),
            (
                real_static + real_static_param(counter_obj_param),
                f"(5.0 + (('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 2.0) ? 3.0 : (('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 1.0) ? 2.0 : 1.0)))",
                increase_counter_param
            ),
            (real_static_param(c2).Equals(real_static_param(c1)), "(2.0 = 1.0)", None),
            (
                real_static_param(counter_obj_param).Equals(real_static_param(c1)),
                f"((('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 2.0) ? 3.0 : (('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 1.0) ? 2.0 : 1.0)) = 1.0)",
                increase_counter_param
            ),
            (real_counter + real_counter_param(c1), f"(fluent_{real_counter.name}@{{i}} + fluent_{real_counter_param.name}_{c1.name}@{{i}})", None),
            (real_counter / real_counter_param(counter_obj_param), f"(fluent_{real_counter.name}@{{i}} / (('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 2.0) ? fluent_{real_counter_param.name}_{c3.name}@{{i}} : (('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 1.0) ? fluent_{real_counter_param.name}_{c2.name}@{{i}} : fluent_{real_counter_param.name}_{c1.name}@{{i}})))", increase_counter_param),

            # bool expressions
            (bool_static(), "False", None),
            (bool_static_param(c1), "False", None),
            (bool_static_param(c2), "True", None),
            (bool_static_param(c3), "True", None),
            (
                bool_static_param(counter_obj_param),
                f"(('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 2.0) ? True : (('parameter_{increase_counter_param.name}_{counter_obj_param.name}@{{w}}' = 1.0) ? True : False))",
                increase_counter_param
            ),
            (bool_counter(), f"fluent_{bool_counter.name}@{{i}}", None),
            (bool_counter_param(c1), f"fluent_{bool_counter_param.name}_{c1.name}@{{i}}", None),
            (bool_counter_param(c2), f"fluent_{bool_counter_param.name}_{c2.name}@{{i}}", None),
            (bool_counter_param(c3), f"fluent_{bool_counter_param.name}_{c3.name}@{{i}}", None),

            (bool_static & bool_static_param(c1), "(False & False)", None),
            (bool_static_param(c2) | bool_static, "(True | False)", None),
            (bool_static_param(c3) & Not(bool_static), "(True & (! False))", None),
        ]

        # testing of expressions
        sym_enc = SymbolEncoder(objects, get_env())
        for expression, oracle_str, scope in expressions_oracle_scope:
            i_range = range(10) if "{i}" in oracle_str else [10]
            for i in i_range:
                w_range = range(i+1) if "{w}" in oracle_str else [0]
                for w in w_range:
                    converter = SMTConverter(
                        i=i, w=w, symenc=sym_enc, pysmt_env=get_env(), problem=problem,
                        objects=objects, static_fluents=problem.get_static_fluents(),
                        scope=scope
                    )
                    converted_exp = converter.to_smt(expression)
                    expected_str = self._convert_expected_str(oracle_str, i, w)
                    self.assertEqual(str(converted_exp), expected_str, f"i: {i}; w: {w}; expression: {expression}; converted_expression: {converted_exp}; oracle_str: {oracle_str}; expected_str: {expected_str}")

    def _convert_expected_str(self, expected_str: str, i: int, w: int):
        expected_str = expected_str.replace("{i}", str(i))
        expected_str = expected_str.replace("{w}", str(w))
        return expected_str
