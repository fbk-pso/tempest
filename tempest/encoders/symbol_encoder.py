from functools import lru_cache
import pysmt
from typing import List, Optional

import pysmt.environment
from unified_planning.model import Action, DurativeAction, Effect, Fluent, FNode, Object, Parameter, Type
import pysmt


class SymbolEncoder:
    def __init__(self, objects: List[Object], pysmt_env: pysmt.environment.Environment):
        assert pysmt_env is not None
        self.pysmt_env = pysmt_env
        self.mgr = self.pysmt_env.formula_manager
        self.objects = objects
        self.type_constraints = {}
        self.c = 0

    @lru_cache(maxsize=None)
    def t(self, i: int):
        return self.mgr.Symbol(f"t@{i}", pysmt.shortcuts.REAL)

    @lru_cache(maxsize=None)
    def t_a(self, a: Action, h: int):
        return self.mgr.Symbol(f"t{a.name}@{h}", pysmt.shortcuts.REAL)

    @lru_cache(maxsize=None)
    def t_last(self):
        return self.mgr.Symbol("t@last", pysmt.shortcuts.REAL)

    @lru_cache(maxsize=None)
    def action(self, action: Action, i: int):
        return self.mgr.Symbol(f"act_{action.name}@{i}")

    @lru_cache(maxsize=None)
    def chain_var(self, action: Optional[Action], e: Effect, i: int, w: int):
        self.c += 1
        if action is None:
            return self.mgr.Symbol(f"problem_{self.c}@{i}-{w}")
        else:
            return self.mgr.Symbol(f"act_{action.name}_{self.c}@{i}-{w}")

    @lru_cache(maxsize=None)
    def duration(self, action: DurativeAction, i: int):
        return self.mgr.Symbol(f"dur_{action.name}@{i}", pysmt.shortcuts.REAL)

    @lru_cache(maxsize=None)
    def fluent(self, fluent: Fluent, args: List[FNode], i: int):
        smt_type, lb, ub = self.type_to_smt(fluent.type)
        args_str = f"_{'_'.join([str(a) for a in args])}"
        res = self.mgr.Symbol(f"fluent_{fluent.name}{args_str}@{i}", smt_type)
        self.add_type_constraints(res, fluent.type, lb, ub, i)
        return res

    @lru_cache(maxsize=None)
    def parameter(self, action: Action, parameter: Parameter, i: int):
        smt_type, lb, ub = self.type_to_smt(parameter.type)
        res = self.mgr.Symbol(f"parameter_{action.name}_{parameter.name}@{i}", smt_type)
        self.add_type_constraints(res, parameter.type, lb, ub, i)
        return res

    def add_type_constraints(self, symbol, type: Type, lb: Optional[int], ub: Optional[int], i: int):
        self.type_constraints.setdefault(i, set())
        if type.is_user_type():
            l = []
            for p in range(lb, ub+1):
                l.append(self.mgr.Equals(symbol, self.mgr.Real(p)))
            self.type_constraints[i].add(self.mgr.Or(l))
        else:
            if lb is not None:
                self.type_constraints[i].add(self.mgr.GE(symbol, self.mgr.Real(lb)))
            if ub is not None:
                self.type_constraints[i].add(self.mgr.LE(symbol, self.mgr.Real(ub)))

    def type_to_smt(self, type: Type):
        if type.is_bool_type():
            return pysmt.shortcuts.BOOL, None, None
        elif type.is_int_type() or type.is_real_type():
            lb, ub = type.lower_bound, type.upper_bound
            return pysmt.shortcuts.REAL, lb, ub
        elif type.is_user_type():
            lb = None
            for obj, i in self.objects.items():
                if obj.type == type:
                    if lb is None:
                        lb = i
                    ub = i
            return pysmt.shortcuts.REAL, lb, ub
        else:
            raise NotImplementedError(f"Unknown type in conversion: {type}")
