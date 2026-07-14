# Copyright (C) 2025 PSO Unit, Fondazione Bruno Kessler
# This file is part of TemPEST.
#
# TemPEST is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# TemPEST is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program. If not, see <https://www.gnu.org/licenses/>.
#

from collections.abc import Hashable
from functools import cache

import pysmt
import pysmt.environment
import pysmt.typing
from pysmt.fnode import FNode as SMTFNode
from pysmt.typing import PySMTType
from unified_planning.model import (
    Action,
    DurativeAction,
    Fluent,
    FNode,
    Object,
    Parameter,
    Type,
)


class SymbolEncoder:
    def __init__(
        self, objects: dict[Object, int], pysmt_env: pysmt.environment.Environment
    ) -> None:
        assert pysmt_env is not None
        self.pysmt_env = pysmt_env
        self.mgr = self.pysmt_env.formula_manager
        self.objects = objects
        self.type_constraints: dict[int, set[SMTFNode]] = {}
        self.c = 0

    @cache
    def t(self, i: int) -> SMTFNode:
        return self.mgr.Symbol(f"t@{i}", pysmt.typing.REAL)

    @cache
    def t_a(self, a: Action, h: int) -> SMTFNode:
        return self.mgr.Symbol(f"t{a.name}@{h}", pysmt.typing.REAL)

    @cache
    def t_last(self) -> SMTFNode:
        return self.mgr.Symbol("t@last", pysmt.typing.REAL)

    @cache
    def action(self, action: Action, i: int) -> SMTFNode:
        return self.mgr.Symbol(f"act_{action.name}@{i}")

    @cache
    def chain_var(self, action: Action | None, e: Hashable, i: int, w: int) -> SMTFNode:
        self.c += 1
        if action is None:
            return self.mgr.Symbol(f"problem_{self.c}@{i}-{w}")
        else:
            return self.mgr.Symbol(f"act_{action.name}_{self.c}@{i}-{w}")

    @cache
    def duration(self, action: DurativeAction, i: int) -> SMTFNode:
        return self.mgr.Symbol(f"dur_{action.name}@{i}", pysmt.typing.REAL)

    @cache
    def fluent(self, fluent: Fluent, args: tuple[FNode, ...], i: int) -> SMTFNode:
        smt_type, lb, ub = self.type_to_smt(fluent.type)
        args_str = f"_{'_'.join([str(a) for a in args])}" if args else ""
        res = self.mgr.Symbol(f"fluent_{fluent.name}{args_str}@{i}", smt_type)
        self.add_type_constraints(res, fluent.type, lb, ub, i)
        return res

    @cache
    def parameter(self, action: Action, parameter: Parameter, i: int) -> SMTFNode:
        smt_type, lb, ub = self.type_to_smt(parameter.type)
        res = self.mgr.Symbol(f"parameter_{action.name}_{parameter.name}@{i}", smt_type)
        self.add_type_constraints(res, parameter.type, lb, ub, i)
        return res

    def add_type_constraints(
        self, symbol: SMTFNode, type: Type, lb: int | None, ub: int | None, i: int
    ) -> None:
        self.type_constraints.setdefault(i, set())
        if type.is_user_type():
            # A user type always yields concrete integer bounds (see type_to_smt).
            assert lb is not None and ub is not None
            terms = [
                self.mgr.Equals(symbol, self.mgr.Real(p)) for p in range(lb, ub + 1)
            ]
            self.type_constraints[i].add(self.mgr.Or(terms))
        else:
            if lb is not None:
                self.type_constraints[i].add(self.mgr.GE(symbol, self.mgr.Real(lb)))
            if ub is not None:
                self.type_constraints[i].add(self.mgr.LE(symbol, self.mgr.Real(ub)))

    def type_to_smt(self, type: Type) -> tuple[PySMTType, int | None, int | None]:
        if type.is_bool_type():
            return pysmt.typing.BOOL, None, None
        elif type.is_int_type() or type.is_real_type():
            lb, ub = type.lower_bound, type.upper_bound
            return pysmt.typing.REAL, lb, ub
        elif type.is_user_type():
            lb, ub = None, None
            for obj, i in self.objects.items():
                if obj.type == type:
                    if lb is None:
                        lb = i
                    ub = i
            assert lb is not None and ub is not None
            return pysmt.typing.REAL, lb, ub
        else:
            raise NotImplementedError(f"Unknown type in conversion: {type}")
