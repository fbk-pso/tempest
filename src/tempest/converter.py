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

from typing import TYPE_CHECKING, Any

import pysmt.environment
import unified_planning.model.walkers as walkers
from pysmt.fnode import FNode as SMTFNode
from unified_planning.model import Action, Fluent, FNode, Object, Problem
from unified_planning.model.fluent import get_all_fluent_exp

if TYPE_CHECKING:
    # Runtime import would be circular: base_encoder imports this module.
    from tempest.encoders.symbol_encoder import SymbolEncoder


class SMTConverter(walkers.dag.DagWalker):
    def __init__(
        self,
        i: int,
        w: int | None,
        symenc: "SymbolEncoder",
        pysmt_env: pysmt.environment.Environment,
        problem: Problem,
        objects: dict[Object, int],
        static_fluents: set[Fluent],
        scope: Action | None,
    ) -> None:
        walkers.dag.DagWalker.__init__(self)
        self.pysmt_env = pysmt_env
        self.i = i
        self.w = w
        self.symenc = symenc
        self.manager = pysmt_env.formula_manager
        self.problem = problem
        self.static_fluents = static_fluents
        self.objects = objects
        self.scope = scope

    def to_smt(self, expression: FNode) -> SMTFNode:
        return self.walk(expression)

    def constant_to_smt(self, expression: FNode) -> SMTFNode:
        if expression.is_object_exp():
            va = self.manager.Real(self.objects[expression.object()])
        elif expression.is_bool_constant():
            va = self.manager.Bool(expression.bool_constant_value())
        elif expression.is_real_constant() or expression.is_int_constant():
            va = self.manager.Real(expression.constant_value())
        else:
            raise NotImplementedError
        return va

    def walk_fluent_exp(
        self, expression: FNode, args: list[SMTFNode]
    ) -> SMTFNode | None:
        f = expression.fluent()
        is_static = False
        if f in self.static_fluents:
            is_static = True
        if len(args) == 0 and is_static:
            init_val = self.problem.initial_value(expression)
            assert init_val is not None
            return self.constant_to_smt(init_val)
        elif len(args) == 0 and not is_static:
            return self.symenc.fluent(expression.fluent(), (), self.i)
        else:
            res = None
            for f_exp in get_all_fluent_exp(self.problem, expression.fluent()):
                if is_static:
                    init_val = self.problem.initial_value(f_exp)
                    assert init_val is not None
                    then = self.constant_to_smt(init_val)
                else:
                    then = self.symenc.fluent(f_exp.fluent(), tuple(f_exp.args), self.i)
                if res is None:
                    res = then
                else:
                    trivially_false = False
                    trivially_true = True
                    conds = []
                    for j, p in enumerate(args):
                        va = self.constant_to_smt(f_exp.arg(j))
                        if p.is_constant() and va.is_constant():
                            if p != va:
                                trivially_false = True
                                trivially_true = False
                                break
                        else:
                            trivially_true = False
                            conds.append(self.manager.Equals(p, va))
                    if trivially_true:
                        return then
                    if not trivially_false:
                        res = self.manager.Ite(self.manager.And(conds), then, res)
            return res

    def walk_bool_constant(
        self, expression: FNode, args: list[SMTFNode], **kwargs: Any
    ) -> SMTFNode:
        return self.manager.Bool(expression.bool_constant_value())

    def walk_int_constant(
        self, expression: FNode, args: list[SMTFNode], **kwargs: Any
    ) -> SMTFNode:
        return self.manager.Real(expression.int_constant_value())

    def walk_real_constant(
        self, expression: FNode, args: list[SMTFNode], **kwargs: Any
    ) -> SMTFNode:
        return self.manager.Real(expression.real_constant_value())

    def walk_param_exp(
        self, expression: FNode, args: list[SMTFNode], **kwargs: Any
    ) -> SMTFNode:
        assert self.scope is not None and self.w is not None
        return self.symenc.parameter(self.scope, expression.parameter(), self.w)

    def walk_object_exp(
        self, expression: FNode, args: list[SMTFNode], **kwargs: Any
    ) -> SMTFNode:
        return self.manager.Real(self.objects[expression.object()])

    def walk_and(self, expression: FNode, args: list[SMTFNode]) -> SMTFNode:
        return self.manager.And(args)

    def walk_or(self, expression: FNode, args: list[SMTFNode]) -> SMTFNode:
        return self.manager.Or(args)

    def walk_not(self, expression: FNode, args: list[SMTFNode]) -> SMTFNode:
        return self.manager.Not(args[0])

    def walk_iff(self, expression: FNode, args: list[SMTFNode]) -> SMTFNode:
        return self.manager.Iff(*args)

    def walk_implies(self, expression: FNode, args: list[SMTFNode]) -> SMTFNode:
        return self.manager.Implies(*args)

    def walk_equals(self, expression: FNode, args: list[SMTFNode]) -> SMTFNode:
        return self.manager.Equals(*args)

    def walk_le(self, expression: FNode, args: list[SMTFNode]) -> SMTFNode:
        return self.manager.LE(*args)

    def walk_lt(self, expression: FNode, args: list[SMTFNode]) -> SMTFNode:
        return self.manager.LT(*args)

    def walk_plus(self, expression: FNode, args: list[SMTFNode]) -> SMTFNode:
        return self.manager.Plus(args)

    def walk_minus(self, expression: FNode, args: list[SMTFNode]) -> SMTFNode:
        return self.manager.Minus(*args)

    def walk_times(self, expression: FNode, args: list[SMTFNode]) -> SMTFNode:
        return self.manager.Times(args)

    def walk_div(self, expression: FNode, args: list[SMTFNode]) -> SMTFNode:
        return self.manager.Div(*args)
