# Mockup optimizer that only prints the problem as SMTLIB2

import sys
from pysmt.optimization.goal import MaxSMTGoal, MinMaxGoal
from pysmt.optimization.optimizer import Optimizer
from pysmt.smtlib.script import SmtLibCommand
from pysmt.smtlib.solver import SmtLibSolver

import pysmt.smtlib.commands as smtcmd
from pysmt.logics import PYSMT_LOGICS

from pysmt.solvers.solver import Model

class MockupModel(Model):

    def __init__(self, environment):
        Model.__init__(self, environment)

    def get_value(self, formula, model_completion=True):
        return self.environment.formula_manager.TRUE()

    # def iterator_over(self, language):
    #     for x in language:
    #         yield x, self.get_value(x, model_completion=True)

    # def __iter__(self):
    #     """Overloading of iterator from Model.  We iterate only on the
    #     variables defined in the assignment.
    #     """
    #     return iter(self.assignment.items())

    # def __contains__(self, x):
    #     """Returns whether the model contains a value for 'x'."""
    #     return x in self.assignment


class MockupOMTOptimizer(Optimizer, SmtLibSolver):

    LOGICS = PYSMT_LOGICS

    def __init__(self, environment, logic, **options):
        Optimizer.__init__(self, environment, logic, **options)
        #SmtLibSolver.__init__(self, environment)
        self.output = sys.stdout

        self.to = self.environment.typeso

        self.declared_vars = [set()]
        self.declared_sorts = [set()]

        #self.parser = SmtLibParser(interactive=True)

        # Initialize solver
        self.options(self)
        self.set_logic(logic)

    def _send_command(self, cmd):
        cmd.serialize(self.output, daggify=True)
        self.output.write("\n")
        self.output.flush()

    def _check_success(self):
        return True

    def solve(self, assumptions=None):
        return False

    def get_value(self, x):
        print(x)
        return self.environment.formula_manager.TRUE()

    def get_model(self):
       return MockupModel(self.environment)

    def optimize(self, goal, **kwargs):
        if isinstance(goal, MaxSMTGoal):
            for f,w in goal.soft:
                self._send_command(cmd=SmtLibCommand(smtcmd.ASSERT_SOFT, [f,w]))
        elif isinstance(goal, MinMaxGoal):
            self._send_command(cmd=SmtLibCommand(smtcmd.MINMAX, goal.terms))
        return self.get_model(), 100

    def _exit(self):
        pass
