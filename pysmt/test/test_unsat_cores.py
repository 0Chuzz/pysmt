#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#
from pysmt.test import (TestCase, skipIfSolverNotAvailable,
                        skipIfNoUnsatCoreSolverForLogic, main)
from pysmt.shortcuts import (get_unsat_core, And, Not, Symbol, UnsatCoreSolver,
                             is_unsat)
from pysmt.logics import QF_BOOL, QF_BV
from pysmt.exceptions import SolverStatusError, SolverReturnedUnknownResultError
from pysmt.test.examples import get_example_formulae

class TestUnsatCores(TestCase):

    def _helper_check_examples(self, solver_name):
        for (f, _, satisfiability, logic) in get_example_formulae():
            if not logic.quantifier_free: continue
            if satisfiability == False:
                with UnsatCoreSolver(name=solver_name,
                                     unsat_cores_mode="named") as solver:
                    if logic not in solver.LOGICS: continue
                    clauses = [f]
                    if f.is_and():
                        clauses = f.args()

                    for i,c in enumerate(clauses):
                        solver.add_assertion(c, "a%d" % i)

                    try:
                        r = solver.solve()
                        self.assertFalse(r)
                    except SolverReturnedUnknownResultError:
                        if QF_BV <= logic:
                            continue # Unsat-core support for QF_UFBV might be
                                     # incomplete
                        else:
                            raise

                    core = solver.get_named_unsat_core()

                    self.assertTrue(len(core) <= len(clauses))
                    for k in core.values():
                        self.assertIn(k, clauses)

                    self.assertTrue(is_unsat(And(core.values()), logic=logic))


    @skipIfNoUnsatCoreSolverForLogic(QF_BOOL)
    def test_basic(self):
        x = Symbol("x")
        with UnsatCoreSolver(logic=QF_BOOL) as s:
            s.add_assertion(x)
            s.add_assertion(Not(x))
            r = s.solve()
            self.assertFalse(r)

            core = s.get_unsat_core()
            self.assertEqual(len(core), 2)
            self.assertIn(x, core)
            self.assertIn(Not(x), core)

            named_core = s.get_named_unsat_core()
            self.assertEqual(len(core), 2)
            self.assertIn(x, named_core.values())
            self.assertIn(Not(x), named_core.values())


    @skipIfNoUnsatCoreSolverForLogic(QF_BOOL)
    def test_shortcut(self):
        x = Symbol("x")
        core = get_unsat_core([x, Not(x)])
        self.assertEqual(len(core), 2)
        self.assertIn(x, core)
        self.assertIn(Not(x), core)


    @skipIfNoUnsatCoreSolverForLogic(QF_BOOL)
    def test_basic_named(self):
        x = Symbol("x")
        with UnsatCoreSolver(logic=QF_BOOL, unsat_cores_mode="named") as s:
            s.add_assertion(x, named="a1")
            s.add_assertion(Not(x), named="a2")
            r = s.solve()
            self.assertFalse(r)

            core = s.get_unsat_core()
            self.assertEqual(len(core), 2)
            self.assertIn(x, core)
            self.assertIn(Not(x), core)

            named_core = s.get_named_unsat_core()
            self.assertEqual(len(named_core), 2)
            self.assertIn("a1", named_core)
            self.assertIn("a2", named_core)
            self.assertEqual(named_core["a1"], x)
            self.assertEqual(named_core["a2"], Not(x))


    @skipIfNoUnsatCoreSolverForLogic(QF_BOOL)
    def test_modify_state(self):
        x = Symbol("x")
        with UnsatCoreSolver(logic=QF_BOOL) as s:
            s.add_assertion(x)
            s.push()
            s.add_assertion(Not(x))
            r = s.solve()
            self.assertFalse(r)
            s.pop()
            with self.assertRaises(SolverStatusError):
                s.get_unsat_core()


    @skipIfNoUnsatCoreSolverForLogic(QF_BOOL)
    def test_modify_state_assert(self):
        x = Symbol("x")
        with UnsatCoreSolver(logic=QF_BOOL) as s:
            s.add_assertion(x)
            s.add_assertion(Not(x))
            r = s.solve()
            self.assertFalse(r)
            s.add_assertion(Symbol("y"))
            with self.assertRaises(SolverStatusError):
                s.get_unsat_core()


    @skipIfSolverNotAvailable("msat")
    def test_examples_msat(self):
        self._helper_check_examples("msat")


    @skipIfSolverNotAvailable("z3")
    def test_examples_z3(self):
        self._helper_check_examples("z3")


if __name__ == '__main__':
    main()
