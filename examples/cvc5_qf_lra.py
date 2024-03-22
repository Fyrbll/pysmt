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

from pysmt.shortcuts import UnsatCoreSolver
from pysmt.smtlib.parser import SmtLibParser
from io import StringIO


def ask_cvc5(formula):
    with UnsatCoreSolver(name = "cvc5", logic = "QF_LRA") as solver:
        solver.set_option("produce-models", "true")
        solver.set_option("produce-unsat-cores", "true")
        solver.set_option("minimal-unsat-cores", "true")
    
        if formula.is_and():
            for conjunct in formula.args():
                solver.add_assertion(conjunct)

        if solver.solve():
            print("sat, with model ", end = "")
            print(solver.get_model())
        else:
            print("unsat, with core ", end = "")
            print(solver.get_unsat_core())


sat_source = """\
(set-logic QF_LRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(assert (< x1 x2))
(assert (< x2 x3))
(assert (< x3 x4))
(assert (= (+ x1 x2 x3 x4) 17))
(assert (= (+ (* 4 x1) (* 3 x2) (* 2 x3) (* (- 0 1) x4)) 20))
(check-sat)
"""


unsat_source = """\
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (or (< x 0) (> x 0)))
(assert (=> (< x 0) (< y 0)))
(assert (=> (> x 0) (> y 0)))
(assert (= z 0))
(assert (= (+ x y z) z))
(check-sat)
"""


smt_lib_parser = SmtLibParser()


print("For satisfiable query, ")
sat_script = smt_lib_parser.get_script(StringIO(sat_source))
sat_query = sat_script.get_last_formula()
ask_cvc5(sat_query)
print()

print("For unsatisfiable query, ")
unsat_script = smt_lib_parser.get_script(StringIO(unsat_source))
unsat_query = unsat_script.get_last_formula()
ask_cvc5(unsat_query)
