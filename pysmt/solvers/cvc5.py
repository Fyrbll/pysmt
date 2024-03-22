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
from __future__ import absolute_import

from pysmt.exceptions import SolverAPINotFound

try:
    import cvc5
except ImportError:
    raise SolverAPINotFound

import pysmt.typing as types
from pysmt.logics import PYSMT_LOGICS, ARRAYS_CONST_LOGICS

from pysmt.solvers.solver import Solver, Converter, SolverOptions, UnsatCoreSolver
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              InternalSolverError,
                              NonLinearError, PysmtValueError,
                              PysmtTypeError)
from pysmt.walkers import DagWalker
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.solvers.eager import EagerModel
from pysmt.decorators import catch_conversion_error
from pysmt.constants import Fraction, is_pysmt_integer, to_python_integer


class Cvc5Options(SolverOptions):
    @staticmethod
    def _set_option(cvc5_solver, name, value):
        try:
            cvc5_solver.setOption(name, value)
        except:
            raise PysmtValueError("Error setting the option '%s = %s'" % (name, value))
# EOC Cvc5Options


class Cvc5Solver(Solver, UnsatCoreSolver, SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = PYSMT_LOGICS

    OptionsClass = Cvc5Options

    def __init__(self, environment, logic, **options):
        Solver.__init__(self, environment = environment, logic = logic, **options)
        self.cvc5_solver = cvc5.Solver()
        self.declarations = None
        self.logic_name = str(logic)
        self.reset_assertions()
        self.converter = Cvc5Converter(environment, self.cvc5_solver)
        return None


    def reset_assertions(self):
        self.cvc5_solver.resetAssertions()
        return None


    def declare_variable(self, var):
        raise NotImplementedError()


    def add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)
        term = self.converter.convert(formula)
        self.cvc5_solver.assertFormula(term)
        return None


    def get_model(self):
        assignment = {}
  
        for s in self.environment.formula_manager.get_all_symbols():
            if s.is_term():
                if s.symbol_type().is_custom_type():
                    continue

                v = self.get_value(s)

                assignment[s] = v

        return EagerModel(assignment = assignment, environment = self.environment)


    def solve(self, assumptions = None):
        if assumptions is not None:
            conj_assumptions = self.environment.formula_manager.And(assumptions)
            cvc5_assumption = self.converter.convert(conj_assumptions)
            res = self.cvc5_solver.checkSatAssuming(cvc5_assumption)

        else:
            try:
                res = self.cvc5_solver.checkSat()
            except:
                raise InternalSolverError()

        if res.isUnknown():
            raise SolverReturnedUnknownResultError()
        else:
            self.last_result = res.isSat()
            self.last_command = "solve"
            return self.last_result


    def push(self, levels = 1):
        self.cvc5_solver.push(levels)
        return None


    def pop(self, levels = 1):
        self.cvc5_solver.pop(levels)
        return None


    def print_model(self, name_filter=None):
        if name_filter is None:
            var_set = self.declarations
        else:
            var_set = (var for var in self.declarations if name_filter(var))

        for var in var_set:
            print("%s = %s", (var.symbol_name(), self.get_value(var)))

        return None


    def get_value(self, item):
        self._assert_no_function_type(item)

        term = self.converter.convert(item)

        cvc5_res = self.cvc5_solver.getValue(term)

        res = self.converter.back(cvc5_res)

        if self.environment.stc.get_type(item).is_real_type() and \
           self.environment.stc.get_type(res).is_int_type():
            res = self.environment.formula_manager.Real(Fraction(res.constant_value(), 1))

        return res

    def _named_assertions_map(self):
        return dict((t[0], (t[1],t[2])) for t in self.assertions)
    

    # def get_named_unsat_core(self):
    #     """After a call to solve() yielding UNSAT, returns the unsat core as a
    #     dict of names to formulae"""
    # 
    #     if self.last_result is not False:
    #         raise SolverStatusError("The last call to solve() was not unsatisfiable")
    # 
    #     if self.last_command != "solve":
    #         raise SolverStatusError("The solver status has been modified by a '%s' command after the last call to solve()" % self.last_command)
    # 
    #     assumptions = self.cvc5_solver.getUnsatCore()
    # 
    #     pysmt_assumptions = set(self.converter.back(t) for t in assumptions)
    # 
    #     res = {}
    # 
    #     n_ass_map = self._named_assertions_map()
    # 
    #     cnt = 0
    # 
    #     for key in pysmt_assumptions:
    #         if key in n_ass_map:
    #             (name, formula) = n_ass_map[key]
    #             if name is None:
    #                 name = "_a_%d" % cnt
    #                 cnt += 1
    #             res[name] = formula
    # 
    #     return res


    def get_unsat_core(self):
        """After a call to solve() yielding UNSAT, returns the unsat core as a
        set of formulae"""

        assumptions = self.cvc5_solver.getUnsatCore()
        pysmt_assumptions = set(self.converter.back(t) for t in assumptions)
        return pysmt_assumptions

        # return self.get_named_unsat_core().values()


    def _exit(self):
        del self.cvc5_solver


    def set_option(self, name, value):
        """Sets an option.

        :param name and value: Option to be set
        :type name: String
        :type value: String
        """
        self.cvc5_solver.setOption(name, value)
        return None

class Cvc5Converter(Converter, DagWalker):


    def __init__(self, environment, cvc5_solver):
        DagWalker.__init__(self, environment)

        self.cvc5_solver = cvc5_solver
        self.declared_vars = {}
        self.backconversion = {}
        self.environment = environment
        self.mgr = environment.formula_manager
        self._get_type = environment.stc.get_type

        return None


    def declare_variable(self, var):
        if not(var.is_symbol()):
            raise PysmtTypeError("Trying to declare as a variable something that is not a symbol")
        
        if var.symbol_name() not in self.declared_vars:
            cvc5_type = self._type_to_cvc5(var.symbol_type())
            decl = self.cvc5_solver.mkConst(cvc5_type, var.symbol_name())
            self.declared_vars[var] = decl


    def back(self, expr):
        res = None

        K = cvc5.Kind
        k = expr.getKind()
        if k == K.CONST_BOOLEAN:
            res = self.mgr.Bool(expr.toPythonObj())
        elif k == K.CONST_INTEGER or\
             k == K.CONST_RATIONAL or\
             k == K.CONST_FLOATINGPOINT:
            res = self.mgr.Real(Fraction(expr.toPythonObj()))
        elif k == K.ADD:
            res = self.mgr.Plus([self.back(subexpr) for subexpr in expr])
        elif k == K.AND:
            res = self.mgr.And([self.back(subexpr) for subexpr in expr])
        elif k == K.CONSTANT:
            res = self.mgr.get_symbol(expr.__str__())
        elif k == K.EQUAL:
            res = self.mgr.Equals(self.back(expr[0]), self.back(expr[1]))
        elif k == K.GEQ:
            res = self.mgr.GE(self.back(expr[0]), self.back(expr[1]))
        elif k == K.GT:
            res = self.mgr.GT(self.back(expr[0]), self.back(expr[1]))
        elif k == K.IMPLIES:
            res = self.mgr.Implies(self.back(expr[0]), self.back(expr[1]))
        elif k == K.ITE:
            res = self.mgr.Ite(self.back(expr[0]), self.back(expr[1]), self.back(expr[2]))
        elif k == K.LEQ:
            res = self.mgr.LE(self.back(expr[0]), self.back(expr[1]))
        elif k == K.LT:
            res = self.mgr.LT(self.back(expr[0]), self.back(expr[1]))
        elif k == K.MULT:
            res = self.mgr.Times([self.back(subexpr) for subexpr in expr])
        elif k == K.NEG:
            raise NotImplementedError("arithmetic negation")
        elif k == K.NOT:
            res = self.mgr.Not(self.back(expr[0]))
        elif k == K.OR:
            res = self.mgr.Or([self.back(subexpr) for subexpr in expr])
        elif k == K.SUB:
            res = self.mgr.Minus(self.back(expr[0]), self.back(expr[1]))
        else:
            raise PysmtTypeError("Unsupported expression %s with kind %s" % (expr, expr.getKind()))

        return res

    @catch_conversion_error
    def convert(self, formula):
        return self.walk(formula)

    def walk_and(self, formula, args, **kwargs):
        return self.cvc5_solver.mkTerm(cvc5.Kind.AND, *args)

    def walk_or(self, formula, args, **kwargs):
        return self.cvc5_solver.mkTerm(cvc5.Kind.OR, *args)

    def walk_not(self, formula, args, **kwargs):
        return self.cvc5_solver.mkTerm(cvc5.Kind.NOT, args[0])

    def walk_symbol(self, formula, args, **kwargs):
        if formula not in self.declared_vars:
            self.declare_variable(formula)

        return self.declared_vars[formula]

    def walk_iff(self, formula, args, **kwargs):
        return self.cvc5_solver.mkTerm(cvc5.Kind.EQUAL, args[0], args[1])

    def walk_implies(self, formula, args, **kwargs):
        return self.cvc5_solver.mkTerm(cvc5.Kind.IMPLIES, args[0], args[1])

    def walk_le(self, formula, args, **kwargs):
        return self.cvc5_solver.mkTerm(cvc5.Kind.LEQ, args[0], args[1])

    def walk_lt(self, formula, args, **kwargs):
        return self.cvc5_solver.mkTerm(cvc5.Kind.LT, args[0], args[1])

    def walk_ite(self, formula, args, **kwargs):
        return self.cvc5_solver.mkTerm(cvc5.Kind.ITE, args[0], args[1], args[2])

    def walk_real_constant(self, formula, **kwargs):
        frac = formula.constant_value()
        return self.cvc5_solver.mkReal(frac.numerator, frac.denominator)

    def walk_bool_constant(self, formula, **kwargs):
        return self.cvc5_solver.mkBoolean(formula.constant_value())

    def walk_plus(self, formula, args, **kwargs):
        return self.cvc5_solver.mkTerm(cvc5.Kind.ADD, *args)

    def walk_minus(self, formula, args, **kwargs):
        return self.cvc5_solver.mkTerm(cvc5.Kind.SUB, args[0], args[1])

    def walk_equals(self, formula, args, **kwargs):
        return self.cvc5_solver.mkTerm(cvc5.Kind.EQUAL, args[0], args[1])

    def walk_times(self, formula, args, **kwargs):
        if sum(1 for x in formula.args() if x.get_free_variables()) > 1:
            raise NonLinearError(formula)

        return self.cvc5_solver.mkTerm(cvc5.Kind.MULT, *args)

    def walk_function(self, formula, args, **kwargs):
        name = formula.function_name()

        if name not in self.declared_vars:
            self.declare_variable(name)

        decl = self.declared_vars[name]

        return self.cvc5_solver.mkTerm(cvc5.Kind.APPLY_UF, decl, *args)

    def walk_toreal(self, formula, args, **kwargs):
        return self.cvc5_solver.mkTerm(cvc5.Kind.TO_REAL, args[0])

    def walk_bv_constant(self, formula, **kwargs):
        raise NotImplementedError()

    def walk_int_constant(self, formula, **kwargs):
        raise NotImplementedError()

    def walk_exists(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_forall(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_array_store(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_array_select(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_ult(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_ule(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_concat(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_extract(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_or(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_not(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_and(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_xor(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_add(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_sub(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_neg(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_mul(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_tonatural(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_udiv(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_urem(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_lshl(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_lshr(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_rol(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_ror(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_zext(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_sext (self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_slt(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_sle(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_comp(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_sdiv(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_srem(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_bv_ashr(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_str_constant(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_str_length (self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_str_concat(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_str_contains(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_str_indexof(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_str_replace(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_str_substr(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_str_prefixof(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_str_suffixof(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_str_to_int(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_int_to_str(self, formula, args, **kwargs):
        raise NotImplementedError()

    def walk_str_charat(self, formula, args, **kwargs):
        raise NotImplementedError()

    def _type_to_cvc5(self, tp):
        if tp.is_bool_type():
            return self.cvc5_solver.getBooleanSort()
        elif tp.is_real_type():
            return self.cvc5_solver.getRealSort()
        elif tp.is_int_type():
            return self.cvc5_solver.getIntegerSort()
        elif tp.is_function_type():
            stps = [self._type_to_cvc5(x) for x in tp.param_types]
            rtp = self._type_to_cvc5(tp.return_type)
            return self.cvc5_solver.mkFunctionSort(stps, rtp)
        else:
            raise NotImplementedError("Unsupported type: %s" %tp)

    def _cvc5_type_to_type(self, type_):
        if type_.isBoolean():
            return types.BOOL
        elif type_.isInteger():
            return types.INT
        elif type_.isReal():
            return types.REAL
        elif type_.isFunction():
            return_type = self._cvc5_type_to_type(type_.getFunctionCodomainSort())
            param_types = tuple(self._cvc5_type_to_type(ty) for ty in type_.getFunctionDomainSorts())
            return types.FunctionType(return_type, param_types)
        else:
            raise NotImplementedError("Unsupported type: %s" % type_)

    def _rename_bound_variables(self, formula, variables):
        """Bounds the variables in formula.

        Returns a tuple (new_formula, new_var_list) in which the old
        variables have been replaced by the new variables in the list.
        """
        # mkBoundVar = self.cvc4_exprMgr.mkBoundVar
        # new_var_list = [mkBoundVar(x.symbol_name(), self._type_to_cvc4(x.symbol_type())) for x in variables]

        new_var_list = [self.cvc5_solver.mkVar(self._type_to_cvc5(x.symbol_type()), x.symbol_name()) for x in variables]
        old_var_list = [self.walk_symbol(x, []) for x in variables]
        new_formula = formula.substitute(old_var_list, new_var_list)
        return (new_formula, new_var_list)
