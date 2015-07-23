#
# This file is part of pySMT.
#
#   Copyright 2015 Andrea Micheli and Marco Gario
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
import boolector

from pysmt.solvers.solver import (IncrementalTrackingSolver, UnsatCoreSolver,
                                  Model, Converter)
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin

from pysmt.walkers import DagWalker
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              SolverNotConfiguredForUnsatCoresError,
                              SolverStatusError,
                              ConvertExpressionError)
from pysmt.decorators import clear_pending_pop, catch_conversion_error
from pysmt.logics import QF_BV
from pysmt.oracles import get_logic



class BoolectorSolver(IncrementalTrackingSolver,
                      SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = [QF_BV]

    def __init__(self, environment, logic, user_options):
        IncrementalTrackingSolver.__init__(self,
                                           environment=environment,
                                           logic=logic,
                                           user_options=user_options)

        self.btor = boolector.Boolector()
        self.btor.Set_opt("model_gen", 1)
        self.converter = BTORConverter(environment, self)
        self.mgr = environment.formula_manager
        self.declarations = {}
        return

    @clear_pending_pop
    def _reset_assertions(self):
        raise NotImplementedError

    @clear_pending_pop
    def declare_variable(self, var):
        raise NotImplementedError
        self.declarations.add(var)
        return

    @clear_pending_pop
    def _add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)
        term = self.converter.convert(formula)
        self.btor.Assert(term)

    def get_model(self):
        raise NotImplementedError

    @clear_pending_pop
    def _solve(self, assumptions=None):
        # self.btor.Assume(...)
        return self.btor.Sat()

    def get_unsat_core(self):
        raise NotImplementedError

    @clear_pending_pop
    def _push(self, levels=1):
        raise NotImplementedError

    @clear_pending_pop
    def _pop(self, levels=1):
        raise NotImplementedError

    def print_model(self, name_filter=None):
        for var in self.declarations:
            if name_filter is None or not var.symbol_name().startswith(name_filter):
                print("%s = %s" % (var.symbol_name(), self.get_value(var)))


    def get_value(self, item):
        self._assert_no_function_type(item)
        titem = self.converter.convert(item)
        res = titem.assignment
        r = self.converter.back(res)
        return r

    def exit(self):
        if not self._destroyed:
            self._destroyed = True
            del self.btor


class BTORConverter(Converter, DagWalker):

    def __init__(self, environment, btor):
        DagWalker.__init__(self, environment)
        self.mgr = environment.formula_manager
        self._get_type = environment.stc.get_type
        self._back_memoization = {}
        self.btor = btor
        return

    @catch_conversion_error
    def convert(self, formula):
        return self.walk(formula)

    def back(self, expr):
        stack = [expr]
        while len(stack) > 0:
            current = stack.pop()
            key = askey(current)
            if key not in self._back_memoization:
                self._back_memoization[key] = None
                stack.append(current)
                for child in current.children():
                    stack.append(child)
            elif self._back_memoization[key] is None:
                args = [self._back_memoization[askey(c)]
                        for c in current.children()]
                res = self._back_single_term(current, args)
                self._back_memoization[key] = res
            else:
                # we already visited the node, nothing else to do
                pass
        return self._back_memoization[askey(expr)]


    # def _back_single_term(self, expr, args):
    #     assert z3.is_expr(expr)

    #     if z3.is_quantifier(expr):
    #         raise NotImplementedError(
    #             "Quantified back conversion is currently not supported")

    #     res = None
    #     if z3.is_and(expr):
    #         res = self.mgr.And(args)
    #     elif z3.is_or(expr):
    #         res = self.mgr.Or(args)
    #     elif z3.is_add(expr):
    #         res = self.mgr.Plus(args)
    #     elif z3.is_div(expr):
    #         res = self.mgr.Div(args[0], args[1])
    #     elif z3.is_eq(expr):
    #         if self._get_type(args[0]).is_bool_type():
    #             res = self.mgr.Iff(args[0], args[1])
    #         else:
    #             res = self.mgr.Equals(args[0], args[1])
    #     elif z3.is_iff(expr):
    #         res = self.mgr.Iff(args[0], args[1])
    #     elif z3.is_xor(expr):
    #         res = self.mgr.Xor(args[0], args[1])
    #     elif z3.is_false(expr):
    #         res = self.mgr.FALSE()
    #     elif z3.is_true(expr):
    #         res = self.mgr.TRUE()
    #     elif z3.is_gt(expr):
    #         res = self.mgr.GT(args[0], args[1])
    #     elif z3.is_ge(expr):
    #         res = self.mgr.GE(args[0], args[1])
    #     elif z3.is_lt(expr):
    #         res = self.mgr.LT(args[0], args[1])
    #     elif z3.is_le(expr):
    #         res = self.mgr.LE(args[0], args[1])
    #     elif z3.is_mul(expr):
    #         res = self.mgr.Times(args[0], args[1])
    #     elif z3.is_uminus(expr):
    #         tp = self._get_type(args[0])
    #         if tp.is_real_type():
    #             minus_one = self.mgr.Real(-1)
    #         else:
    #             assert tp.is_int_type()
    #             minus_one = self.mgr.Int(-1)
    #         res = self.mgr.Times(args[0], minus_one)
    #     elif z3.is_sub(expr):
    #         res = self.mgr.Minus(args[0], args[1])
    #     elif z3.is_not(expr):
    #         res = self.mgr.Not(args[0])
    #     elif z3.is_implies(expr):
    #         res = self.mgr.Implies(args[0], args[1])
    #     elif z3.is_quantifier(expr):
    #         raise NotImplementedError
    #     elif z3.is_const(expr):
    #         if z3.is_rational_value(expr):
    #             n = expr.numerator_as_long()
    #             d = expr.denominator_as_long()
    #             f = Fraction(n, d)
    #             res = self.mgr.Real(f)
    #         elif z3.is_int_value(expr):
    #             n = expr.as_long()
    #             res = self.mgr.Int(n)
    #         elif z3.is_bv_value(expr):
    #             n = expr.as_long()
    #             w = expr.size()
    #             res = self.mgr.BV(n, w)
    #         else:
    #             # it must be a symbol
    #             res = self.mgr.get_symbol(str(expr))
    #     elif z3.is_ite(expr):
    #         res = self.mgr.Ite(args[0], args[1], args[2])
    #     elif z3.is_function(expr):
    #         res = self.mgr.Function(self.mgr.get_symbol(expr.decl().name()), args)
    #     elif z3.is_to_real(expr):
    #         res = self.mgr.ToReal(args[0])
    #     elif z3.is_bv_and(expr):
    #         res = self.mgr.BVAnd(args[0], args[1])
    #     elif z3.is_bv_or(expr):
    #         res = self.mgr.BVOr(args[0], args[1])
    #     elif z3.is_bv_xor(expr):
    #         res = self.mgr.BVXor(args[0], args[1])
    #     elif z3.is_bv_not(expr):
    #         res = self.mgr.BVNot(args[0])
    #     elif z3.is_bv_neg(expr):
    #         res = self.mgr.BVNeg(args[0])
    #     elif z3.is_bv_concat(expr):
    #         res = self.mgr.BVConcat(args[0], args[1])
    #     elif z3.is_bv_ult(expr):
    #         res = self.mgr.BVULT(args[0], args[1])
    #     elif z3.is_bv_uleq(expr):
    #         res = self.mgr.BVULE(args[0], args[1])
    #     elif z3.is_bv_slt(expr):
    #         res = self.mgr.BVSLT(args[0], args[1])
    #     elif z3.is_bv_sleq(expr):
    #         res = self.mgr.BVSLE(args[0], args[1])
    #     elif z3.is_bv_ugt(expr):
    #         res = self.mgr.BVUGT(args[0], args[1])
    #     elif z3.is_bv_ugeq(expr):
    #         res = self.mgr.BVUGE(args[0], args[1])
    #     elif z3.is_bv_sgt(expr):
    #         res = self.mgr.BVSGT(args[0], args[1])
    #     elif z3.is_bv_sgeq(expr):
    #         res = self.mgr.BVSGE(args[0], args[1])
    #     elif z3.is_bv_extract(expr):
    #         end = z3.get_payload(expr, 0)
    #         start = z3.get_payload(expr, 1)
    #         res = self.mgr.BVExtract(args[0], start, end)
    #     elif z3.is_bv_add(expr):
    #         res = self.mgr.BVAdd(args[0], args[1])
    #     elif z3.is_bv_mul(expr):
    #         res = self.mgr.BVMul(args[0], args[1])
    #     elif z3.is_bv_udiv(expr):
    #         res = self.mgr.BVUDiv(args[0], args[1])
    #     elif z3.is_bv_sdiv(expr):
    #         res = self.mgr.BVSDiv(args[0], args[1])
    #     elif z3.is_bv_urem(expr):
    #         res = self.mgr.BVURem(args[0], args[1])
    #     elif z3.is_bv_srem(expr):
    #         res = self.mgr.BVSRem(args[0], args[1])
    #     elif z3.is_bv_lshl(expr):
    #         res = self.mgr.BVLShl(args[0], args[1])
    #     elif z3.is_bv_lshr(expr):
    #         res = self.mgr.BVLShr(args[0], args[1])
    #     elif z3.is_bv_ashr(expr):
    #         res = self.mgr.BVAShr(args[0], args[1])
    #     elif z3.is_bv_sub(expr):
    #         res = self.mgr.BVSub(args[0], args[1])
    #     elif z3.is_bv_rol(expr):
    #         amount = z3.get_payload(expr, 0)
    #         res = self.mgr.BVRol(args[0], amount)
    #     elif z3.is_bv_ror(expr):
    #         amount = z3.get_payload(expr, 0)
    #         res = self.mgr.BVRor(args[0], amount)
    #     elif z3.is_bv_ext_rol(expr):
    #         amount = args[1].bv_unsigned_value()
    #         res = self.mgr.BVRol(args[0], amount)
    #     elif z3.is_bv_ext_ror(expr):
    #         amount = args[1].bv_unsigned_value()
    #         res = self.mgr.BVRor(args[0], amount)
    #     elif z3.is_bv_sext(expr):
    #         amount = z3.get_payload(expr, 0)
    #         res = self.mgr.BVSExt(args[0], amount)
    #     elif z3.is_bv_zext(expr):
    #         amount = z3.get_payload(expr, 0)
    #         res = self.mgr.BVZExt(args[0], amount)

    #     if res is None:
    #         raise ConvertExpressionError(message=("Unsupported expression: %s" %
    #                                                str(expr)),
    #                                      expression=expr)
    #     return res


    def walk_and(self, formula, args, **kwargs):
        #pylint: disable=star-args
        self.btor.And(*args)

    def walk_or(self, formula, args, **kwargs):
        #pylint: disable=star-args
        return self.btor.Or(*args)

    def walk_not(self, formula, args, **kwargs):
        return self.btor.Not(args[0])

    def walk_symbol(self, formula, **kwargs):
        symbol_type = formula.symbol_type()
        if symbol_type.is_bool_type():
            res = self.btor.Var(1, formula.symbol_name())
        elif symbol_type.is_real_type():
            raise ConvertExpressionError
        elif symbol_type.is_int_type():
            raise ConvertExpressionError
        else:
            assert symbol_type.is_bv_type()
            res = self.btor.Var(formula.bv_width(),
                                formula.symbol_name())
        return res

    def walk_iff(self, formula, args, **kwargs):
        return self.btor.Iff(*args)

    def walk_implies(self, formula, args, **kwargs):
        return self.btor.Implies(*args)

    def walk_ite(self, formula, args, **kwargs):
        raise ConvertExpressionError

    def walk_bool_constant(self, formula, **kwargs):
        return self.btor.Const(formula.constant_value())

    def walk_equals(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_function(self, formula, args, **kwargs):
        #pylint: disable=star-args
        raise NotImplementedError
        f = formula.function_name()
        tp = f.symbol_type()
        sig = [self._type_to_z3(x) for x in tp.param_types]
        sig.append(self._type_to_z3(tp.return_type))
        z3_f = z3.Function(f.symbol_name(), *sig)
        return z3_f(*args)

    def walk_bv_constant(self, formula, **kwargs):
        value = formula.constant_value()
        width = formula.bv_width()
        return self.btor.Var(value, width)

    def walk_bv_ult(self, formula, args, **kwargs):
        return self.btor.Ult(args[0], args[1])

    def walk_bv_ule(self, formula, args, **kwargs):
        return self.btor.Ulte(args[0], args[1])

    def walk_bv_concat(self, formula, args, **kwargs):
        return self.btor.Concat(args[0], args[1])

    def walk_bv_extract(self, formula, args, **kwargs):
        return args[0][formula.bv_extract_start:formula.bv_extract_end]

    def walk_bv_or(self, formula, args, **kwargs):
        return self.walk_or(formula, args, **kwargs)

    def walk_bv_not(self, formula, args, **kwargs):
        return self.walk_not(formula, args, **kwargs)

    def walk_bv_and(self, formula, args, **kwargs):
        return self.walk_and(formula, args, **kwargs)

    def walk_bv_xor(self, formula, args, **kwargs):
        return self.btor.Xor(*args)

    def walk_bv_add(self, formula, args, **kwargs):
        return self.btor.Add(args[0], args[1])

    def walk_bv_sub(self, formula, args, **kwargs):
        return self.btor.Sub(args[0], args[1])

    def walk_bv_neg(self, formula, args, **kwargs):
        return -args[0]

    def walk_bv_mul(self, formula, args, **kwargs):
        return args[0]*args[1]

    def walk_bv_udiv(self, formula, args, **kwargs):
        return args[0] / args[1]

    def walk_bv_urem(self, formula, args, **kwargs):
        return z3.args[0] % args[1]

    def walk_bv_lshl(self, formula, args, **kwargs):
        return args[0] << args[1]

    def walk_bv_lshr(self, formula, args, **kwargs):
        return args[0] >> args[1]

    def walk_bv_rol(self, formula, args, **kwargs):
        return self.btor.Rol(args[0],
                             formula.bv_rotation_step())

    def walk_bv_ror(self, formula, args, **kwargs):
        return self.btor.Ror(args[0],
                             formula.bv_rotation_step())

    def walk_bv_zext(self, formula, args, **kwargs):
        return self.btor.Uext(args[0], formula.bv_extend_step())

    def walk_bv_sext (self, formula, args, **kwargs):
        return self.btor.Sext(args[0], formula.bv_extend_step())

    def walk_bv_slt(self, formula, args, **kwargs):
        return self.btor.Slt(args[0], args[1])

    def walk_bv_sle (self, formula, args, **kwargs):
        return self.btor.Sle(args[0], args[1])

    def walk_bv_comp (self, formula, args, **kwargs):
        raise NotImplementedError
        return z3.If(args[0] == args[1], z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

    def walk_bv_sdiv (self, formula, args, **kwargs):
        return self.btor.Sdiv(args[0], args[1])

    def walk_bv_srem (self, formula, args, **kwargs):
        return self.btor.Srem(args[0], args[1])

    def walk_bv_ashr (self, formula, args, **kwargs):
        return self.btor.Sra(args[0], formula.bv_rotation_step())

    def _type_to_z3(self, tp):
        if tp.is_bool_type():
            return self.btor.BoolSort()
        elif tp.is_real_type():
            raise ConvertExpressionError
        elif tp.is_int_type():
            raise ConvertExpressionError
        else:
            assert tp.is_bv_type() , "Unsupported type '%s'" % tp
            return self.btor.BitVecSort(tp.width)
