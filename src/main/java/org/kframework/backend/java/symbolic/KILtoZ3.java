// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.kil.Z3Term;
import org.kframework.kil.ASTNode;
import java.util.Set;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Z3Exception;


/**
 * @author: AndreiS
 */
public class KILtoZ3 extends CopyOnWriteTransformer {

    private final Context context;
    private final Set<Variable> boundVariables;

    public KILtoZ3(Set<Variable> boundVariables, Context context) {
        this.boundVariables = boundVariables;
        this.context = context;
    }

    @Override
    public ASTNode transform(BoolToken boolToken) {
        try {
            return new Z3Term(context.mkBool(boolToken.booleanValue()));
        } catch (Z3Exception e) {
            throw new UnsupportedOperationException(e.getMessage(), e.getCause());
        }
    }

    @Override
    public ASTNode transform(IntToken intToken) {
        try {
            return new Z3Term(context.mkInt(intToken.bigIntegerValue().longValue()));
        } catch (Z3Exception e) {
            throw new UnsupportedOperationException(e.getMessage(), e.getCause());
        }
    }

    @Override
    public ASTNode transform(BitVector bitVector) {
        try {
            return new Z3Term(context.mkBV(bitVector.signedValue().longValue(), bitVector.bitwidth()));
        } catch (Z3Exception e) {
            throw new RuntimeException(e.getMessage(), e.getCause());
        }
    }

    @Override
    public ASTNode transform(KItem kItem) {
        if (!(kItem.kLabel() instanceof KLabelConstant)) {
            throw new UnsupportedOperationException();
        }
        KLabelConstant kLabel = (KLabelConstant) kItem.kLabel();

        if (!(kItem.kList() instanceof KList)) {
            throw new UnsupportedOperationException();
        }
        KList kList = (KList) kItem.kList();

        if (kList.hasFrame()) {
            throw new UnsupportedOperationException();
        }

        // TODO(AndreiS): implement a more general mechanic
        try {
            if (kLabel.label().equals("'notBool_") && kList.concreteSize() == 1) {
                BoolExpr booleanExpression
                        = (BoolExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                return new Z3Term(context.mkNot(booleanExpression));
            } else if (kLabel.label().equals("'_andBool_") && kList.concreteSize() == 2) {
                BoolExpr[] booleanExpressions = {
                        (BoolExpr) ((Z3Term) kList.get(0).accept(this)).expression(),
                        (BoolExpr) ((Z3Term) kList.get(1).accept(this)).expression()};
                return new Z3Term(context.mkAnd(booleanExpressions));
            } else if (kLabel.label().equals("'_orBool_") && kList.concreteSize() == 2) {
                BoolExpr[] booleanExpressions = {
                        (BoolExpr) ((Z3Term) kList.get(0).accept(this)).expression(),
                        (BoolExpr) ((Z3Term) kList.get(1).accept(this)).expression()};
                return new Z3Term(context.mkOr(booleanExpressions));
            } else if (kLabel.label().equals("'_==Bool_") && kList.concreteSize() == 2) {
                BoolExpr booleanExpression1
                        = (BoolExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                BoolExpr booleanExpression2
                        = (BoolExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkEq(booleanExpression1, booleanExpression2));
            } else if (kLabel.label().equals("'_=/=Bool_") && kList.concreteSize() == 2) {
                BoolExpr booleanExpression1
                        = (BoolExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                BoolExpr booleanExpression2
                        = (BoolExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkNot(context.mkEq(
                        booleanExpression1,
                        booleanExpression2)));
            } else if (kLabel.label().equals("'_+Int_") && kList.concreteSize() == 2) {
                ArithExpr[] arithmeticExpressions = {
                        (ArithExpr) ((Z3Term) kList.get(0).accept(this)).expression(),
                        (ArithExpr) ((Z3Term) kList.get(1).accept(this)).expression()};
                return new Z3Term(context.mkAdd(arithmeticExpressions));
            } else if (kLabel.label().equals("'_-Int_") && kList.concreteSize() == 2) {
                ArithExpr[] arithmeticExpressions = {
                        (ArithExpr) ((Z3Term) kList.get(0).accept(this)).expression(),
                        (ArithExpr) ((Z3Term) kList.get(1).accept(this)).expression()};
                return new Z3Term(context.mkSub(arithmeticExpressions));
            } else if (kLabel.label().equals("'_*Int_") && kList.concreteSize() == 2) {
                ArithExpr[] arithmeticExpressions = {
                        (ArithExpr) ((Z3Term) kList.get(0).accept(this)).expression(),
                        (ArithExpr) ((Z3Term) kList.get(1).accept(this)).expression()};
                return new Z3Term(context.mkMul(arithmeticExpressions));
            } else if (kLabel.label().equals("'_/Int_") && kList.concreteSize() == 2) {
                ArithExpr arithmeticExpression1
                        = (ArithExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                ArithExpr arithmeticExpression2
                        = (ArithExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkDiv(arithmeticExpression1, arithmeticExpression2));
            } else if (kLabel.label().equals("'_>Int_") && kList.concreteSize() == 2) {
                ArithExpr arithmeticExpression1
                        = (ArithExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                ArithExpr arithmeticExpression2
                        = (ArithExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkGt(arithmeticExpression1, arithmeticExpression2));
            } else if (kLabel.label().equals("'_>=Int_") && kList.concreteSize() == 2) {
                ArithExpr arithmeticExpression1
                        = (ArithExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                ArithExpr arithmeticExpression2
                        = (ArithExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkGe(arithmeticExpression1, arithmeticExpression2));
            } else if (kLabel.label().equals("'_<Int_") && kList.concreteSize() == 2) {
                ArithExpr arithmeticExpression1
                        = (ArithExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                ArithExpr arithmeticExpression2
                        = (ArithExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkLt(arithmeticExpression1, arithmeticExpression2));
            } else if (kLabel.label().equals("'_<=Int_") && kList.concreteSize() == 2) {
                ArithExpr arithmeticExpression1
                        = (ArithExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                ArithExpr arithmeticExpression2
                        = (ArithExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkLe(arithmeticExpression1, arithmeticExpression2));
            } else if (kLabel.label().equals("'_==Int_") && kList.concreteSize() == 2) {
                ArithExpr arithmeticExpression1
                        = (ArithExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                ArithExpr arithmeticExpression2
                        = (ArithExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkEq(arithmeticExpression1, arithmeticExpression2));
            } else if (kLabel.label().equals("'_=/=Int_") && kList.concreteSize() == 2) {
                ArithExpr arithmeticExpression1
                        = (ArithExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                ArithExpr arithmeticExpression2
                        = (ArithExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkNot(context.mkEq(
                        arithmeticExpression1,
                        arithmeticExpression2)));
            } else if (kLabel.label().equals("'_==K_") && kList.concreteSize() == 2) {
                Expr expression1 = ((Z3Term) kList.get(0).accept(this)).expression();
                Expr expression2 = ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkEq(expression1, expression2));
            } else if (kLabel.label().equals("'_=/=K_") && kList.concreteSize() == 2) {
                Expr expression1 = ((Z3Term) kList.get(0).accept(this)).expression();
                Expr expression2 = ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkNot(context.mkEq(expression1, expression2)));

            } else if (kLabel.label().equals("'[E]K_._") && kList.concreteSize() == 2) {
                Expr expression1 = (ArithExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                Expr expression2 = (BoolExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                Expr[] newExpr = new Expr[1];
                newExpr[0] = expression1;
                return new Z3Term(context.mkExists(newExpr, expression2, 1, null, null, null, null));

            } else if (kLabel.label().equals("'[A]K_._") && kList.concreteSize() == 2) {
                Expr expression1 = (ArithExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                Expr expression2 = (BoolExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                Expr[] newExpr = new Expr[1];
                newExpr[0] = expression1;
                return new Z3Term(context.mkForall(newExpr, expression2, 1, null, null, null, null));
            } else if (kLabel.label().equals("'extractMInt")) {
                BitVecExpr bitvectorExpression = (BitVecExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                int beginIndex = ((IntToken) kList.get(1)).intValue();
                int endIndex = ((IntToken) kList.get(2)).intValue() - 1;
                return new Z3Term(context.mkExtract(endIndex, beginIndex, bitvectorExpression));
            } else if (kLabel.label().equals("'concatenateMInt")) {
                BitVecExpr bitvectorExpression1 = (BitVecExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                BitVecExpr bitvectorExpression2 = (BitVecExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                // reverse order for arguments
                return new Z3Term(context.mkConcat(bitvectorExpression2, bitvectorExpression1));
            } else if (kLabel.label().equals("'addMInt")) {
                BitVecExpr bitvectorExpression1 = (BitVecExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                BitVecExpr bitvectorExpression2 = (BitVecExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkBVAdd(bitvectorExpression1, bitvectorExpression2));
            } else if (kLabel.label().equals("'subMInt")) {
                BitVecExpr bitvectorExpression1 = (BitVecExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                BitVecExpr bitvectorExpression2 = (BitVecExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkBVSub(bitvectorExpression1, bitvectorExpression2));
            } else if (kLabel.label().equals("'mulMInt")) {
                BitVecExpr bitvectorExpression1 = (BitVecExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                BitVecExpr bitvectorExpression2 = (BitVecExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkBVMul(bitvectorExpression1, bitvectorExpression2));
            } else if (kLabel.label().equals("'udivMInt")) {
                BitVecExpr bitvectorExpression1 = (BitVecExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                BitVecExpr bitvectorExpression2 = (BitVecExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkBVUDiv(bitvectorExpression1, bitvectorExpression2));
            } else if (kLabel.label().equals("'xorMInt")) {
                BitVecExpr bitvectorExpression1 = (BitVecExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                BitVecExpr bitvectorExpression2 = (BitVecExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkBVXOR(bitvectorExpression1, bitvectorExpression2));
            } else if (kLabel.label().equals("'ultMInt")) {
                BitVecExpr bitvectorExpression1 = (BitVecExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                BitVecExpr bitvectorExpression2 = (BitVecExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkBVULT(bitvectorExpression1, bitvectorExpression2));
            } else if (kLabel.label().equals("'eqMInt")) {
                BitVecExpr bitvectorExpression1 = (BitVecExpr) ((Z3Term) kList.get(0).accept(this)).expression();
                BitVecExpr bitvectorExpression2 = (BitVecExpr) ((Z3Term) kList.get(1).accept(this)).expression();
                return new Z3Term(context.mkEq(bitvectorExpression1, bitvectorExpression2));
            } else {
                throw new UnsupportedOperationException("cannot translate term to Z3 format " + kItem);
            }
        } catch (ClassCastException | ArithmeticException e) {
            throw new UnsupportedOperationException(e.getMessage(), e.getCause());
        } catch (Z3Exception e) {
            throw new UnsupportedOperationException(e.getMessage(), e.getCause());
        }
    }

    @Override
    public ASTNode transform(Variable variable) {
        return KILtoZ3.valueOf(variable, context);
    }

    public static Z3Term valueOf(Variable variable, Context context) {
        try {
            if (variable.sort().equals(BoolToken.SORT)) {
                //if (boundVariables.contains(variable)) {}
                return new Z3Term(context.mkBoolConst(variable.name()));
            } else if (variable.sort().equals(IntToken.SORT)) {
                return new Z3Term(context.mkIntConst(variable.name()));
            } else if (variable.sort().equals(BitVector.SORT)) {
                return new Z3Term(context.mkBVConst(variable.name(), BitVector.getBitwidthOrDie(variable)));
            } else {
                throw new UnsupportedOperationException("cannot translate term to Z3 format " + variable);
            }
        } catch (Z3Exception e) {
            throw new UnsupportedOperationException(e.getMessage(), e.getCause());
        }
    }

}
