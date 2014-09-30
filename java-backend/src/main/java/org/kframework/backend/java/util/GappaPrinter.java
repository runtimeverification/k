// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.symbolic.BottomUpVisitor;
import org.kframework.backend.java.symbolic.SymbolicConstraint;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * @author Traian
 */
public class GappaPrinter extends BottomUpVisitor {

    public static String intervalOp = "'_<=Float_<=Float_";
    private static String unaryMinusOp = "'--Float_";
    private static String absOp = "'absFloat";

    public static Map<String,String> comparisonOps = new HashMap<String, String>();
    static {
        comparisonOps.put("'_>=Float_", ">=");
        comparisonOps.put("'_<=Float_", "<=");
    }

    public static  Map<String,String> reverseComparisonOps = new HashMap<String, String>();
    static {
        reverseComparisonOps.put("'_>=Float_", "'_<=Float_");
        reverseComparisonOps.put("'_<=Float_", "'_>=Float_");
        reverseComparisonOps.put(">=", "<=");
        reverseComparisonOps.put("<=", ">=");
    };


       public static Map<String,String> binaryOps = new HashMap<String, String>();
    static {
        comparisonOps.put("'_>=Float_", ">=");
        comparisonOps.put("'_<=Float_", "<=");
        comparisonOps.put("'_>Float_", ">=");
        comparisonOps.put("'_<Float_", "<=");
        binaryOps.put("'_+Float_", "+");
        binaryOps.put("'_-Float_", "-");
        binaryOps.put("'_*Float_", "*");
        binaryOps.put("'_/Float_", "/");
        binaryOps.put("'_/Float_", "/");
        binaryOps.put("'_andBool_", "/\\");
        binaryOps.put("'_orBool_", "\\/");
        binaryOps.put("'_impliesBool_", " -> ");
    };

       public static Map<String,String> doubleBinaryOps = new HashMap<String, String>();
    static {
        doubleBinaryOps.put("'_+Float64_", "+");
        doubleBinaryOps.put("'_-Float64_", "-");
        doubleBinaryOps.put("'_*Float64_", "*");
        doubleBinaryOps.put("'_/Float64_", "/");
        doubleBinaryOps.put("'_/Float64_", "/");
    };

    public static Map<String,String> unaryOps = new HashMap<String, String>();
    static {
        unaryOps.put("'notBool_", "not");
    }

    private final boolean acceptVariables;
    private Exception exception = null;
    private Set<String> variables = new HashSet<>();

    public static GappaPrinter toGappa(Term term) {
        return toGappa(term, true);
    }

    public static GappaPrinter toGappaGround(Term term) {
        return toGappa(term, false);
    }

    public static GappaPrinter toGappa(Term term, boolean acceptVariables) {
        GappaPrinter printer = new GappaPrinter(acceptVariables);
        term.accept(printer);
        return printer;
    }

    public static GappaPrintResult toGappa(SymbolicConstraint constraint) {
        Set<String> variables = null;
        String result = "";
        boolean first = true;
        Exception error = null;
        for (SymbolicConstraint.Equality equality : constraint.equalities()) {
            Term equalityLHS = equality.leftHandSide();
            Term equalityRHS = equality.rightHandSide();
            if (equalityLHS instanceof BoolToken) {
                Term term = equalityLHS;
                equalityLHS = equalityRHS;
                equalityRHS = term;
            }
            if (equalityRHS.equals(BoolToken.FALSE)) {
                if (equalityLHS instanceof KItem) {
                    Term klabel = ((KItem) equalityLHS).kLabel();
                    if (klabel instanceof KLabelConstant && ((KItem) equalityLHS).kList() instanceof KList) {
                        KLabelConstant klabelCt = ((KLabelConstant) klabel);
                        String label = klabelCt.label();
                        String newlabel = reverseComparisonOps.get(label);
                        if (newlabel != null) {
                            klabelCt = KLabelConstant.of(newlabel, constraint.termContext().definition().context());
                            equalityLHS = KItem.of(klabelCt, (KList) ((KItem) equalityLHS).kList(), constraint.termContext());
                            equalityRHS = BoolToken.TRUE;
                        }
                    }
                }
            }
            GappaPrinter gappaLHSPrinter = toGappa(equalityLHS);
            if (gappaLHSPrinter.exception != null) {
                error = gappaLHSPrinter.exception;
                continue;
            }
            String gappaLHS = gappaLHSPrinter.getResult();
            if (gappaLHS.isEmpty()) System.out.println("THis is empty: " + equalityLHS.toString());
            variables = gappaLHSPrinter.variables;
            String eqString = "";
            if (!first) eqString += " /\\ "; else first = false;

            if (equalityRHS.equals(BoolToken.TRUE)) {
               eqString += "(" + gappaLHS + ")";
            } else if (equalityRHS.equals(BoolToken.FALSE)) {
               eqString += "not(" + gappaLHS + ")";
            } else {
                GappaPrinter gappaRHSPrinter = toGappa(equalityRHS);
                if (gappaRHSPrinter.exception != null) {
                    error = gappaRHSPrinter.exception;
                    continue;
                }
                String gappaRHS = gappaRHSPrinter.getResult();
                variables.addAll(gappaRHSPrinter.variables);
                eqString += "(" + gappaLHS + " = " +
                        gappaRHS + ")";
            }
            result += eqString;
        }
        GappaPrintResult printResult = new GappaPrintResult(result, error, variables);
        return printResult;
    }

    public String getResult() {
        return result.toString();
    }

    StringBuilder result;
    public GappaPrinter(boolean acceptVariables) {
        this.acceptVariables = acceptVariables;
        result = new StringBuilder();

    }

    public void reset() {
        result = new StringBuilder();
    }

    @Override
    public void visit(UninterpretedToken uninterpretedToken) {
        result.append(uninterpretedToken.value());
    }

    @Override
    public void visit(KItem kItem) {
        if (!kItem.isGround() && !acceptVariables) {
            exception = new GappaPrinterException(kItem + " is not ground");
            return;
        }
        final Term kLabel = kItem.kLabel();
        if (!(kLabel instanceof KLabelConstant)) {
            exception = new GappaPrinterException(kLabel + " is not constant");
            return;
        }
        KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
//            if (!BuiltinFunction.isBuiltinKLabel(kLabelConstant)) {
//                throw new GappaPrinterException(kLabelConstant + " is not builtin");
//            }

        if (!(kItem.kList() instanceof KList)) {
            exception = new GappaPrinterException(kItem.kList() + " is not a concrete klist");
            return;
        }
        KList kList = (KList) kItem.kList();

        String label = kLabelConstant.label();
        String gappaOp = unaryOps.get(label);
        Term term = null;
        if (gappaOp != null) {
            term = kList.get(0);
        } else if (label.equals("'_-Float_") || label.equals("'_-Float64_")) {
            term=kList.get(0);
            if (term instanceof UninterpretedToken &&
                ((UninterpretedToken) term).value().equals("0.0")) {
                term = kList.get(1);
                gappaOp = "-";
            }
        }
        if (gappaOp != null) {
            result.append(gappaOp + "(");
            term.accept(this);
            result.append(")");
            return;
        }
        boolean comparison = false;
        boolean closeParens = false;
        gappaOp = comparisonOps.get(label);
        if (gappaOp != null) {
            comparison = true;
        } else {
            gappaOp = binaryOps.get(label);
        }
        if (doubleBinaryOps.containsKey(label)) {
            gappaOp = doubleBinaryOps.get(label);
            result.append("rnd(");
            closeParens = true;
        }
        if (gappaOp != null) {
            Term left = kList.get(0);
            Term right = kList.get(1);
            if (comparison && !(right instanceof UninterpretedToken) && left instanceof UninterpretedToken) {
                Term temp = left;
                left = right;
                right = temp;
                gappaOp = reverseComparisonOps.get(gappaOp);
            }
            if (comparison && !(right instanceof UninterpretedToken)) {
                result.append("(");
                openParens(left);
                left.accept(this);
                closeParens(left);
                result.append(" - ");
                openParens(right);
                right.accept(this);
                closeParens(right);
                result.append(")");
                right = UninterpretedToken.of(Sort.of("#Float"), "0.0");
            } else {
                openParens(left);
                left.accept(this);
                closeParens(left);
            }
            result.append(gappaOp);
            openParens(right);
            right.accept(this);
            closeParens(right);
            if (closeParens)
                result.append(")");
            return;
        }
        if (label.equals(intervalOp)) {
            kList.get(1).accept(this);
            result.append(" in [");
            kList.get(0).accept(this);
            result.append(", ");
            kList.get(2).accept(this);
            result.append("]");
            return;
        }
        if (label.equals(unaryMinusOp)) {
            result.append("-");
            Term minused =  kList.get(0);
            boolean parens = !(minused instanceof UninterpretedToken);
            if (parens) result.append("(");
            minused.accept(this);
            if (parens) result.append(")");
            return;
        }
        if (label.equals(absOp)) {
            result.append("|");
            kList.get(0).accept(this);
            result.append("|");
            return;
        }
        exception =  new GappaPrinterException("Operation " + label + " not supported (yet)");
    }

    private void closeParens(Term left) {
        if (left instanceof KItem) result.append(")");
    }

    private void openParens(Term left) {
        if (left instanceof KItem) result.append("(");
    }

    @Override
    public void visit(Variable variable) {
        if (!variable.sort().equals(Sort.FLOAT)) {
            exception =  new GappaPrinterException("Variable " + variable + " is not Float.");
            return;
        }
        String variableName = variable.name().toLowerCase().replaceAll("_", "o");
        variables.add(variableName);
        result.append(variableName);
    }

    public Exception getException() {
        return exception;
    }

    private class GappaPrinterException extends Exception {
        public GappaPrinterException(String s) {
            super(s);
        }
    }


    public static class GappaPrintResult {
        GappaPrintResult(String result, Exception exception, Set<String> variables) {
            this.result = result;
            this.exception = exception;
            this.variables = variables;
        }

        public String result;
        public Exception exception;
        public Set<String> variables;
    }
}
