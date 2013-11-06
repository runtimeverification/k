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

   	public static Map<String,String> binaryOps = new HashMap<String, String>();
	static {
        binaryOps.put("'_>=Float_", ">=");
        binaryOps.put("'_<=Float_", "<=");
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

    public static  Map<String,String> negativeBinaryOps = new HashMap<String, String>();
	static {
        negativeBinaryOps.put("'_>Float_", "<=");
        negativeBinaryOps.put("'_<Float_", ">=");
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
            String eqString = "";
            if (!first) eqString += " /\\ "; else first = false;
            GappaPrinter gappaLHSPrinter = toGappa(equality.leftHandSide());
            if (gappaLHSPrinter.exception != null) {
                error = gappaLHSPrinter.exception;
                continue;
            }
            String gappaLHS = gappaLHSPrinter.getResult();
            variables = gappaLHSPrinter.variables;
            if (equality.rightHandSide().equals(BoolToken.TRUE)) {
               eqString += "(" + gappaLHS + ")";
            } else if (equality.rightHandSide().equals(BoolToken.FALSE)) {
               eqString += "not(" + gappaLHS + ")";
            } else {
                GappaPrinter gappaRHSPrinter = toGappa(equality.rightHandSide());
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
        final KLabel kLabel = kItem.kLabel();
        if (!(kLabel instanceof KLabelConstant)) {
            exception = new GappaPrinterException(kLabel + " is not constant");
            return;
        }
        KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
//            if (!BuiltinFunction.isBuiltinKLabel(kLabelConstant)) {
//                throw new GappaPrinterException(kLabelConstant + " is not builtin");
//            }
        KList kList = kItem.kList();
        String label = kLabelConstant.label();
        String gappaOp = unaryOps.get(label);
        if (gappaOp != null) {
            result.append(gappaOp + "(");
            kList.get(0).accept(this);
            result.append(")");
            return;
        }
        gappaOp = negativeBinaryOps.get(label);
        boolean closeParens;
        if (gappaOp != null) {
            result.append("not(");
            closeParens = true;
        } else {
            gappaOp = binaryOps.get(label);
            closeParens = false;
        }
        if (doubleBinaryOps.containsKey(label)) {
            gappaOp = doubleBinaryOps.get(label);
            result.append("rnd(");
            closeParens = true;
        }
        if (gappaOp != null) {
            result.append("(");
            kList.get(0).accept(this);
            result.append(") " + gappaOp + " (" );
            kList.get(1).accept(this);
            result.append(")");
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
            kList.get(0).accept(this);
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

    @Override
    public void visit(Variable variable) {
        if (!variable.sort().equals("Float")) {
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
