package org.kframework.backend.java.util;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.symbolic.BottomUpVisitor;
import org.kframework.backend.java.symbolic.BuiltinFunction;
import org.kframework.backend.java.symbolic.SymbolicConstraint;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Traian
 */
public class GappaPrinter extends BottomUpVisitor {

    public static String intervalOp = "'_<=Float_<=Float_";

   	public static Map<String,String> binaryOps = new HashMap<String, String>();
	static {
        binaryOps.put("'_>=Float_", ">=");
        binaryOps.put("'_<=Float_", ">=");
		binaryOps.put("'_+Float_", "+");
        binaryOps.put("'_-Float_", "-");
		binaryOps.put("'_*Float_", "*");
		binaryOps.put("'_/Float_", "/");
        binaryOps.put("'_/Float_", "/");
        binaryOps.put("'_andBool_", "/\\");
        binaryOps.put("'_orBool_", "\\/");
        binaryOps.put("'_impliesBool_", " -> ");
	};

    public static  Map<String,String> negativeBinaryOps = new HashMap<String, String>();
	static {
        negativeBinaryOps.put("'_>Float_", "<=");
        negativeBinaryOps.put("'_<Float_", ">=");
	};

    public static Map<String,String> unaryOps = new HashMap<String, String>();
    static {
        unaryOps.put("'-Float_", "-");
        unaryOps.put("'notBool_", "not");
    }

    private final boolean acceptVariables;
    private Exception exception = null;

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

    public static Pair<String, Exception> toGappa(SymbolicConstraint constraint) {
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
                eqString += "(" + gappaLHS + " = " +
                        gappaRHS + ")";
            }
            result += eqString;
        }
        final String finalResult = result;
        final Exception finalError = error;
        Pair<String,Exception> resultPair = new Pair<String, Exception>() {
            @Override
            public String getLeft() {
                return finalResult;
            }

            @Override
            public Exception getRight() {
                return finalError;
            }

            @Override
            public Exception setValue(Exception value) {
                return null;
            }
        };
        return resultPair;
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
        boolean negative;
        if (gappaOp != null) {
            result.append("not(");
            negative = true;
        } else {
            gappaOp = binaryOps.get(label);
            negative = false;
        }
        if (gappaOp != null) {
            result.append("(");
            kList.get(0).accept(this);
            result.append(") " + gappaOp + " (" );
            kList.get(1).accept(this);
            result.append(")");
            if (negative)
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
        exception =  new GappaPrinterException("Operation " + label + " not supported (yet)");
    }

    @Override
    public void visit(Variable variable) {
        if (!variable.sort().equals("Float")) {
            exception =  new GappaPrinterException("Variable " + variable + " is not Float.");
            return;
        }
        result.append(variable.name().toLowerCase().replaceAll("_", "o"));
    }

    public Exception getException() {
        return exception;
    }

    private class GappaPrinterException extends Exception {
        public GappaPrinterException(String s) {
            super(s);
        }
    }
}
