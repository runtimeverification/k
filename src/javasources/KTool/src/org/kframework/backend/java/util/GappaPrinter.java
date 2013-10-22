package org.kframework.backend.java.util;

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

    public static String toGappa(Term term) {
        return toGappa(term, true);
    }

    public static String toGappaGround(Term term) {
        return toGappa(term, false);
    }

    public static String toGappa(Term term, boolean acceptVariables) {
        GappaPrinter printer = new GappaPrinter(acceptVariables);
        term.accept(printer);
        return printer.getResult();
    }

    public static String toGappa(SymbolicConstraint constraint) {
        String result = "";
        boolean first = true;
        for (SymbolicConstraint.Equality equality : constraint.equalities()) {
            if (!first) result += " /\\ "; else first = false;
            if (equality.rightHandSide().equals(BoolToken.TRUE)) {
               result += "(" + toGappa(equality.leftHandSide()) + ")";
            } else if (equality.rightHandSide().equals(BoolToken.FALSE)) {
               result += "not(" + toGappa(equality.leftHandSide()) + ")";
            } else {
                result += "(" + toGappa(equality.leftHandSide()) + " = " +
                        toGappa(equality.rightHandSide()) + ")";
            }
        }
        return result;
    }

    String getResult() {
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
        try {
            if (!kItem.isGround() && !acceptVariables)
                throw new GappaPrinterException(kItem + " is not ground");
            final KLabel kLabel = kItem.kLabel();
            if (!(kLabel instanceof KLabelConstant))
                throw new GappaPrinterException(kLabel + " is not constant");
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
            throw new GappaPrinterException("Operation " + label + " not supported (yet)");
        } catch (GappaPrinterException e) {
            System.err.println(e.getMessage());
        }
    }

    @Override
    public void visit(Variable variable) {
        try {
            if (!variable.sort().equals("Float"))
                throw new GappaPrinterException("Variable " + variable + " is not Float.");
            result.append(variable.name().toLowerCase().replaceAll("_","o"));
        } catch (GappaPrinterException e) {
            System.err.println(e.getMessage());
        }
    }

    private class GappaPrinterException extends Exception {
        public GappaPrinterException(String s) {
            super(s);
        }
    }
}
