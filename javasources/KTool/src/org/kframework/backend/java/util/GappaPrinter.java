package org.kframework.backend.java.util;

import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.symbolic.BottomUpVisitor;
import org.kframework.backend.java.symbolic.BuiltinFunction;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Traian
 */
public class GappaPrinter extends BottomUpVisitor {
   	public static Map<String,String> binaryOps = new HashMap<String, String>();
	static {
		binaryOps.put("'_+Float_", "+");
        binaryOps.put("'_-Float_", "-");
		binaryOps.put("'_*Float_", "*");
		binaryOps.put("'_/Float_", "/");
        binaryOps.put("'_andBool_", "/\\");
        binaryOps.put("'_orBool_", "\\/");
        binaryOps.put("'_impliesBool_", " -> ");
	};

    public static Map<String,String> unaryOps = new HashMap<String, String>();
    static {
        unaryOps.put("'-Float_", "-");
        unaryOps.put("'notBool_", "not");
    }

    public String getResult() {
        return result.toString();
    }

    StringBuilder result;
    public GappaPrinter() {
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
            if (!kItem.isGround())
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
            gappaOp = binaryOps.get(label);
            if (gappaOp != null) {
                result.append("(");
                kList.get(0).accept(this);
                result.append(") " + gappaOp + " (" );
                kList.get(1).accept(this);
                result.append(")");
                return;
            }
            throw new GappaPrinterException("Operation " + label + " not supported (yet)");
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
