package org.kframework.backend.java.builtins;


import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.util.GappaPrinter;
import org.kframework.backend.java.util.GappaServer;
import org.kframework.krun.K;

/**
 * Table of {@code public static} methods on builtin floats.
 *
 * @author: TraianSF
 */
public class BuiltinFloatOperations {

    /*
    public static IntToken add(IntToken term1, IntToken term2) {
        return IntToken.of(term1.bigIntegerValue().add(term2.bigIntegerValue()));
    }

    public static IntToken sub(IntToken term1, IntToken term2) {
        return IntToken.of(term1.bigIntegerValue().subtract(term2.bigIntegerValue()));
    }

    public static IntToken mul(IntToken term1, IntToken term2) {
        return IntToken.of(term1.bigIntegerValue().multiply(term2.bigIntegerValue()));
    }

    public static IntToken div(IntToken term1, IntToken term2) {
        return IntToken.of(term1.bigIntegerValue().divide(term2.bigIntegerValue()));
    }

    public static IntToken rem(IntToken term1, IntToken term2) {
        return IntToken.of(term1.bigIntegerValue().remainder(term2.bigIntegerValue()));
    }

    public static IntToken pow(IntToken term1, IntToken term2) {
        return IntToken.of(term1.bigIntegerValue().pow(term2.bigIntegerValue().intValue()));
    }

    public static IntToken shl(IntToken term1, IntToken term2) {
        return IntToken.of(term1.bigIntegerValue().shiftLeft(term2.bigIntegerValue().intValue()));
    }

    public static IntToken shr(IntToken term1, IntToken term2) {
        return IntToken.of(term1.bigIntegerValue().shiftRight(term2.bigIntegerValue().intValue()));
    }

    public static IntToken not(IntToken term) {
        return IntToken.of(term.bigIntegerValue().not());
    }

    public static IntToken and(IntToken term1, IntToken term2) {
        return IntToken.of(term1.bigIntegerValue().and(term2.bigIntegerValue()));
    }

    public static IntToken or(IntToken term1, IntToken term2) {
        return IntToken.of(term1.bigIntegerValue().or(term2.bigIntegerValue()));
    }

    public static IntToken xor(IntToken term1, IntToken term2) {
        return IntToken.of(term1.bigIntegerValue().xor(term2.bigIntegerValue()));
    }

    public static IntToken min(IntToken term1, IntToken term2) {
        return IntToken.of(term1.bigIntegerValue().min(term2.bigIntegerValue()));
    }

    public static IntToken max(IntToken term1, IntToken term2) {
        return IntToken.of(term1.bigIntegerValue().max(term2.bigIntegerValue()));
    }

    public static IntToken abs(IntToken term) {
        return IntToken.of(term.bigIntegerValue().abs());
    }

    public static BoolToken eq(IntToken term1, IntToken term2) {
        return BoolToken.of(term1.bigIntegerValue().compareTo(term2.bigIntegerValue()) == 0);
    }

    public static BoolToken ne(IntToken term1, IntToken term2) {
        return BoolToken.of(term1.bigIntegerValue().compareTo(term2.bigIntegerValue()) != 0);
    }
*/

    public static UninterpretedToken unaryMinus(Term term, TermContext context) {
        if (!(term instanceof UninterpretedToken))
            return null;
        UninterpretedToken token = ((UninterpretedToken) term);
        String sort = token.sort();
        if (!sort.equals("Float")) return null;
        String value = token.value();
        if (value.startsWith("-")) value = value.substring(1);
        else value = "-" + value;
        return UninterpretedToken.of(sort, value);
    }

    public static BoolToken gt(Term term1, Term term2, TermContext context) {
        if (!K.smt.equals("gappa")) return null;
        GappaPrinter gappaPrinter = GappaPrinter.toGappaGround(term1);
        if (gappaPrinter.getException() != null) {
            return null;
        }
        String gterm1 = gappaPrinter.getResult();
        gappaPrinter = GappaPrinter.toGappaGround(term2);
        if (gappaPrinter.getException() != null) {
            return null;
        }
        String gterm2 = gappaPrinter.getResult();
        String inputFalse = "(" + gterm1 + " - " + gterm2 + ")" + " <= 0";
        if (GappaServer.proveFalse(inputFalse))
            return BoolToken.TRUE;
        if (GappaServer.proveTrue(inputFalse))
            return BoolToken.FALSE;
        return null;
    }

    public static BoolToken ge(Term term1, Term term2, TermContext context) {
        if (!K.smt.equals("gappa")) return null;
        GappaPrinter gappaPrinter = GappaPrinter.toGappaGround(term1);
        if (gappaPrinter.getException() != null) {
            return null;
        }
        String gterm1 = gappaPrinter.getResult();
        gappaPrinter = GappaPrinter.toGappaGround(term2);
        if (gappaPrinter.getException() != null) {
            return null;
        }
        String gterm2 = gappaPrinter.getResult();
        final String inputTrue = "(" + gterm1 + "-" + gterm2 + ")" + " >= 0";
        if (GappaServer.proveTrue(inputTrue))
            return BoolToken.TRUE;
        if (GappaServer.proveFalse(inputTrue))
            return BoolToken.FALSE;
        return null;
    }

    public static BoolToken lt(Term term1, Term term2, TermContext context) {
        if (!K.smt.equals("gappa")) return null;
        GappaPrinter gappaPrinter = GappaPrinter.toGappaGround(term1);
        if (gappaPrinter.getException() != null) {
            return null;
        }
        String gterm1 = gappaPrinter.getResult();
        gappaPrinter = GappaPrinter.toGappaGround(term2);
        if (gappaPrinter.getException() != null) {
            return null;
        }
        String gterm2 = gappaPrinter.getResult();
        final String inputFalse = "(" + gterm1 + " - " +  gterm2 + ")" + " >= 0";
        if (GappaServer.proveFalse(inputFalse))
            return BoolToken.TRUE;
        if (GappaServer.proveTrue(inputFalse))
            return BoolToken.FALSE;
        return null;
    }

    public static BoolToken le(Term term1, Term term2, TermContext context) {
        if (!K.smt.equals("gappa")) return null;
        GappaPrinter gappaPrinter = GappaPrinter.toGappaGround(term1);
        if (gappaPrinter.getException() != null) {
            return null;
        }
        String gterm1 = gappaPrinter.getResult();
        gappaPrinter = GappaPrinter.toGappaGround(term2);
        if (gappaPrinter.getException() != null) {
            return null;
        }
        String gterm2 = gappaPrinter.getResult();
        final String inputTrue = "(" + gterm1 + "-" + gterm2 + ")" + " <= 0";
        if (GappaServer.proveTrue(inputTrue))
            return BoolToken.TRUE;
        if (GappaServer.proveFalse(inputTrue))
            return BoolToken.FALSE;
        return null;
    }
}
