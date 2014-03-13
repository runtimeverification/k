package org.kframework.backend.java.builtins;


import com.google.common.primitives.*;
import org.kframework.backend.java.kil.TermContext;

/**
 * Table of {@code public static} methods on builtin integers.
 *
 * @author AndreiS
 */
public class BuiltinInt32Operations {

    public static BitVector construct(IntToken bitwidth, IntToken value, TermContext context) {
        try {
            return BitVector.of(value.bigIntegerValue(), bitwidth.intValue());
        } catch (ArithmeticException e) {
            throw new IllegalArgumentException(e);
        }
    }

    public static IntToken bitwidth(BitVector term, TermContext context) {
        return IntToken.of(term.bitwidth());
    }

    public static IntToken svalue(BitVector term, TermContext context) {
        if (term instanceof PrimitiveIntToken) {
            return IntToken.of(((PrimitiveIntToken) term).longValue());
        } else {
            return IntToken.of(term.bigIntegerValue());
        }
    }

    public static IntToken uvalue(BitVector term, TermContext context) {
        if (term instanceof PrimitiveIntToken) {
            Number value = ((PrimitiveIntToken) term).primitiveIntValue();
            if (value instanceof Byte) {
                return IntToken.of(UnsignedInteger.fromIntBits((Byte) value).bigIntegerValue());
            } else if (value instanceof Short) {
                return IntToken.of(UnsignedInteger.fromIntBits((Short) value).bigIntegerValue());
            } else if (value instanceof Integer) {
                return IntToken.of(UnsignedInteger.fromIntBits((Integer) value).bigIntegerValue());
            } else if (value instanceof Long) {
                return IntToken.of(UnsignedLong.fromLongBits((Long) value).bigIntegerValue());
            } else  {
                assert false;
                /* unreachable code */
                return null;
            }
        } else {
            return IntToken.of(term.bigIntegerValue());
        }
    }

    public static BitVector add(BitVector term1, BitVector term2, TermContext context) {
        if (term1 instanceof PrimitiveIntToken && term2 instanceof PrimitiveIntToken) {
            Number value1 = ((PrimitiveIntToken) term1).primitiveIntValue();
            Number value2 = ((PrimitiveIntToken) term1).primitiveIntValue();
            if (value1 instanceof Byte && value2 instanceof Byte) {
                return PrimitiveIntToken.of((Byte) value1 + (Byte) value2);
            } else if (value1 instanceof Short && value2 instanceof Short) {
                return PrimitiveIntToken.of((Short) value1 + (Short) value2);
            } else if (value1 instanceof Integer && value2 instanceof Integer) {
                return PrimitiveIntToken.of((Integer) value1 + (Integer) value2);
            } else if (value1 instanceof Long && value2 instanceof Long) {
                return PrimitiveIntToken.of((Long) value1 + (Long) value2);
            } else {
                return failWithBitwidthMismatch(term1, term2);
            }
        } else if (term1.bitwidth() == term2.bitwidth()) {
            throw new UnsupportedOperationException();
        } else {
            return failWithBitwidthMismatch(term1, term2);
        }
    }

    public static BitVector sub(BitVector term1, BitVector term2, TermContext context) {
        if (term1 instanceof PrimitiveIntToken && term2 instanceof PrimitiveIntToken) {
            Number value1 = ((PrimitiveIntToken) term1).primitiveIntValue();
            Number value2 = ((PrimitiveIntToken) term1).primitiveIntValue();
            if (value1 instanceof Byte && value2 instanceof Byte) {
                return PrimitiveIntToken.of((Byte) value1 - (Byte) value2);
            } else if (value1 instanceof Short && value2 instanceof Short) {
                return PrimitiveIntToken.of((Short) value1 - (Short) value2);
            } else if (value1 instanceof Integer && value2 instanceof Integer) {
                return PrimitiveIntToken.of((Integer) value1 - (Integer) value2);
            } else if (value1 instanceof Long && value2 instanceof Long) {
                return PrimitiveIntToken.of((Long) value1 - (Long) value2);
            } else {
                return failWithBitwidthMismatch(term1, term2);
            }
        } else if (term1.bitwidth() == term2.bitwidth()) {
            throw new UnsupportedOperationException();
        } else {
            return failWithBitwidthMismatch(term1, term2);
        }
    }

    public static BitVector mul(BitVector term1, BitVector term2, TermContext context) {
        if (term1 instanceof PrimitiveIntToken && term2 instanceof PrimitiveIntToken) {
            Number value1 = ((PrimitiveIntToken) term1).primitiveIntValue();
            Number value2 = ((PrimitiveIntToken) term1).primitiveIntValue();
            if (value1 instanceof Byte && value2 instanceof Byte) {
                return PrimitiveIntToken.of((Byte) value1 * (Byte) value2);
            } else if (value1 instanceof Short && value2 instanceof Short) {
                return PrimitiveIntToken.of((Short) value1 * (Short) value2);
            } else if (value1 instanceof Integer && value2 instanceof Integer) {
                return PrimitiveIntToken.of((Integer) value1 * (Integer) value2);
            } else if (value1 instanceof Long && value2 instanceof Long) {
                return PrimitiveIntToken.of((Long) value1 * (Long) value2);
            } else {
                return failWithBitwidthMismatch(term1, term2);
            }
        } else if (term1.bitwidth() == term2.bitwidth()) {
            throw new UnsupportedOperationException();
        } else {
            return failWithBitwidthMismatch(term1, term2);
        }
    }

    /**
     * Throws {@link IllegalArgumentException}.
     * @return does not return anything; it is not void as a convenience.
     */
    private static PrimitiveIntToken failWithBitwidthMismatch(
            BitVector term1,
            BitVector term2) {
        throw new IllegalArgumentException(
                "mismatch bit width: "
                + "first argument is represented on " + term1.bitwidth() + " bits "
                + "while second argument is represented on " + term2.bitwidth() + "bits");
    }

//    public static PrimitiveIntToken div(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return PrimitiveIntToken.of(term1.intValue() / term2.intValue());
//    }
//
//    public static PrimitiveIntToken rem(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return PrimitiveIntToken.of(term1.intValue() % term2.intValue());
//    }
//
//    public static PrimitiveIntToken pow(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return PrimitiveIntToken.of((int) Math.pow(term1.intValue(), term2.intValue()));
//    }
//
//    public static PrimitiveIntToken shl(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return PrimitiveIntToken.of(term1.intValue() << term2.intValue());
//    }
//
//    public static PrimitiveIntToken shr(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return PrimitiveIntToken.of(term1.intValue() >> term2.intValue());
//    }
//
//    public static PrimitiveIntToken not(PrimitiveIntToken term, TermContext context) {
//        return PrimitiveIntToken.of(~term.intValue());
//    }
//
//    public static PrimitiveIntToken and(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return PrimitiveIntToken.of(term1.intValue() & term2.intValue());
//    }
//
//    public static PrimitiveIntToken or(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return PrimitiveIntToken.of(term1.intValue() | term2.intValue());
//    }
//
//    public static PrimitiveIntToken xor(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return PrimitiveIntToken.of(term1.intValue() ^ term2.intValue());
//    }
//
//    public static PrimitiveIntToken min(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return PrimitiveIntToken.of(Math.min(term1.intValue(), term2.intValue()));
//    }
//
//    public static PrimitiveIntToken max(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return PrimitiveIntToken.of(Math.max(term1.intValue(), term2.intValue()));
//    }
//
//    public static PrimitiveIntToken abs(PrimitiveIntToken term, TermContext context) {
//        return PrimitiveIntToken.of(Math.abs(term.intValue()));
//    }
//
//    public static BoolToken eq(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return BoolToken.of(term1.intValue() == term2.intValue());
//    }
//
//    public static BoolToken ne(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return BoolToken.of(term1.intValue() != term2.intValue());
//    }
//
//    public static BoolToken gt(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return BoolToken.of(term1.intValue() > term2.intValue());
//    }
//
//    public static BoolToken ge(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return BoolToken.of(term1.intValue() >= term2.intValue());
//    }
//
//    public static BoolToken lt(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return BoolToken.of(term1.intValue() < term2.intValue());
//    }
//
//    public static BoolToken le(PrimitiveIntToken term1, PrimitiveIntToken term2, TermContext context) {
//        return BoolToken.of(term1.intValue() <= term2.intValue());
//    }

}
