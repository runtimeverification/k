package org.kframework.backend.java.builtins;


/**
 * Table of {@code public static} methods on builtin integers.
 *
 * @author: AndreiS
 */
public class BuiltinInt32Operations {

    public static Int32Token add(Int32Token term1, Int32Token term2) {
        return Int32Token.of(term1.intValue() + term2.intValue());
    }

    public static Int32Token sub(Int32Token term1, Int32Token term2) {
        return Int32Token.of(term1.intValue() - term2.intValue());
    }

    public static Int32Token mul(Int32Token term1, Int32Token term2) {
        return Int32Token.of(term1.intValue() * term2.intValue());
    }

    public static Int32Token div(Int32Token term1, Int32Token term2) {
        return Int32Token.of(term1.intValue() / term2.intValue());
    }

    public static Int32Token rem(Int32Token term1, Int32Token term2) {
        return Int32Token.of(term1.intValue() % term2.intValue());
    }

    public static Int32Token pow(Int32Token term1, Int32Token term2) {
        return Int32Token.of((int) Math.pow(term1.intValue(), term2.intValue()));
    }

    public static Int32Token shl(Int32Token term1, Int32Token term2) {
        return Int32Token.of(term1.intValue() << term2.intValue());
    }

    public static Int32Token shr(Int32Token term1, Int32Token term2) {
        return Int32Token.of(term1.intValue() >> term2.intValue());
    }

    public static Int32Token not(Int32Token term) {
        return Int32Token.of(~term.intValue());
    }

    public static Int32Token and(Int32Token term1, Int32Token term2) {
        return Int32Token.of(term1.intValue() & term2.intValue());
    }

    public static Int32Token or(Int32Token term1, Int32Token term2) {
        return Int32Token.of(term1.intValue() | term2.intValue());
    }

    public static Int32Token xor(Int32Token term1, Int32Token term2) {
        return Int32Token.of(term1.intValue() ^ term2.intValue());
    }

    public static Int32Token min(Int32Token term1, Int32Token term2) {
        return Int32Token.of(Math.min(term1.intValue(), term2.intValue()));
    }

    public static Int32Token max(Int32Token term1, Int32Token term2) {
        return Int32Token.of(Math.max(term1.intValue(), term2.intValue()));
    }

    public static Int32Token abs(Int32Token term) {
        return Int32Token.of(Math.abs(term.intValue()));
    }

    public static BoolToken eq(Int32Token term1, Int32Token term2) {
        return BoolToken.of(term1.intValue() == term2.intValue());
    }

    public static BoolToken ne(Int32Token term1, Int32Token term2) {
        return BoolToken.of(term1.intValue() != term2.intValue());
    }

    public static BoolToken gt(Int32Token term1, Int32Token term2) {
        return BoolToken.of(term1.intValue() > term2.intValue());
    }

    public static BoolToken ge(Int32Token term1, Int32Token term2) {
        return BoolToken.of(term1.intValue() >= term2.intValue());
    }

    public static BoolToken lt(Int32Token term1, Int32Token term2) {
        return BoolToken.of(term1.intValue() < term2.intValue());
    }

    public static BoolToken le(Int32Token term1, Int32Token term2) {
        return BoolToken.of(term1.intValue() <= term2.intValue());
    }

}
