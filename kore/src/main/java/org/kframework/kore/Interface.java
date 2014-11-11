// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore;

/**
 *
 * Helper constructors for KORE classes. The class is meant to be imported
 * statically.
 *
 * @see org.kframework.kore.InterfaceTest
 *
 */

public class Interface {
    private static Attributes emptyAttributes = Attributes$.MODULE$.apply(KList());

    public static KString KString(String s) {
        return new KString(s);
    }

    public static Sort Sort(String name) {
        return new Sort(name);
    }

    public static KLabel KLabel(String name) {
        return new ConcreteKLabel(name);
    }

    public static KList KList(K... ks) {
        return KList.fromJava(ks);
    }

    public static KApply KApply(KLabel klabel, KList klist, Attributes att) {
        return new KApply(klabel, klist, att);
    }

    public static KApply KApply(KLabel klabel, KList klist) {
        return KApply(klabel, klist, emptyAttributes);
    }

    public static KToken KToken(Sort sort, KString string, Attributes att) {
        return new KToken(sort, string, att);
    }

    public static KToken KToken(Sort sort, KString string) {
        return KToken(sort, string, emptyAttributes);
    }

    public static KVariable KVariable(String name, Attributes att) {
        return new KVariable(name, emptyAttributes);
    }

    public static KVariable KVariable(String name) {
        return KVariable(name, emptyAttributes);
    }

    public static KSequence KSequence(K... ks) {
        return KSequence.fromJava(ks);
    }

    public static KRewrite KRewrite(K left, K right) {
        return new KRewrite(left, right, emptyAttributes);
    }
}
