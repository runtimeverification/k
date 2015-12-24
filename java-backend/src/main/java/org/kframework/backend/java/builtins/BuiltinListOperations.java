// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import com.google.common.collect.ImmutableList;
import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.DataStructures;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;

import java.util.List;
import java.util.stream.IntStream;


/**
 * Table of {@code public static} methods on builtin lists.
 *
 * @author AndreiS
 */
public class BuiltinListOperations {

    public static Term constructor(Term list1, Term list2, TermContext context) {
        if (list1.sort() != Sort.LIST || list2.sort() != Sort.LIST) {
            throw new IllegalArgumentException();
        }
        return BuiltinList.builder(context.global()).addAll(list1, list2).build();
    }

    public static Term unit(TermContext context) {
        return BuiltinList.builder(context.global()).build();
    }

    public static Term element(Term element, TermContext context) {
        throw new UnsupportedOperationException();
    }

    public static Term get(BuiltinList list, IntToken index, TermContext context) {
        Term value = list.get(index.intValue());
        if (value != null) {
            return value;
        } else if (list.isConcreteCollection()) {
            return Bottom.BOTTOM;
        } else {
            return null;
        }
    }

    public static BoolToken in(Term element, BuiltinList list, TermContext context) {
        if (list.contains(element)) {
            return BoolToken.TRUE;
        } else if (element.isGround() && list.isGround()) {
            return BoolToken.FALSE;
        } else {
            return null;
        }
    }

    public static Term range(Term list, IntToken int1, IntToken int2, TermContext context) {
        int removeLeft = int1.intValue();
        int removeRight = int2.intValue();
        if (removeLeft == 0 && removeRight == 0) {
            return list;
        }
        if (!(list instanceof BuiltinList)) {
            return null;
        }
        BuiltinList builtinList = (BuiltinList) list;

        int toRemoveFromLeft = IntStream.range(0, removeLeft)
                .filter(i -> builtinList.get(i).sort().equals(builtinList.sort))
                .findFirst().orElse(removeLeft);
        int toRemoveFromRight = IntStream.range(0, removeRight)
                .filter(i -> builtinList.get(builtinList.size() - 1 - i).sort().equals(builtinList.sort))
                .findFirst().orElse(removeRight);

        int pendingRemoveLeft = removeLeft - toRemoveFromLeft;
        int pendingRemoveRight = removeRight - toRemoveFromRight;
        Term subList = builtinList.range(toRemoveFromLeft, builtinList.size() - toRemoveFromRight);

        return (pendingRemoveLeft > 0 || pendingRemoveRight > 0) ?
                DataStructures.listRange(subList, pendingRemoveLeft, pendingRemoveLeft, context) :
                subList;
    }

}
