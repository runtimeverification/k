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
        return BuiltinList.concatenate(context.global(), list1, list2);
    }

    public static Term unit(TermContext context) {
        return BuiltinList.builder(context.global()).build();
    }

    public static Term element(Term element, TermContext context) {
        BuiltinList.Builder builder = BuiltinList.builder(context.global());
        builder.addItem(element);
        return builder.build();
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
        int pendingRemoveLeft;
        int pendingRemoveRight;
        if (!(list instanceof BuiltinList)) {
            return null;
        }
        BuiltinList builtinList = (BuiltinList) list;
        List<Term> elementsLeft = builtinList.elementsLeft();
        List<Term> elementsRight = builtinList.elementsRight();
        if (builtinList.isConcreteCollection()) {
            if (removeLeft + removeRight > elementsLeft.size()) {
                return Bottom.BOTTOM;
            }

            pendingRemoveLeft = pendingRemoveRight = 0;
            elementsLeft = elementsLeft.subList(removeLeft, elementsLeft.size() - removeRight);
            elementsRight = ImmutableList.of();
        } else {
            if (removeLeft > elementsLeft.size()) {
                pendingRemoveLeft = removeLeft - elementsLeft.size();
                elementsLeft = ImmutableList.of();
            } else {
                pendingRemoveLeft = 0;
                elementsLeft = elementsLeft.subList(removeLeft, elementsLeft.size());
            }

            if (removeRight > elementsRight.size()) {
                pendingRemoveRight = removeRight - elementsRight.size();
                elementsRight = ImmutableList.of();
            } else {
                pendingRemoveRight = 0;
                elementsRight = elementsRight.subList(0, elementsRight.size() - removeRight);
            }
        }

        BuiltinList.Builder builder = BuiltinList.builder(context.global());
        builder.addItems(elementsLeft);
        builder.concatenate(builtinList.baseTerms());
        builder.addItems(elementsRight);

        return (pendingRemoveLeft > 0 || pendingRemoveRight > 0) ?
                DataStructures.listRange(
                        builder.build(),
                        pendingRemoveLeft,
                        pendingRemoveLeft, context) :
                builder.build();
    }

}
