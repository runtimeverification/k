// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.DataStructures;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.builtin.KLabels;

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

    public static Term get(Term list, IntToken index, TermContext context) {
        if (list instanceof BuiltinList) {
            try {
                BuiltinList builtinList = (BuiltinList) list;
                if (index.intValue() >= 0) {
                    if (IntStream.range(0, index.intValue()).allMatch(builtinList::isElement)) {
                        return builtinList.get(index.intValue());
                    } else {
                        return null;
                    }
                } else {
                    if (IntStream.range(builtinList.size() + index.intValue() + 1, builtinList.size()).allMatch(builtinList::isElement)) {
                        return builtinList.get(builtinList.size() + index.intValue());
                    } else {
                        return null;
                    }
                }
            } catch (IndexOutOfBoundsException e) {
                return Bottom.BOTTOM;
            }
        } else {
            /* the list must consist of exactly one element */
            if (list.sort() != Sort.LIST) {
                throw new IllegalArgumentException();
            }

            if (list instanceof Variable) {
                return null;
            }

            if (index.intValue() == 0) {
                return list;
            } else {
                return Bottom.BOTTOM;
            }
        }
    }

    public static BoolToken in(Term element, Term list, TermContext context) {
        if (list instanceof BuiltinList) {
            BuiltinList builtinList = (BuiltinList) list;
            if (builtinList.contains(wrapListItem(element, context))) {
                return BoolToken.TRUE;
            } else if (element.isGround() && builtinList.isGround()) {
                return BoolToken.FALSE;
            } else {
                return null;
            }
        } else {
            /* the list must consist of exactly one element */
            if (list.sort() != Sort.LIST) {
                throw new IllegalArgumentException();
            }

            if (list.equals(wrapListItem(element, context))) {
                return BoolToken.TRUE;
            } else if (element.isGround() && list.isGround()) {
                return BoolToken.FALSE;
            } else {
                return null;
            }
        }
    }

    public static Term range(Term list, IntToken int1, IntToken int2, TermContext context) {
        int removeLeft = int1.intValue();
        int removeRight = int2.intValue();
        if (removeLeft == 0 && removeRight == 0) {
            return list;
        }

        if (list instanceof BuiltinList) {
            try {
                BuiltinList builtinList = (BuiltinList) list;

                int toRemoveFromLeft = IntStream.range(0, removeLeft)
                        .filter(i -> !builtinList.isElement(i))
                        .findFirst().orElse(removeLeft);
                int toRemoveFromRight = IntStream.range(0, removeRight)
                        .filter(i -> !builtinList.isElement(builtinList.size() - 1 - i))
                        .findFirst().orElse(removeRight);

                int pendingRemoveLeft = removeLeft - toRemoveFromLeft;
                int pendingRemoveRight = removeRight - toRemoveFromRight;
                Term subList = builtinList.range(toRemoveFromLeft, builtinList.size() - toRemoveFromRight);

                return (pendingRemoveLeft > 0 || pendingRemoveRight > 0) ?
                        DataStructures.listRange(subList, pendingRemoveLeft, pendingRemoveRight, context) :
                        subList;
            } catch (IndexOutOfBoundsException e) {
                return Bottom.BOTTOM;
            }
        } else {
            /* the list must consist of exactly one element */
            if (list.sort() != Sort.LIST) {
                throw new IllegalArgumentException();
            }

            if (list instanceof Variable) {
                return null;
            }

            if (removeLeft == 1 && removeRight == 0 || removeLeft == 0 && removeRight == 1) {
                return unit(context);
            } else {
                return Bottom.BOTTOM;
            }
        }
    }

    public static KItem wrapListItem(Term element, TermContext context) {
        return KItem.of(
                KLabelConstant.of(KLabels.ListItem, context.definition()),
                KList.singleton(element),
                context.global());
    }

}
