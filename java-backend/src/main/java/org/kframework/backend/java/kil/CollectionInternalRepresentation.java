// Copyright (c) K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.util.List;


public interface CollectionInternalRepresentation extends KItemRepresentation {
    /**
     * Returns a KORE (KLabel/KList) representation of this collection object.
     * The returned representation is not unique (due to associativity/commutativity).
     * {@link Term#evaluate} is the inverse operation.
     */
    @Override
    default Term toKore() {
        List<Term> components = getKComponents();

        if (components.isEmpty()) {
            return unit();
        }

        Term result = components.get(components.size() - 1);
        for (int i = components.size() - 2; i >= 0; --i) {
            Term component = components.get(i);
            result = new KItem(
                    constructorLabel(),
                    KList.concatenate(component, result),
                    globalContext(), sort(),
                    true,
                    component.att());
        }

        return result;
    }

    /**
     * Returns a list aggregating the base terms and the elements/entries of this collection.
     * Each collection is responsible for representing its elements/entries in KLabel and KList
     * format.
     */
    List<Term> getKComponents();

    /**
     * Returns the KLabel that constructs an instance of this collection/formula.
     */
    KLabel constructorLabel();

    /**
     * Returns the KItem representation of the unit of this collection/formula.
     */
    Term unit();

    Sort sort();
}
