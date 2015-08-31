// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

/**
 * Created by dwightguth on 5/8/15.
 */
public interface KItemCollection extends CollectionInternalRepresentation {

    TermContext context();
    Sort sort();

    @Override
    default Term toKore() {
        return toKore(context());
    }

    @Override
    default KLabel constructorLabel() {
        return KLabelConstant.of(
                context().definition().dataStructureSortOf(sort()).constructorLabel(),
                context().definition());
    }

    @Override
    default KItem unit() {
        return KItem.of(
                KLabelConstant.of(
                        context().definition().dataStructureSortOf(sort()).unitLabel(),
                        context().definition()),
                KList.EMPTY,
                context());
    }
}
