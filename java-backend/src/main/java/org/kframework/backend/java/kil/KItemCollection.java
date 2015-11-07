// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

/**
 * Created by dwightguth on 5/8/15.
 */
public interface KItemCollection extends CollectionInternalRepresentation, HasGlobalContext {

    @Override
    default KLabel constructorLabel() {
        Definition definition = globalContext().getDefinition();
        return KLabelConstant.of(
                definition.dataStructureSortOf(sort()).constructorLabel(),
                definition);
    }

    @Override
    default KItem unit() {
        Definition definition = globalContext().getDefinition();
        return KItem.of(
                KLabelConstant.of(
                        definition.dataStructureSortOf(sort()).unitLabel(),
                        definition),
                KList.EMPTY,
                globalContext());
    }
}
