// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.*;
import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;


/**
 * Transformer class which applies the same transformation on all {@link Term} nodes in the AST.
 *
 * @author AndreiS
 */
public class TermTransformer extends CopyOnWriteTransformer {

    public TermTransformer(TermContext context) {
        super(context);
    }

    /**
     * Performs the transformation used for all {@code Term} nodes on a
     * {@code Term}.
     * 
     * @param term
     *            the term to be transformed
     * @return the transformed term
     */
    protected Term transformTerm(Term term) {
        return term;
    }

    @Override
    public ASTNode transform(BitVector bitVector) {
        return transformTerm((Term) super.transform(bitVector));
    }

    @Override
    public ASTNode transform(BoolToken boolToken) {
        return transformTerm((Term) super.transform(boolToken));
    }

    @Override
    public ASTNode transform(BuiltinList builtinList) {
        return transformTerm((Term) super.transform(builtinList));
    }

    @Override
    public ASTNode transform(BuiltinMap builtinMap) {
        return transformTerm((Term) super.transform(builtinMap));
    }

    @Override
    public ASTNode transform(BuiltinMgu builtinMgu) {
        return transformTerm((Term) super.transform(builtinMgu));
    }

    @Override
    public ASTNode transform(BuiltinSet builtinSet) {
        return transformTerm((Term) super.transform(builtinSet));
    }

    @Override
    public ASTNode transform(Cell cell) {
        return transformTerm((Term) super.transform(cell));
    }

    @Override
    public ASTNode transform(CellCollection cellCollection) {
        return transformTerm((Term) super.transform(cellCollection));
    }

    @Override
    public ASTNode transform(Hole hole) {
        return transformTerm((Term) super.transform(hole));
    }

    @Override
    public ASTNode transform(IntToken intToken) {
        return transformTerm((Term) super.transform(intToken));
    }

    @Override
    public ASTNode transform(KLabelConstant kLabelConstant) {
        return transformTerm((Term) super.transform(kLabelConstant));
    }

    @Override
    public ASTNode transform(KLabelFreezer kLabelFreezer) {
        return transformTerm((Term) super.transform(kLabelFreezer));
    }

    @Override
    public ASTNode transform(KLabelInjection kLabelInjection) {
        return transformTerm((Term) super.transform(kLabelInjection));
    }

    @Override
    public ASTNode transform(KItem kItem) {
        return transformTerm((Term) super.transform(kItem));
    }
    
//    @Override
//    public ASTNode transform(KItemProjection kItemProj) {
//        return transformTerm((Term) super.transform(kItemProj));
//    }

    @Override
    public ASTNode transform(KList kList) {
        return transformTerm((Term) super.transform(kList));
    }

    @Override
    public ASTNode transform(KSequence kSequence) {
        return transformTerm((Term) super.transform(kSequence));
    }
    
    @Override
    public ASTNode transform(ListLookup listLookup) {
        return transformTerm((Term) super.transform(listLookup));
    }

    @Override
    public ASTNode transform(MapKeyChoice mapKeyChoice) {
        return transformTerm((Term) super.transform(mapKeyChoice));
    }

    @Override
    public ASTNode transform(MapLookup mapLookup) {
        return transformTerm((Term) super.transform(mapLookup));
    }

    @Override
    public ASTNode transform(MapUpdate mapUpdate) {
        return transformTerm((Term) super.transform(mapUpdate));
    }

    @Override
    public ASTNode transform(SetElementChoice setElementChoice) {
        return transformTerm((Term) super.transform(setElementChoice));
    }

    @Override
    public ASTNode transform(SetLookup setLookup) {
        return transformTerm((Term) super.transform(setLookup));
    }

    @Override
    public ASTNode transform(SetUpdate setUpdate) {
        return transformTerm((Term) super.transform(setUpdate));
    }
    
    @Override
    public ASTNode transform(StringToken stringToken) {
        return transformTerm((Term) super.transform(stringToken));
    }
    
    @Override
    public ASTNode transform(MetaVariable metaVariable) {
        return transformTerm((Term) super.transform(metaVariable));
    }

    @Override
    public ASTNode transform(UninterpretedToken uninterpretedToken) {
        return transformTerm((Term) super.transform(uninterpretedToken));
    }

    @Override
    public ASTNode transform(Variable variable) {
        return transformTerm((Term) super.transform(variable));
    }

}
