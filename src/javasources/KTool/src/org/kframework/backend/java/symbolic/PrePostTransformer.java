// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.*;
import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;
import org.kframework.kil.visitors.Visitor;

/**
 * Performs transformation which includes pre-processing and post-processing.
 * <p><br>
 * Transformation on a given node is performed in three steps:
 * <li>pre-processing that node;
 * <li>applying transformation recursively on its children;
 * <li>post-processing that node.
 *
 * @author AndreiS
 */
public abstract class PrePostTransformer extends CopyOnWriteTransformer {

    /**
     * Returns the {@code CombinedLocalTransformer} used for pre-processing.
     */
    public CombinedLocalTransformer getPreTransformer() {
        return preTransformer;
    }

    public void setPreTransformer(CombinedLocalTransformer preTransformer) {
        this.preTransformer = preTransformer;
    }

    /**
     * Returns the {@code CombinedLocalTransformer} used for post-processing.
     */
    public CombinedLocalTransformer getPostTransformer() {
        return postTransformer;
    }

    public void setPostTransformer(CombinedLocalTransformer postTransformer) {
        this.postTransformer = postTransformer;
    }

    protected CombinedLocalTransformer preTransformer = new CombinedLocalTransformer();
    protected CombinedLocalTransformer postTransformer = new CombinedLocalTransformer();

    public PrePostTransformer(TermContext context) {
        super(context);
    }

    public PrePostTransformer() {
        super();
    }

    @Override
    public ASTNode transform(Cell cell) {
        ASTNode astNode = cell.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof Cell : "preTransformer should not modify type";
        cell = (Cell<?>) astNode;
        cell = (Cell<?>) super.transform(cell);
        return cell.accept(postTransformer);
    }

    @Override
    public ASTNode transform(CellCollection cellCollection) {
        ASTNode astNode = cellCollection.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof CellCollection : "preTransformer should not modify type";
        cellCollection = (CellCollection) astNode;
        cellCollection = (CellCollection) super.transform(cellCollection);
        return cellCollection.accept(postTransformer);
    }

    @Override
    public ASTNode transform(Collection collection) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(ConstrainedTerm constrainedTerm) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(KLabelConstant kLabelConstant) {
        ASTNode astNode = kLabelConstant.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof KLabelConstant : "preTransformer should not modify type";
        kLabelConstant = (KLabelConstant) astNode;
        kLabelConstant = (KLabelConstant) super.transform(kLabelConstant);
        return kLabelConstant.accept(postTransformer);
    }

    @Override
    public ASTNode transform(KLabelFreezer kLabelFreezer) {
        ASTNode astNode = kLabelFreezer.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof KLabelFreezer : "preTransformer should not modify type";
        kLabelFreezer = (KLabelFreezer) astNode;
        kLabelFreezer = (KLabelFreezer) super.transform(kLabelFreezer);
        return kLabelFreezer.accept(postTransformer);
    }

    @Override
    public ASTNode transform(Hole hole) {
        ASTNode astNode = hole.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof Hole : "preTransformer should not modify type";
        hole = (Hole) astNode;
        hole = (Hole) super.transform(hole);
        return hole.accept(postTransformer);
    }

    @Override
    public ASTNode transform(KLabelInjection kLabelInjection) {
        ASTNode astNode = kLabelInjection.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof KLabelInjection : "preTransformer should not modify type";
        kLabelInjection = (KLabelInjection) astNode;
        kLabelInjection = (KLabelInjection) super.transform(kLabelInjection);
        return kLabelInjection.accept(postTransformer);
    }

    @Override
    public ASTNode transform(KItem kItem) {
        ASTNode astNode = kItem.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof KItem : "preTransformer should not modify type";
        kItem = (KItem) astNode;
        kItem = (KItem) super.transform(kItem);
        return kItem.accept(postTransformer);
    }

    @Override
    public ASTNode transform(KItemProjection kItemProjection) {
        ASTNode astNode = kItemProjection.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof KItemProjection : "preTransformer should not modify type";
        kItemProjection = (KItemProjection) astNode;
        kItemProjection = (KItemProjection) super.transform(kItemProjection);
        return kItemProjection.accept(postTransformer);
    }

    @Override
    public ASTNode transform(Token token) {
        ASTNode astNode = token.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof Token : "preTransformer should not modify type";
        token = (Token) astNode;
        token = (Token) super.transform(token);
        return token.accept(postTransformer);
    }

    @Override
    public ASTNode transform(UninterpretedToken uninterpretedToken) {
        return transform((Token) uninterpretedToken);
    }

    @Override
    public ASTNode transform(BoolToken boolToken) {
        return transform((Token) boolToken);
    }

    @Override
    public ASTNode transform(IntToken intToken) {
        return transform((Token) intToken);
    }

    @Override
    public ASTNode transform(StringToken stringToken) {
        return transform((Token) stringToken);
    }

    @Override
    public ASTNode transform(KCollection kCollection) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(KLabel kLabel) {
        ASTNode astNode = kLabel.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof KLabel : "preTransformer should not modify type";
        kLabel = (KLabel) astNode;
        kLabel = (KLabel) super.transform(kLabel);
        return kLabel.accept(postTransformer);
    }

    @Override
    public ASTNode transform(KList kList) {
        ASTNode astNode = kList.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof KList : "preTransformer should not modify type";
        kList = (KList) astNode;
        kList = (KList) super.transform(kList);
        return kList.accept(postTransformer);
    }

    @Override
    public ASTNode transform(KSequence kSequence) {
        ASTNode astNode = kSequence.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof KSequence : "preTransformer should not modify type";
        kSequence = (KSequence) astNode;
        Term t =  (Term) super.transform(kSequence);
        if (t instanceof KSequence)
            t = (KSequence) t.accept(postTransformer);
        return t;
    }

    @Override
    public ASTNode transform(ListLookup listLookup) {
        ASTNode astNode = listLookup.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof ListLookup : "preTransformer should not modify type";
        listLookup = (ListLookup) astNode;
        listLookup = (ListLookup) super.transform(listLookup);
        return listLookup.accept(postTransformer);
    }

    @Override
    public ASTNode transform(BuiltinList builtinList) {
        ASTNode astNode = builtinList.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof BuiltinList : "preTransformer should not modify type";
        builtinList = (BuiltinList) astNode;
        builtinList = (BuiltinList) super.transform(builtinList);
        return builtinList.accept(postTransformer);
    }

    @Override
    public ASTNode transform(BuiltinMap builtinMap) {
        ASTNode astNode = builtinMap.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof BuiltinMap : "preTransformer should not modify type";
        builtinMap = (BuiltinMap) astNode;
        builtinMap = (BuiltinMap) super.transform(builtinMap);
        return builtinMap.accept(postTransformer);
    }

    @Override
    public ASTNode transform(BuiltinSet builtinSet) {
        ASTNode astNode = builtinSet.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof BuiltinSet : "preTransformer should not modify type";
        builtinSet = (BuiltinSet) astNode;
        builtinSet = (BuiltinSet) super.transform(builtinSet);
        return builtinSet.accept(postTransformer);
    }

    @Override
    public ASTNode transform(MapKeyChoice mapKeyChoice) {
        ASTNode astNode = mapKeyChoice.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof MapKeyChoice : "preTransformer should not modify type";
        mapKeyChoice = (MapKeyChoice) astNode;
        mapKeyChoice = (MapKeyChoice) super.transform(mapKeyChoice);
        return mapKeyChoice.accept(postTransformer);
    }

    @Override
    public ASTNode transform(MapLookup mapLookup) {
        ASTNode astNode = mapLookup.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof MapLookup : "preTransformer should not modify type";
        mapLookup = (MapLookup) astNode;
        mapLookup = (MapLookup) super.transform(mapLookup);
        return mapLookup.accept(postTransformer);
    }

    @Override
    public ASTNode transform(MapUpdate mapUpdate) {
        ASTNode astNode = mapUpdate.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof MapUpdate : "preTransformer should not modify type";
        mapUpdate = (MapUpdate) astNode;
        mapUpdate = (MapUpdate) super.transform(mapUpdate);
        return mapUpdate.accept(postTransformer);
    }

    @Override
    public ASTNode transform(SetUpdate setUpdate) {
        ASTNode astNode = setUpdate.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof SetUpdate : "preTransformer should not modify type";
        setUpdate = (SetUpdate) astNode;
        setUpdate = (SetUpdate) super.transform(setUpdate);
        return setUpdate.accept(postTransformer);
    }

    @Override
    public ASTNode transform(SetElementChoice setElementChoice) {
        ASTNode astNode = setElementChoice.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof SetElementChoice : "preTransformer should not modify type";
        setElementChoice = (SetElementChoice) astNode;
        setElementChoice = (SetElementChoice) super.transform(setElementChoice);
        return setElementChoice.accept(postTransformer);
    }

    @Override
    public ASTNode transform(SetLookup setLookup) {
        ASTNode astNode = setLookup.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof SetLookup : "preTransformer should not modify type";
        setLookup = (SetLookup) astNode;
        setLookup = (SetLookup) super.transform(setLookup);
        return setLookup.accept(postTransformer);
    }

    @Override
    public ASTNode transform(MetaVariable metaVariable) {
        return transform((Token) metaVariable);
    }

    @Override
    public ASTNode transform(Rule rule) {
        ASTNode astNode = rule.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof Rule : "preTransformer should not modify type";
        rule = (Rule) astNode;
        rule = (Rule) super.transform(rule);
        return rule.accept(postTransformer);
    }

    @Override
    public ASTNode transform(SymbolicConstraint symbolicConstraint) {
        ASTNode astNode = symbolicConstraint.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof SymbolicConstraint : "preTransformer should not modify type";
        symbolicConstraint = (SymbolicConstraint) astNode;
        symbolicConstraint = (SymbolicConstraint) super.transform(symbolicConstraint);
        return symbolicConstraint.accept(postTransformer);
    }

    @Override
    public ASTNode transform(UninterpretedConstraint uninterpretedConstraint) {
        ASTNode astNode = uninterpretedConstraint.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof UninterpretedConstraint : "preTransformer should not modify type";
        uninterpretedConstraint = (UninterpretedConstraint) astNode;
        uninterpretedConstraint = (UninterpretedConstraint) super.transform(uninterpretedConstraint);
        return uninterpretedConstraint.accept(postTransformer);
    }

    @Override
    public ASTNode transform(Term node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(Variable variable) {
        ASTNode astNode = variable.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof Variable : "preTransformer should not modify type";
        variable = (Variable) astNode;
        variable = (Variable) super.transform(variable);
        return variable.accept(postTransformer);
    }

    @Override
    public ASTNode transform(BuiltinMgu mgu) {
        ASTNode astNode = mgu.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof BuiltinMgu : "preTransformer should not modify type";
        mgu = (BuiltinMgu) astNode;
        mgu = (BuiltinMgu) super.transform(mgu);
        return mgu.accept(postTransformer);
    }

    protected class DoneTransforming extends ASTNode {
        public DoneTransforming(ASTNode node) {
            contents = node;
        }

        @Override
        public ASTNode shallowCopy() {
            throw new UnsupportedOperationException();
        }

        public ASTNode getContents() {
            return contents;
        }

        private final ASTNode contents;

        @Override
        protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
            throw new UnsupportedOperationException();
        }
    }
}
