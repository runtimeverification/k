package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.CollectionBuiltin;
import org.kframework.kil.CollectionSort;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.Production;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;


/**
 * Transformer class compiling collection (bag, list, map and set) terms into K internal
 * representation.
 *
 * @author AndreiS
 */
public class FlattenCollections extends CopyOnWriteTransformer {

    private enum Status { LHS, RHS, CONDITION };

    private Status status;

    public FlattenCollections(Context context) {
        super("Compile collections (bag, list, map and set) to abstract K",
                context);
    }

    @Override
    public ASTNode transform(Rule node) throws TransformerException {
        assert node.getBody() instanceof Rewrite :
                "expected rewrite at the top of rule\n" + node + "\n"
                + "FlattenCollections pass should be applied after ResolveRewrite pass";

        Rewrite rewrite = (Rewrite) node.getBody();
        status = Status.LHS;
        Term lhs = (Term) rewrite.getLeft().accept(this);
        status = Status.RHS;
        Term rhs = (Term) rewrite.getRight().accept(this);
        Term condition;
        if (node.getCondition() != null) {
            status = Status.CONDITION;
            condition = (Term) node.getCondition().accept(this);
        } else {
            condition = null;
        }

        if (lhs == rewrite.getLeft()
            && rhs == rewrite.getRight()
            && condition == node.getCondition()) {
            return node;
        }

        node = node.shallowCopy();
        rewrite = rewrite.shallowCopy();
        node.setBody(rewrite);
        rewrite.setLeft(lhs, context);
        rewrite.setRight(rhs, context);
        node.setCondition(condition);
        return node;
    }

    @Override
    public ASTNode transform(Rewrite node) throws TransformerException {
        assert false: "FlattenCollections pass should be applied after ResolveRewrite pass";
        return node;
    }

    @Deprecated @Override
    public ASTNode transform(TermCons node) throws TransformerException {
        /* TODO(andreis): TermCons should have been transformed into KApp by now */
        if (status != Status.LHS) {
            return super.transform(node);
        }

        Production production = node.getProduction();
        CollectionSort collectionSort = context.collectionSortOf(production.getSort());
        if (collectionSort == null) {
            return super.transform(node);
        }

        String kLabel = production.getKLabel();
        if (collectionSort.constructorLabel().equals(kLabel)) {
            assert node.arity() == 2;

            Term term1 = (Term) node.getContents().get(0).accept(this);
            Term term2 = (Term) node.getContents().get(0).accept(this);

            CollectionBuiltin collection = CollectionBuiltin.of(collectionSort, term1, term2);
            if (collection.hasFrame() || collection.isElementCollection()) {
                return collection;
            } else {
                GlobalSettings.kem.register(new KException(
                        KException.ExceptionType.ERROR,
                        KException.KExceptionGroup.COMPILER,
                        "unexpected left-hand side collection format; "
                        + "expected elements and at most one variable",
                        getName(),
                        node.getFilename(),
                        node.getLocation()));
                return null;
            }
        } else if (collectionSort.elementLabel().equals(kLabel)) {
            /* TODO(andreis): check sort restrictions */
            Term[] arguments = new Term[node.getContents().size()];
            for (int i = 0; i < node.getContents().size(); ++i) {
                arguments[i] = (Term) node.getContents().get(i).accept(this);
            }
            return CollectionBuiltin.element(collectionSort, arguments);
        } else if (collectionSort.unitLabel().equals(kLabel)) {
            return CollectionBuiltin.empty(collectionSort);
        } else {
            /* custom function */
            return super.transform(node);
        }
    }

    @Override
    public ASTNode transform(KApp node) throws TransformerException {
        if (!(node.getLabel() instanceof KLabelConstant)) {
            /* only consider KLabel constants */
            return super.transform(node);
        }
        KLabelConstant kLabelConstant = (KLabelConstant) node.getLabel();

        if (!(node.getChild() instanceof KList)) {
                /* only consider KList constants */
            return super.transform(node);
        }
        KList kList = (KList) node.getChild();

        if (kLabelConstant.productions().size() != 1) {
            /* ignore KLabels associated with multiple productions */
            return super.transform(node);
        }
        Production production = kLabelConstant.productions().iterator().next();

        CollectionSort collectionSort = context.collectionSortOf(production.getSort());
        if (collectionSort == null) {
            return super.transform(node);
        }

        Term[] arguments = new Term[kList.getContents().size()];
        for (int i = 0; i < kList.getContents().size(); ++i) {
            arguments[i] = (Term) kList.getContents().get(i).accept(this);
        }

        if (collectionSort.constructorLabel().equals(kLabelConstant)) {
            CollectionBuiltin collection = CollectionBuiltin.of(collectionSort, arguments);
            if (collection.hasFrame() || collection.isElementCollection()) {
                return collection;
            } else {
                GlobalSettings.kem.register(new KException(
                        KException.ExceptionType.ERROR,
                        KException.KExceptionGroup.CRITICAL,
                        "unexpected left-hand side collection format; "
                        + "expected elements and at most one variable",
                        getName(),
                        node.getFilename(),
                        node.getLocation()));
                return null;
            }
        } else if (collectionSort.elementLabel().equals(kLabelConstant)) {
            /* TODO(andreis): check sort restrictions */
            return CollectionBuiltin.element(collectionSort, arguments);
        } else if (collectionSort.unitLabel().equals(kLabelConstant)) {
            if (kList.isEmpty()) {
                return CollectionBuiltin.empty(collectionSort);
            } else {
                GlobalSettings.kem.register(new KException(
                        KException.ExceptionType.ERROR,
                        KException.KExceptionGroup.CRITICAL,
                        "unexpected non-empty KList applied to constant KLabel " + kLabelConstant,
                        getName(),
                        node.getFilename(),
                        node.getLocation()));
                return super.transform(node);
            }
        } else {
            /* custom function */
            return super.transform(node);
        }

    }

}
