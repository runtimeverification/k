package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.DataStructureBuiltin;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSorts;
import org.kframework.kil.MapUpdate;
import org.kframework.kil.Production;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.Collections;


/**
 * Transformer class compiling collection (bag, list, map and set) terms into K internal
 * representation. It traverses the AST bottom-up and upon encountering a KLabel hooked to a
 * primitive data structure operation (constructor, element, unit) it creates a {@link
 * DataStructureBuiltin} instance representing the respective data structure. In particular the
 * constructor operation requires both argument to be already compiled into data structures of
 * the same sort.
 *
 * @see DataStructureSort
 * @see DataStructureBuiltin
 *
 * @author AndreiS
 */
public class CompileDataStructures extends CopyOnWriteTransformer {

    private enum Status { LHS, RHS, CONDITION }

    private Status status;

    public CompileDataStructures(Context context) {
        super("Compile collections to internal K representation", context);
    }

    @Override
    public ASTNode transform(Rule node) throws TransformerException {
        assert node.getBody() instanceof Rewrite :
                "expected rewrite at the top of rule\n" + node + "\n"
                + "CompileDataStructures pass should be applied after ResolveRewrite pass";

        Rewrite rewrite = (Rewrite) node.getBody();
        status = Status.LHS;
        Term lhs = (Term) rewrite.getLeft().accept(this);
        status = Status.RHS;
        Term rhs = (Term) rewrite.getRight().accept(this);
        Term requires;
        if (node.getRequires() != null) {
            status = Status.CONDITION;
            requires = (Term) node.getRequires().accept(this);
        } else {
            requires = null;
        }
        
        //TODO: handle ensures, too.

        if (lhs == rewrite.getLeft()
            && rhs == rewrite.getRight()
            && requires == node.getRequires()) {
            return node;
        }

        node = node.shallowCopy();
        rewrite = rewrite.shallowCopy();
        node.setBody(rewrite);
        rewrite.setLeft(lhs, context);
        rewrite.setRight(rhs, context);
        node.setRequires(requires);
        return node;
    }

    @Override
    public ASTNode transform(Rewrite node) throws TransformerException {
        assert false: "CompileDataStructures pass should be applied after ResolveRewrite pass";
        return node;
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

        // TODO(AndreiS): the lines below should work one KLabelConstant are properly created
        //if (kLabelConstant.productions().size() != 1) {
        //    /* ignore KLabels associated with multiple productions */
        //    return super.transform(node);
        //}
        //Production production = kLabelConstant.productions().iterator().next();

        if (context.productionsOf(kLabelConstant.getLabel()).size() != 1) {
            /* ignore KLabels associated with multiple productions */
            return super.transform(node);
        }
        Production production = context.productionsOf(kLabelConstant.getLabel()).iterator().next();

        DataStructureSort sort = context.dataStructureSortOf(production.getSort());
        if (sort == null) {
            return super.transform(node);
        }

        Term[] arguments = new Term[kList.getContents().size()];
        for (int i = 0; i < kList.getContents().size(); ++i) {
            arguments[i] = (Term) kList.getContents().get(i).accept(this);
        }

        if (sort.constructorLabel().equals(kLabelConstant.getLabel())) {
            DataStructureBuiltin dataStructure = DataStructureBuiltin.of(sort, arguments);
            if (status == Status.LHS && !dataStructure.isLHSView()) {
                GlobalSettings.kem.register(new KException(
                        KException.ExceptionType.ERROR,
                        KException.KExceptionGroup.CRITICAL,
                        "unexpected left-hand side data structure format; "
                        + "expected elements and at most one variable\n"
                        + node,
                        getName(),
                        node.getFilename(),
                        node.getLocation()));
                return null;
            }
            return dataStructure;
        } else if (sort.elementLabel().equals(kLabelConstant.getLabel())) {
            /* TODO(AndreiS): check sort restrictions */
            return DataStructureBuiltin.element(sort, arguments);
        } else if (sort.unitLabel().equals(kLabelConstant.getLabel())) {
            if (kList.isEmpty()) {
                return DataStructureBuiltin.empty(sort);
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
        } else if (sort.type().equals(KSorts.MAP)) {
            /* TODO(AndreiS): replace this with a more generic mechanism */
            try {
                if (sort.operatorLabels().get("update").equals(kLabelConstant.getLabel())) {
                    return new MapUpdate(
                            (Variable) kList.getContents().get(0),
                            Collections.<Term, Term>emptyMap(),
                            Collections.singletonMap(
                                    kList.getContents().get(1),
                                    kList.getContents().get(2)));
                }
            } catch (Exception e) { }
            return super.transform(node);
        } else {
            /* custom function */
            return super.transform(node);
        }
    }

}
