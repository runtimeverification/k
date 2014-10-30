// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.DataStructureBuiltin;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.MapUpdate;
import org.kframework.kil.Production;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KExceptionManager;
import java.util.Collections;
import java.util.Set;

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

    private ASTNode location;

    private final KExceptionManager kem;

    /**
     * Simplified constructor for the common case
     * @param context The context of the rules being compiled
     */
    public CompileDataStructures(Context context, KExceptionManager kem) {
        super("Compile collections to internal K representation", context);
        this.kem = kem;
    }

    @Override
    public ASTNode visit(Rule node, Void _)  {
        location = node;
        boolean change = false;

        Term body;
        if (node.getBody() instanceof Rewrite) {
            Rewrite rewrite = (Rewrite) node.getBody();
            Term lhs = (Term) this.visitNode(rewrite.getLeft());
            Term rhs = (Term) this.visitNode(rewrite.getRight());
            if (lhs != rewrite.getLeft() || rhs != rewrite.getRight()) {
                rewrite = rewrite.shallowCopy();
                rewrite.setLeft(lhs, context);
                rewrite.setRight(rhs, context);
            }
            body = rewrite;
        } else {
            body = (Term) this.visitNode(node.getBody());
        }
        if (body != node.getBody()) {
            change = true;
        }

        Term requires;
        if (node.getRequires() != null) {
            requires = (Term) this.visitNode(node.getRequires());
            if (requires != node.getRequires()) {
                change = true;
            }
        } else {
            requires = null;
        }

        Term ensures;
        if (node.getEnsures() != null) {
            ensures = (Term) this.visitNode(node.getEnsures());
            if (ensures != node.getEnsures()) {
                change = true;
            }
        } else {
            ensures = null;
        }

        if (!change) {
            return node;
        }

        node = node.shallowCopy();
        node.setBody(body);
        node.setRequires(requires);
        node.setEnsures(ensures);
        return node;
    }

    @Override
    public ASTNode visit(Rewrite node, Void _)  {
        assert false: "CompileDataStructures pass should be applied after ResolveRewrite pass";
        return node;
    }

    @Override
    public ASTNode visit(KApp node, Void _)  {
        node = (KApp) super.visit(node, _);
        if (!(node.getLabel() instanceof KLabelConstant)) {
            /* only consider KLabel constants */
            return node;
        }
        KLabelConstant kLabelConstant = (KLabelConstant) node.getLabel();

        if (!(node.getChild() instanceof KList)) {
            /* only consider KList constants */
            return node;
        }
        KList kList = (KList) node.getChild();

        Set<Production> productions = context.productionsOf(kLabelConstant.getLabel());
        if (productions.isEmpty()) {
            return node;
        }
        Production production = productions.iterator().next();

        DataStructureSort sort = context.dataStructureSortOf(production.getSort());
        if (sort == null) {
            return node;
        }

        Term[] arguments = new Term[kList.getContents().size()];
        for (int i = 0; i < kList.getContents().size(); ++i) {
            arguments[i] = (Term) this.visitNode(kList.getContents().get(i));
        }

        if (sort.constructorLabel().equals(kLabelConstant.getLabel())
                || sort.elementLabel().equals(kLabelConstant.getLabel())
                || sort.unitLabel().equals(kLabelConstant.getLabel())
                || sort.sort().equals(Sort.MAP)) {
            // TODO(AndreiS): the lines below should work once KLabelConstant are properly created
            if (productions.size() > 1) {
                kem.registerCompilerWarning(
                        "unable to transform the KApp: " + node
                        + "\nbecause of multiple productions associated:\n"
                        + productions,
                        this,
                        location);
            }
        }

        if (sort.constructorLabel().equals(kLabelConstant.getLabel())) {
            return DataStructureBuiltin.of(sort, arguments);
        } else if (sort.elementLabel().equals(kLabelConstant.getLabel())) {
            /* TODO(AndreiS): check sort restrictions */
            return DataStructureBuiltin.element(sort, arguments);
        } else if (sort.unitLabel().equals(kLabelConstant.getLabel())) {
            if (kList.isEmpty()) {
                return DataStructureBuiltin.empty(sort);
            } else {
                throw KExceptionManager.criticalError(
                        "unexpected non-empty KList applied to constant KLabel " + kLabelConstant,
                        this,
                        location);
            }
        } else if (sort.sort().equals(Sort.MAP)) {
            /* TODO(AndreiS): replace this with a more generic mechanism */
            if (kLabelConstant.getLabel().equals(sort.operatorLabels().get("update"))
                    && kList.getContents().size() == 3
                    && kList.getContents().get(0) instanceof Variable) {
                return new MapUpdate(
                        (Variable) kList.getContents().get(0),
                        Collections.<Term, Term>emptyMap(),
                        Collections.singletonMap(
                                kList.getContents().get(1),
                                kList.getContents().get(2)));
            }
            return node;
        } else {
            /* custom function */
            return node;
        }
    }

}
