// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Configuration;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSorts;
import org.kframework.kil.List;
import org.kframework.kil.ListItem;
import org.kframework.kil.Map;
import org.kframework.kil.MapItem;
import org.kframework.kil.Module;
import org.kframework.kil.Rule;
import org.kframework.kil.Set;
import org.kframework.kil.SetItem;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

/**
 * Created with IntelliJ IDEA.
 * User: andrei.arusoaie
 * Date: 10/14/13
 * Time: 9:06 AM
 * To change this template use File | Settings | File Templates.
 */
public class CompileToBuiltins extends CopyOnWriteTransformer {

    private static java.util.Map<String,String> builtinCollectionOps;
    private static java.util.Map<String,String> builtinCollectionLabels;
    private static java.util.Set<String> undeclaredLabels;

    static {
        // TODO(YilongL): what about other ops in k-prelude.k, e.g., "inKList"?
        builtinCollectionOps = new HashMap<>();
        builtinCollectionOps.put("_-Set_", "'_-MySet_");
        builtinCollectionOps.put("#variables(_)", "#variables(_)");
        builtinCollectionOps.put("keys_", "'keys");

        // TODO(YilongL): 1) why change "inSet" to "'_in_"? 2) how can I know
        // this is the only case that needs to be changed? (just search
        // "klabel(" in k-prelude.k?) 3) shall we externalize strings in this
        // class?
        builtinCollectionLabels = new HashMap<>();
        builtinCollectionLabels.put("inSet", "'_in_");

        undeclaredLabels = new HashSet<>();
    }


    public CompileToBuiltins(Context context) {
        super("Compile data structure into builtin data structures", context);
    }

    @Override
    public ASTNode visit(Configuration node, Void _)  {
        ASTNode result = super.visit(node, _);
        return result;
    }

    @Override
    public ASTNode visit(KApp node, Void _)  {

        // TODO(YilongL): how can the K label of node be an instance of TermCons?
        if (node.getLabel() instanceof TermCons) {

            TermCons cons = (TermCons) node.getLabel();
            String label = getLabelOf(cons);
            if (label.equals("Set2KLabel_")) {
                return this.visitNode(cons.getContents().get(0));
            }

        }

        if (node.getLabel() instanceof  KInjectedLabel) {
            Term term = ((KInjectedLabel)node.getLabel()).getTerm();

            if (isCollectionItem(term.getSort()) || isCollection(term.getSort())) {
                // e.g., when node = "# Env : Map ()", return "Env : MyMap";
                // or when node = "# GeneratedFreshVar704:SetItem ()", return "'MySetItem(GeneratedFreshVar557:KItem)"
                // note: node like "# C:Bag ()" is left to be transformed in later pass
                return this.visitNode(term);
            }
        }
        node = (KApp) super.visit(node, _);
        if (node.getLabel() instanceof KLabelConstant) {
            KLabelConstant label = (KLabelConstant) node.getLabel();
            String newLabel = builtinCollectionLabels.get(label.getLabel());
            if (newLabel != null) {
                node = new KApp(KLabelConstant.of(newLabel), node.getChild());
            }
        }
        return node;
    }

    @Override
    public ASTNode visit(List node, Void _)  {

        if (node.getContents().isEmpty()) {
            return new KApp(KLabelConstant.of("'.MyList"), KList.EMPTY);
        }

        java.util.List<Term> contents = transformTerms(node.getContents());

        return new KApp(KLabelConstant.of("'_List_"), new KList(contents));
    }

    @Override
    public ASTNode visit(Set node, Void _)  {

        if (node.getContents().isEmpty()) {
            return new KApp(KLabelConstant.of("'.MySet"), KList.EMPTY);
        }

        java.util.List<Term> contents = transformTerms(node.getContents());

        return new KApp(KLabelConstant.of("'_Set_"), new KList(contents));
    }


    @Override
    public ASTNode visit(Rule node, Void _)  {
        // TODO(YilongL): why not transform the rule from /include directory? is
        // it because this will be filtered out by TagUserRules anyway? However,
        // this stage is used also by the Java backend which also uses io.k
        if (node.getFilename().contains("include")) {
            return node;
        }

        ASTNode transform = super.visit(node, _);
        return transform;
    }

    @Override
    public ASTNode visit(Map node, Void _)  {
//        System.out.println("TR: " + node);

        if (node.getContents().isEmpty()) {
//            return new Empty("MyMap");
            return new KApp(KLabelConstant.of("'.MyMap"), KList.EMPTY);
        }

        java.util.List<Term> contents = transformTerms(node.getContents());

        return new KApp(KLabelConstant.of("'_Map_"), new KList(contents));
    }

    @Override
    public ASTNode visit(TermCons node, Void _)  {
        String label = getLabelOf(node);
        
        // do not transform this TermCons unless it represents a Collection/CollectionItem node
        if (!(isCollection(node.getSort()) || isCollectionItem(node.getSort()))){
            return super.visit(node, _);
        }

        // handle map update individually because the arguments need to be reordered
        if (label.equals("_[_/_]")) {
            java.util.List<Term> terms = node.getContents();
            java.util.List<Term> contents = transformTerms(terms);

            Term map = contents.get(0);
            Term keyList = contents.get(2);
            Term valueList = contents.get(1);
            assert keyList instanceof KList : "Expecting a KList here";
            Term key = ((KList) keyList).getContents().get(0);
            assert valueList instanceof KList : "Expecting a KList here";
            Term value = ((KList) valueList).getContents().get(0);
            return KApp.of(KLabelConstant.of("'_[_<-_]"), map, key, value);
        } else {
            return transformBuiltinOp(node);
        }
    }

    /**
     * Returns the K label of the specified {@code TermCons}.
     * 
     * @param node
     *            the specified TermCons
     * @return the K label
     */
    private String getLabelOf(TermCons node) {
        return context.conses.get(node.getCons()).getLabel();
    }

    private java.util.List<Term> transformTerms(java.util.List<Term> terms)  {
        java.util.List<Term> contents = new ArrayList<>();
        for(Term t : terms) {
            Term tnew = (Term) this.visitNode(t);
            if (tnew != null) {
                contents.add(tnew);
            }
        }
        return contents;
    }

    private ASTNode transformBuiltinOp(TermCons node)  {
        String label = getLabelOf(node);
        String newLabel = null;
        // pre-defined K label, e.g., @see builtinCollectionOps
        if (builtinCollectionOps.containsKey(label)) {
            newLabel = builtinCollectionOps.get(label);
        } 
        // user-defined K label, e.g., extendMap(_,_,_,_) in "syntax Map ::= extendMap(Map, Int, Int, K)
        else {
            newLabel = "'#" + node.getSort() + label;
            undeclaredLabels.add(newLabel);
        }

        java.util.List<Term> contents = transformTerms(node.getContents());

        return new KApp(KLabelConstant.of(newLabel), new KList(contents));
    }

    @Override
    public ASTNode visit(MapItem node, Void _)  {

//        System.out.println(node);

        Term key = (Term) this.visitNode(node.getKey());
        Term value = (Term) this.visitNode(node.getValue());

        java.util.List<Term> contents = new ArrayList<>();
        contents.add(key);
        contents.add(value);

        return new KApp(KLabelConstant.of("'_|->_"), new KList(contents));
    }

    @Override
    public ASTNode visit(ListItem node, Void _)  {
        java.util.List<Term> contents = new ArrayList<>();
        contents.add((Term) this.visitNode(node.getItem()));
        return new KApp(KLabelConstant.of("'MyListItem"), new KList(contents));
    }

    @Override
    public ASTNode visit(SetItem node, Void _)  {
        java.util.List<Term> contents = new ArrayList<>();
        contents.add((Term) this.visitNode(node.getItem()));
        return new KApp(KLabelConstant.of("'MySetItem"), new KList(contents));
    }

    private boolean isCollection(String sort) {
        // TODO(YilongL): why doesn't "Bag" count?
        return sort.equals(KSorts.MAP)
                || sort.equals(KSorts.LIST)
                || sort.equals(KSorts.SET);
    }

    private boolean isCollectionItem(String sort) {
        // TODO(YilongL): why doesn't "BagItem" count? Because a cell is not
        // wrapped inside "BagItem(_)"?
        return  sort.equals(KSorts.MAP_ITEM)
                || sort.equals(KSorts.LIST_ITEM)
                || sort.equals(KSorts.SET_ITEM);
    }

    @Override
    public ASTNode visit(Variable node, Void _)  {

        if (isCollectionItem(node.getSort())) {
            // TODO:find a clever way to deal with anonymous variables for (List)Item
            
            // TODO(YilongL): in my opinion, it is not very intuitive why we
            // need to treat anonymous variable differently?
            
            // transform generated fresh variable of collection item to K
            // application, e.g., GeneratedFreshVarX:SetItem =>
            // 'MySetItem(GeneratedFreshX:KItem)
            if (node.isGenerated()) {
                java.util.List<Term> contents = new ArrayList<>();
                contents.add(new Variable(node.getName(), KSorts.KITEM));
                return new KApp(KLabelConstant.of("'My" + node.getSort()), new KList(contents));
            } else {
                node = node.shallowCopy();
                node.setSort("My" + node.getSort());
                node.setExpectedSort(node.getSort());
            }
        } else if (isCollection(node.getSort())) {
            node = node.shallowCopy();
            node.setSort("My" + node.getSort());
            node.setExpectedSort(node.getSort());
        }

        return super.visit(node, _);
    }

    @Override
    public ASTNode visit(Module node, Void _)  {

        Module result = (Module) super.visit(node, _);
        for (String label : undeclaredLabels) {
            // declare newly generated K labels, e.g., syntax KLabel ::= "'#MapextendMap(_,_,_,_)"
            result.addConstant(KSorts.KLABEL, label);
        }

        return result;
    }
}
