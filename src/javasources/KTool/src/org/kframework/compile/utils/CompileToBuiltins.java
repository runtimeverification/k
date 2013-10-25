package org.kframework.compile.utils;

import com.google.common.collect.ImmutableMap;
import org.kframework.kil.*;
import org.kframework.kil.List;
import org.kframework.kil.Map;
import org.kframework.kil.Set;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.*;

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
        builtinCollectionOps = new HashMap<>();
        builtinCollectionOps.put("_-Set_", "'_-MySet_");
        builtinCollectionOps.put("keys_", "'keys");

        builtinCollectionLabels = new HashMap<>();
        builtinCollectionLabels.put("inSet", "'_in_");

        undeclaredLabels = new HashSet<>();
    }


    public CompileToBuiltins(Context context) {
        super("Compile data structure into builtin data structures", context);    //To change body of overridden methods use File | Settings | File Templates.
    }

    @Override
    public ASTNode transform(Configuration node) throws TransformerException {
        ASTNode result = super.transform(node);
        return result;
    }

    @Override
    public ASTNode transform(KApp node) throws TransformerException {

        if (node.getLabel() instanceof  TermCons) {

            TermCons cons = (TermCons) node.getLabel();
            String label = context.conses.get(cons.getCons()).getLabel();
                if (label.equals("Set2KLabel_")) {
                    return cons.getContents().get(0).accept(this);
                }

        }

        if (node.getLabel() instanceof  KInjectedLabel) {
            Term term = ((KInjectedLabel)node.getLabel()).getTerm();

            if (isCollectionItem(term.getSort()) || isCollection(term.getSort())) {
                return term.accept(this);
            }
        }
        node = (KApp) super.transform(node);
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
    public ASTNode transform(List node) throws TransformerException {

        if (node.getContents().isEmpty()) {
            return new KApp(KLabelConstant.of("'.MyList"), KList.EMPTY);
        }

        java.util.List<Term> contents = transformTerms(node.getContents());

        return new KApp(KLabelConstant.of("'_List_"), new KList(contents));
    }

    @Override
    public ASTNode transform(Set node) throws TransformerException {

        if (node.getContents().isEmpty()) {
            return new KApp(KLabelConstant.of("'.MySet"), KList.EMPTY);
        }

        java.util.List<Term> contents = transformTerms(node.getContents());

        return new KApp(KLabelConstant.of("'_Set_"), new KList(contents));
    }


    @Override
    public ASTNode transform(Rule node) throws TransformerException {

//        if (node.getFilename().contains("include")) {
//            return node;
//        }

        ASTNode transform = super.transform(node);
        return transform;    //To change body of overridden methods use File | Settings | File Templates.
    }

    @Override
    public ASTNode transform(Map node) throws TransformerException {
//        System.out.println("TR: " + node);

        if (node.getContents().isEmpty()) {
//            return new Empty("MyMap");
            return new KApp(KLabelConstant.of("'.MyMap"), KList.EMPTY);
        }

        java.util.List<Term> contents = transformTerms(node.getContents());

        return new KApp(KLabelConstant.of("'_Map_"), new KList(contents));
    }

    @Override
    public ASTNode transform(TermCons node) throws TransformerException {
        String label = context.conses.get(node.getCons()).getLabel();
        if (!(isCollection(node.getSort()) || isCollectionItem(node.getSort()))){
            return super.transform(node);
        }

        if (label.equals("_[_/_]")) {
            java.util.List<Term> terms = node.getContents();
            java.util.List<Term> contents = transformTerms(terms);

            return KApp.of(KLabelConstant.of("'_[_<-_]"), contents.get(0), contents.get(2), contents.get(1));
        }

        return checkBuiltinOp(node, builtinCollectionOps);
    }

    private java.util.List<Term> transformTerms(java.util.List<Term> terms) throws TransformerException {
        java.util.List<Term> contents = new ArrayList<>();
        for(Term t : terms) {
            Term tnew = (Term)t.accept(this);
            if (tnew != null) {
                contents.add(tnew);
            }
        }
        return contents;
    }

    private ASTNode checkBuiltinOp(TermCons node, java.util.Map<String, String> labels) throws TransformerException {
        String label = context.conses.get(node.getCons()).getLabel();
        String newLabel = null;
        if (labels.containsKey(label)) {
            newLabel = labels.get(label);
        } else {
            newLabel = "'#" + node.getSort() + label;
            undeclaredLabels.add(newLabel);
        }

        java.util.List<Term> contents = transformTerms(node.getContents());

        return new KApp(KLabelConstant.of(newLabel), new KList(contents));
    }

    @Override
    public ASTNode transform(MapItem node) throws TransformerException {

//        System.out.println(node);

        Term key = (Term) node.getKey().accept(this);
        Term value = (Term) node.getValue().accept(this);

        java.util.List<Term> contents = new ArrayList<>();
        contents.add(key);
        contents.add(value);

        return new KApp(KLabelConstant.of("'_|->_"), new KList(contents));
    }

    @Override
    public ASTNode transform(ListItem node) throws TransformerException {
        java.util.List<Term> contents = new ArrayList<>();
        contents.add((Term) node.getItem().accept(this));
        return new KApp(KLabelConstant.of("'MyListItem"), new KList(contents));
    }

    @Override
    public ASTNode transform(SetItem node) throws TransformerException {
        java.util.List<Term> contents = new ArrayList<>();
        contents.add((Term) node.getItem().accept(this));
        return new KApp(KLabelConstant.of("'MySetItem"), new KList(contents));
    }

    private boolean isCollection(String sort) {
        return sort.equals(KSorts.MAP)
                || sort.equals(KSorts.LIST)
                || sort.equals(KSorts.SET);
    }

    private boolean isCollectionItem(String sort) {
        return  sort.equals(KSorts.MAP_ITEM)
                || sort.equals(KSorts.LIST_ITEM)
                || sort.equals(KSorts.SET_ITEM);
    }

    @Override
    public ASTNode transform(Variable node) throws TransformerException {

        if ( isCollection(node.getSort()) || isCollectionItem(node.getSort()))
        {
            // TODO:find a clever way to deal with anonymous variables for (List)Item
            if (node.isGenerated() && isCollectionItem(node.getSort())) {
                java.util.List<Term> contents = new ArrayList<>();
                contents.add(new Variable(node.getName(), KSorts.KITEM));
                return new KApp(KLabelConstant.of("'My" + node.getSort()), new KList(contents));
            }

            node = node.shallowCopy();
            node.setSort("My" + node.getSort());
            node.setExpectedSort(node.getSort());
        }

        return super.transform(node);    //To change body of overridden methods use File | Settings | File Templates.
    }

    @Override
    public ASTNode transform(Module node) throws TransformerException {

        Module result = (Module) super.transform(node);
        for (String label : undeclaredLabels) {
            result.addConstant(KSorts.KLABEL, label);
        }

        return result;
    }
}
