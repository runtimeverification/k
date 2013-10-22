package org.kframework.backend.java.symbolic;

import com.google.common.collect.Multimap;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;


/**
 * Convert a term from the Java Rewrite engine internal representation into the KIL representation.
 *
 * @author: AndreiS
 */
public class BackendJavaKILtoKILTranslation extends CopyOnWriteTransformer {

    private final Context context;
    private final ConfigurationStructureMap configurationStructureMap;
    private org.kframework.kil.Cell currentCell;

    public BackendJavaKILtoKILTranslation(Context context) {
        this.context = context;
        configurationStructureMap = context.getConfigurationStructureMap();
    }

    @Override
    public ASTNode transform(Cell cell) {
        org.kframework.kil.Cell returnCell = new org.kframework.kil.Cell();
        final String label = cell.getLabel();
        currentCell = configurationStructureMap.get(label).cell;
        returnCell.setLabel(label);
        returnCell.setEndLabel(label);
        returnCell.setContents((org.kframework.kil.Term) cell.getContent().accept(this));
        return returnCell;
    }

    @Override
    public ASTNode transform(CellCollection cellCollection) {
        final Multimap<String,Cell> cellMap = cellCollection.cellMap();
        List<org.kframework.kil.Term> terms = currentCell.getCellTerms();
        List<org.kframework.kil.Term> contents = new ArrayList<org.kframework.kil.Term>();
        for (org.kframework.kil.Term term : terms) {
            if (! (term instanceof org.kframework.kil.Cell)) continue;
            String key = ((org.kframework.kil.Cell) term).getLabel();
            for (Cell cell : cellMap.get(key)) {
                contents.add((org.kframework.kil.Cell) transform(cell));
            }
        }
        if (cellCollection.hasFrame()) {
            contents.add((org.kframework.kil.Term) cellCollection.frame().accept(this));
        }
        return new org.kframework.kil.Bag(contents);
    }

    @Override
    public ASTNode transform(Hole hole) {
        //return new org.kframework.kil.FreezerHole(0);
        return org.kframework.kil.Hole.KITEM_HOLE;
    }

    @Override
    public ASTNode transform(KItem kItem) {
        return new org.kframework.kil.KApp(
                (org.kframework.kil.Term) kItem.kLabel().accept(this),
                (org.kframework.kil.Term) kItem.kList().accept(this));
    }

    @Override
    public ASTNode transform(KLabelConstant kLabelConstant) {
        return org.kframework.kil.KLabelConstant.of(kLabelConstant.label(), context);
    }

    @Override
    public ASTNode transform(KLabelFreezer kLabelFreezer) {
        return new org.kframework.kil.FreezerLabel(
                (org.kframework.kil.Term) kLabelFreezer.term().accept(this));
    }

    @Override
    public ASTNode transform(KLabelInjection kLabelInjection) {
        return new org.kframework.kil.KInjectedLabel(
                (org.kframework.kil.Term) kLabelInjection.term().accept(this));
    }

    @Override
    public ASTNode transform(KList kList) {
        List<org.kframework.kil.Term> terms = transformTerms(kList);
        return new org.kframework.kil.KList(terms);
    }

    @Override
    public ASTNode transform(KSequence kSequence) {
        List<org.kframework.kil.Term> terms = transformTerms(kSequence);
        return new org.kframework.kil.KSequence(terms);
    }

    private List<org.kframework.kil.Term> transformTerms(KCollection kCollection) {
        List<org.kframework.kil.Term> terms = new ArrayList<org.kframework.kil.Term>();
        for (Term term : kCollection) {
            terms.add((org.kframework.kil.Term) term.accept(this));
        }
        if (kCollection.hasFrame()) {
            terms.add((org.kframework.kil.Term) kCollection.frame().accept(this));
        }
        return terms;
    }

    @Override
    public ASTNode transform(BuiltinSet set) {
        // TODO(AndreiS): use BuiltinMap
        List<org.kframework.kil.Term> items = new ArrayList<org.kframework.kil.Term>();
        for (Term entry : set.elements()) {
            items.add(new org.kframework.kil.SetItem(
                    (org.kframework.kil.Term) entry.accept(this)));
        }
        Collections.sort(items);
        if (set.hasFrame()) {
            items.add((org.kframework.kil.Term) set.frame().accept(this));
        }
        return new org.kframework.kil.Set(items);
    }

     @Override
    public ASTNode transform(BuiltinList builtinList) {
        // TODO(AndreiS): use BuiltinList
        List<org.kframework.kil.Term> items = new ArrayList<org.kframework.kil.Term>();
        for (Term entry : builtinList.elementsLeft()) {
            items.add(new org.kframework.kil.ListItem(
                    (org.kframework.kil.Term) entry.accept(this)));
        }
         if (builtinList.hasFrame()) {
             items.add((org.kframework.kil.Term) builtinList.frame().accept(this));
         }
        for (Term entry : builtinList.elementsRight()) {
            items.add(new org.kframework.kil.ListItem(
                    (org.kframework.kil.Term) entry.accept(this)));
        }
        return new org.kframework.kil.List(items);
    }

    @Override
    public ASTNode transform(BuiltinMap map) {
        // TODO(AndreiS): use BuiltinMap
        final Map<Term, Term> entries = map.getEntries();
        List<Term> keys = new ArrayList<Term>(entries.keySet());
        Collections.sort(keys);
        List<org.kframework.kil.Term> items = new ArrayList<org.kframework.kil.Term>();
        for (Term key : keys) {
            Term value = entries.get(key);
            items.add(new org.kframework.kil.MapItem(
                    (org.kframework.kil.Term) key.accept(this),
                    (org.kframework.kil.Term) value.accept(this)));
        }
        if (map.hasFrame()) {
            items.add((org.kframework.kil.Term) map.frame().accept(this));
        }
        return new org.kframework.kil.Map(items);
    }

    @Override
    public ASTNode transform(Token token) {
        return org.kframework.kil.Token.kAppOf(token.sort(), token.value());
    }

    @Override
    public ASTNode transform(Variable variable) {
//        System.out.println("VARIABLE*************"+ variable.name()+"->"+variable.sort());
        ASTNode node = new org.kframework.kil.Variable(variable.name(), variable.sort());
//        System.out.println("NODE: "+node.toString());
//        System.out.println("**********VARIABLE"+ variable.name()+"->"+variable.sort());
        return node;
    }

}
