// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FloatToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.ListBuiltin;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.SetBuiltin;
import org.kframework.kil.Sort;
import org.kframework.kil.loader.Context;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;


/**
 * Convert a term from the Java Rewrite engine internal representation into the KIL representation.
 *
 * @author: AndreiS
 */
public class BackendJavaKILtoKILTransformer implements Transformer {

    private final Context context;
    private final ConfigurationStructureMap configurationStructureMap;
    private final IdentityHashMap<Term, ASTNode> cache = new IdentityHashMap<>();
    /**
     * List of expected cell labels, in the oder in which they appear in the configuration.
     * Used to ensure deterministic order of cells when translating
     * a {@link org.kframework.backend.java.kil.CellCollection} to a {@link org.kframework.kil.Bag}.
     */
    private List<String> currentCellLabels;

    public BackendJavaKILtoKILTransformer(Context context) {
        this.context = context;
        configurationStructureMap = context.getConfigurationStructureMap();
        currentCellLabels = Collections.emptyList();
    }

    @Override
    public String getName() {
        return this.getClass().toString();
    }

    /**
     * Private helper method that translates Java backend specific KIL term back
     * to generic KIL term.
     *
     * @param term
     *            the term to be translated
     * @return the translated term
     */
    private ASTNode transformJavaBackendSpecificTerm(Term term) {
        if (cache.containsKey(term)) return cache.get(term);
        ASTNode kil = new org.kframework.kil.BackendTerm(term.sort().toFrontEnd(), term.toString());
        kil.copyAttributesFrom(term);
        cache.put(term, kil);
        return kil;
    }

    @Override
    public ASTNode transform(CellCollection cellCollection) {
        if (cache.containsKey(cellCollection)) return cache.get(cellCollection);
        Set<CellLabel> cellLabels = !currentCellLabels.isEmpty() ?
                currentCellLabels.stream().map(CellLabel::of).collect(Collectors.toSet()) :
                cellCollection.cells().keySet();

        List<org.kframework.kil.Term> contents = new ArrayList<>();
        for (CellLabel cellLabel : cellLabels) {
            for (CellCollection.Cell cell : cellCollection.cells().get(cellLabel)) {
                contents.add(transformCell(cell));
            }
        }
        if (cellCollection.hasFrame()) {
            contents.add((org.kframework.kil.Term) cellCollection.frame().accept(this));
        }

        if (contents.size() == 1 && contents.get(0) instanceof Cell) {
            return contents.get(0);
        }

        ASTNode kil = new org.kframework.kil.Bag(contents);
        kil.copyAttributesFrom(cellCollection);
        cache.put(cellCollection, kil);
        return kil;
    }

    private org.kframework.kil.Cell transformCell(CellCollection.Cell cell) {
        // TODO(AndreiS): fix the printing of the cells which are representing maps
        CellLabel label = cell.cellLabel();
        Term content = cell.content();
        if (content instanceof CellCollection) {
            if (label.isMapCell()) {
                currentCellLabels = configurationStructureMap.get(label.getRealCellLabel().name()).cell.getCellLabels();
            } else {
                currentCellLabels = configurationStructureMap.get(label.name()).cell.getCellLabels();
            }
        } else {
            currentCellLabels = Collections.emptyList();
        }

        org.kframework.kil.Cell returnCell = new org.kframework.kil.Cell();
        returnCell.setLabel(label.name());
        returnCell.setEndLabel(label.name());
        returnCell.setContents((org.kframework.kil.Term) content.accept(this));
        // TODO(AndreiS): what cell attributes are preserved by the backend?
        // returnCell.copyAttributesFrom(cell);
        return returnCell;
    }

    @Override
    public ASTNode transform(Hole hole) {
        //return new org.kframework.kil.FreezerHole(0);
        return org.kframework.kil.Hole.KITEM_HOLE;
    }

    @Override
    public ASTNode transform(KItem kItem) {
        if (cache.containsKey(kItem)) return cache.get(kItem);
        ASTNode kil = new org.kframework.kil.KApp(
                (org.kframework.kil.Term) kItem.kLabel().accept(this),
                (org.kframework.kil.Term) kItem.kList().accept(this));
        kil.copyAttributesFrom(kItem);
        cache.put(kItem, kil);
        return kil;
    }

    @Override
    public ASTNode transform(KItemProjection kItemProj) {
        if (cache.containsKey(kItemProj)) return cache.get(kItemProj);
        ASTNode kil = new org.kframework.kil.KItemProjection(
                Sort.of(kItemProj.kind().toString()),
                (org.kframework.kil.Term) kItemProj.term().accept(this));
        kil.copyAttributesFrom(kItemProj);
        cache.put(kItemProj, kil);
        return kil;
    }

    @Override
    public ASTNode transform(KLabelConstant kLabelConstant) {
        if (cache.containsKey(kLabelConstant)) return cache.get(kLabelConstant);
        ASTNode kil = org.kframework.kil.KLabelConstant.of(kLabelConstant.label());
        kil.copyAttributesFrom(kLabelConstant);
        cache.put(kLabelConstant, kil);
        return kil;
    }

    @Override
    public ASTNode transform(KLabelFreezer kLabelFreezer) {
        if (cache.containsKey(kLabelFreezer)) return cache.get(kLabelFreezer);
        ASTNode kil = new org.kframework.kil.FreezerLabel(
                (org.kframework.kil.Term) kLabelFreezer.term().accept(this));
        kil.copyAttributesFrom(kLabelFreezer);
        cache.put(kLabelFreezer, kil);
        return kil;
    }

    @Override
    public ASTNode transform(KLabelInjection kLabelInjection) {
        if (cache.containsKey(kLabelInjection)) return cache.get(kLabelInjection);
        ASTNode kil = new org.kframework.kil.KInjectedLabel(
                (org.kframework.kil.Term) kLabelInjection.term().accept(this));
        kil.copyAttributesFrom(kLabelInjection);
        cache.put(kLabelInjection, kil);
        return kil;
    }

    @Override
    public ASTNode transform(KList kList) {
        if (cache.containsKey(kList)) return cache.get(kList);
        List<org.kframework.kil.Term> terms = transformTerms(kList);
        ASTNode kil = new org.kframework.kil.KList(terms);
        kil.copyAttributesFrom(kList);
        cache.put(kList, kil);
        return kil;
    }

    @Override
    public ASTNode transform(KSequence kSequence) {
        if (cache.containsKey(kSequence)) return cache.get(kSequence);
        List<org.kframework.kil.Term> terms = transformTerms(kSequence);
        ASTNode kil = new org.kframework.kil.KSequence(terms);
        kil.copyAttributesFrom(kSequence);
        cache.put(kSequence, kil);
        return kil;
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
        if (cache.containsKey(set)) return cache.get(set);
        List<org.kframework.kil.Term> elements = new ArrayList<org.kframework.kil.Term>();
        List<org.kframework.kil.Term> baseTerms = new ArrayList<org.kframework.kil.Term>();
        for (Term entry : set.elements()) {
            elements.add((org.kframework.kil.Term)entry.accept(this));
        }
        Collections.sort(elements);
        for (Term term : set.baseTerms()) {
            baseTerms.add((org.kframework.kil.Term) term.accept(this));
        }
        ASTNode kil = new SetBuiltin(
                context.dataStructureSortOf(DataStructureSort.DEFAULT_SET_SORT),
                baseTerms,
                elements);
        kil.copyAttributesFrom(set);
        cache.put(set, kil);
        return kil;
    }


    @Override
    public ASTNode transform(BuiltinList builtinList) {
        if (cache.containsKey(builtinList)) return cache.get(builtinList);
        List<org.kframework.kil.Term> elementsLeft = new ArrayList<org.kframework.kil.Term>();
        List<org.kframework.kil.Term> baseTerms = new ArrayList<org.kframework.kil.Term>();
        List<org.kframework.kil.Term> elementsRight = new ArrayList<org.kframework.kil.Term>();
        for (Term entry : builtinList.elementsLeft()) {
            elementsLeft.add((org.kframework.kil.Term)entry.accept(this));
        }
        for (Term term : builtinList.baseTerms()) {
            baseTerms.add((org.kframework.kil.Term) term.accept(this));
        }
        for (Term entry : builtinList.elementsRight()) {
            elementsRight.add((org.kframework.kil.Term)entry.accept(this));
        }
        ASTNode kil = ListBuiltin.of(context.dataStructureSortOf(DataStructureSort.DEFAULT_LIST_SORT),
                baseTerms, elementsLeft, elementsRight);
        kil.copyAttributesFrom(builtinList);
        cache.put(builtinList, kil);
        return kil;
    }

    @Override
    public ASTNode transform(BuiltinMap map) {
        if (cache.containsKey(map)) return cache.get(map);
        final Map<Term, Term> entries = map.getEntries();
        List<Term> keys = new ArrayList<Term>(entries.keySet());
        Collections.sort(keys);
        Map<org.kframework.kil.Term, org.kframework.kil.Term> elements = new HashMap<>();
        List<org.kframework.kil.Term> baseTerms = new ArrayList<>();
        for (Term key : keys) {
            Term value = entries.get(key);
            elements.put(
                    (org.kframework.kil.Term) key.accept(this),
                    (org.kframework.kil.Term) value.accept(this));
        }
        for (Term term : map.baseTerms()) {
            baseTerms.add((org.kframework.kil.Term) term.accept(this));
        }
        ASTNode kil = new MapBuiltin(
                context.dataStructureSortOf(DataStructureSort.DEFAULT_MAP_SORT),
                baseTerms,
                elements);
        kil.copyAttributesFrom(map);
        cache.put(map, kil);
        return kil;
    }

    @Override
    public ASTNode transform(Token token) {
        if (cache.containsKey(token)) return cache.get(token);
        ASTNode kil = org.kframework.kil.Token.kAppOf(token.sort().toFrontEnd(), token.value());
        kil.copyAttributesFrom(token);
        cache.put(token, kil);
        return kil;
    }

    @Override
    public ASTNode transform(Variable variable) {
        if (cache.containsKey(variable)) return cache.get(variable);
//        System.out.println("VARIABLE*************"+ variable.name()+"->"+variable.sort());
        ASTNode node = new org.kframework.kil.Variable(variable.name(), variable.sort().toFrontEnd());
//        System.out.println("NODE: "+node.toString());
//        System.out.println("**********VARIABLE"+ variable.name()+"->"+variable.sort());
        node.copyAttributesFrom(variable);
        cache.put(variable, node);
        return node;
    }

    @Override
    public ASTNode transform(InjectedKLabel injectedKLabel) {
        throw new AssertionError("should be unreachable");
    }

    @Override
    public ASTNode transform(BitVector bitVector) {
        return transform((Token) bitVector);
    }

    @Override
    public ASTNode transform(BoolToken boolToken) {
        return transform((Token) boolToken);
    }

    @Override
    public ASTNode transform(Collection collection) {
        throw new UnsupportedOperationException("This method should never be called");
    }

    @Override
    public ASTNode transform(ConstrainedTerm constrainedTerm) {
        throw new UnsupportedOperationException("Not implemented, yet");
    }

    @Override
    public ASTNode transform(FloatToken floatToken) {
        return transform((Token) floatToken);
    }

    @Override
    public ASTNode transform(IntToken intToken) {
        return transform((Token) intToken);
    }

    @Override
    public ASTNode transform(KCollection kCollection) {
        throw new UnsupportedOperationException("This method should never be called");
    }

    @Override
    public ASTNode transform(KLabel kLabel) {
        throw new UnsupportedOperationException("This method should never be called");
    }

    @Override
    public ASTNode transform(MetaVariable metaVariable) {
        return transform((Token) metaVariable);
    }

    @Override
    public ASTNode transform(Rule rule) {
        throw new UnsupportedOperationException("Not implemented, yet");
    }

    @Override
    public ASTNode transform(ConjunctiveFormula conjunctiveFormula) {
        throw new UnsupportedOperationException("Not implemented, yet");
    }

    @Override
    public ASTNode transform(DisjunctiveFormula disjunctiveFormula) {
        throw new UnsupportedOperationException("Not implemented, yet");
    }

    @Override
    public ASTNode transform(StringToken stringToken) {
        return transform((Token) stringToken);
    }

    @Override
    public ASTNode transform(Term node) {
        throw new UnsupportedOperationException("This method should never be called");
    }

    @Override
    public ASTNode transform(UninterpretedToken uninterpretedToken) {
        return transform((Token) uninterpretedToken);
    }

}
