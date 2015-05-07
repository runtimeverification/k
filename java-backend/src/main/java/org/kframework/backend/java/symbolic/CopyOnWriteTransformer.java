// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FloatToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;


/**
 * Performs transformation in post-order using a copy-on-write(COW) strategy.
 * This class serves as an adapter class: it provides a default post-order
 * traversal behavior for each KIL node and avoids constructing a new copy of
 * the target node to return unless it is actually going to be mutated.
 * <p>
 * COW strategy allows safe sub-term sharing.
 *
 * @author AndreiS
 */
public class CopyOnWriteTransformer implements Transformer {

    protected final TermContext context;
    protected final Definition definition;

    public CopyOnWriteTransformer(TermContext context) {
        this.context = context;
        this.definition = context.definition();
    }

    public CopyOnWriteTransformer() {
        this.context = null;
        this.definition = null;
    }

    @Override
    public String getName() {
        return this.getClass().toString();
    }

    @Override
    public ASTNode transform(CellCollection cellCollection) {
        boolean changed = false;
        CellCollection.Builder builder = CellCollection.builder(context.definition());
        for (CellCollection.Cell cell : cellCollection.cells().values()) {
            Term transformedContent = (Term) cell.content().accept(this);
            builder.put(cell.cellLabel(), transformedContent);
            changed = changed || cell.content() != transformedContent;
        }
        for (Term term : cellCollection.baseTerms()) {
            Term transformedTerm = (Term) term.accept(this);
            builder.concatenate(transformedTerm);
            changed = changed || term != transformedTerm;
        }
        return changed ? builder.build() : cellCollection;
    }

    @Override
    public ASTNode transform(Collection collection) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(ConstrainedTerm constrainedTerm) {
        Term term = (Term) constrainedTerm.term().accept(this);
        ConjunctiveFormula constraint = (ConjunctiveFormula) constrainedTerm.constraint().accept(this);
        if (term != constrainedTerm.term() || constraint != constrainedTerm.constraint()) {
            constrainedTerm = new ConstrainedTerm(term, constraint);
        }
        return constrainedTerm;
    }

    @Override
    public ASTNode transform(KLabelConstant kLabelConstant) {
        return kLabelConstant;
    }

    @Override
    public ASTNode transform(KLabelFreezer kLabelFreezer) {
        Term term = (Term) kLabelFreezer.term().accept(this);
        if (term != kLabelFreezer.term()) {
            kLabelFreezer = new KLabelFreezer(term);
        }
        return kLabelFreezer;
    }

    @Override
    public ASTNode transform(Hole hole) {
        return hole;
    }

    @Override
    public ASTNode transform(KLabelInjection kLabelInjection) {
        Term term = (Term) kLabelInjection.term().accept(this);
        if (term != kLabelInjection.term()) {
            kLabelInjection = new KLabelInjection(term);
        }
        return kLabelInjection;
    }

    @Override
    public ASTNode transform(InjectedKLabel injectedKLabel) {
        Term term = (Term) injectedKLabel.injectedKLabel().accept(this);
        if (term != injectedKLabel.injectedKLabel()) {
            injectedKLabel = new InjectedKLabel(term);
        }
        return injectedKLabel;
    }

    @Override
    public ASTNode transform(KItemProjection kItemProjection) {
        Term term = (Term) kItemProjection.term().accept(this);
        if (term != kItemProjection.term()) {
            kItemProjection = new KItemProjection(kItemProjection.kind(), term);
        }
        return kItemProjection;
    }

    @Override
    public ASTNode transform(KItem kItem) {
        Term kLabel = (Term) kItem.kLabel().accept(this);
        Term kList = (Term) kItem.kList().accept(this);
        if (kLabel != kItem.kLabel() || kList != kItem.kList()) {
            kItem = KItem.of(kLabel, kList, context, kItem.getSource(), kItem.getLocation());
        }
        return kItem;
    }

    @Override
    public ASTNode transform(Token token) {
        return token;
    }

    @Override
    public ASTNode transform(UninterpretedToken uninterpretedToken) {
        return transform((Token) uninterpretedToken);
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
    public ASTNode transform(IntToken intToken) {
        return transform((Token) intToken);
    }

    @Override
    public ASTNode transform(FloatToken floatToken) {
        return transform((Token) floatToken);
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
        return kLabel;
    }

    @Override
    public ASTNode transform(KList kList) {
        boolean changed = false;
        // transform the contents
        KList.Builder builder = KList.builder();
        for (Term term : kList) {
            Term transformedTerm = (Term) term.accept(this);
            if (transformedTerm != term) {
                changed = true;
            }
            builder.concatenate(transformedTerm);
        }

        if (kList.hasFrame()) {
            Variable frame = kList.frame();
            Term transformedFrame = (Term) frame.accept(this);
            if (transformedFrame != frame) {
                changed = true;
            }
            builder.concatenate(transformedFrame);
        }

        if (!changed) {
            return kList;
        } else {
            return builder.build();
        }
    }

    @Override
    public ASTNode transform(KSequence kSequence) {
        boolean changed = false;
        // transform the contents
        KSequence.Builder builder = KSequence.builder();
        for (Term term : kSequence) {
            Term transformedTerm = (Term) term.accept(this);
            if (transformedTerm != term) {
                changed = true;
            }
            builder.concatenate(transformedTerm);
        }

        if (kSequence.hasFrame()) {
            Variable frame = kSequence.frame();
            Term transformedFrame = (Term) frame.accept(this);
            if (transformedFrame != frame) {
                changed = true;
            }
            builder.concatenate(transformedFrame);
        }

        if (!changed) {
            return kSequence;
        } else {
            return builder.build();
        }
    }

    @Override
    public ASTNode transform(BuiltinList builtinList) {
        boolean changed = false;
        BuiltinList.Builder builder = BuiltinList.builder(context);
        for (Term term : builtinList.elementsLeft()) {
            Term transformedTerm = (Term) term.accept(this);
            changed = changed || (transformedTerm != term);
            builder.addItem(transformedTerm);
        }
        for (Term term : builtinList.baseTerms()) {
            Term transformedTerm = (Term) term.accept(this);
            changed = changed || (transformedTerm != term);
            builder.concatenate(transformedTerm);
        }
        for (Term term : builtinList.elementsRight()) {
            Term transformedTerm = (Term) term.accept(this);
            changed = changed || (transformedTerm != term);
            builder.addItem(transformedTerm);
        }
        return changed ? builder.build() : builtinList;
    }

    @Override
    public ASTNode transform(BuiltinMap builtinMap) {
        boolean changed = false;
        BuiltinMap.Builder builder = BuiltinMap.builder(context);

        for (Map.Entry<Term, Term> entry : builtinMap.getEntries().entrySet()) {
            Term key = (Term) entry.getKey().accept(this);
            Term value = (Term) entry.getValue().accept(this);

            // first time encounter a changed entry
            if (!changed && (key != entry.getKey() || value != entry.getValue())) {
                changed = true;
                // copy previous entries into the BuiltinMap being built
                for (Map.Entry<Term, Term> copy : builtinMap.getEntries().entrySet()) {
                    if (copy.equals(entry)) {
                        // cannot rely on reference identity check here
                        break;
                    }
                    builder.put(copy.getKey(), copy.getValue());
                }
            }

            if (changed) {
                builder.put(key, value);
            }
        }
        /* special case for maps composed only of entries */
        if (builtinMap.isConcreteCollection()) {
            return changed ? builder.build() : builtinMap;
        }

        if (!changed) {
            builder.putAll(builtinMap.getEntries());
        }

        for (Term term : builtinMap.baseTerms()) {
            Term transformedTerm = (Term) term.accept(this);
            changed = changed || (transformedTerm != term);
            builder.concatenate(transformedTerm);
        }

        return changed ? builder.build() : builtinMap;
    }

    @Override
    public ASTNode transform(BuiltinSet builtinSet) {
        boolean changed = false;
        BuiltinSet.Builder builder = BuiltinSet.builder(context);
        for(Term element : builtinSet.elements()) {
            Term transformedElement = (Term) element.accept(this);
            builder.add(transformedElement);
            changed = changed || (transformedElement != element);
        }
        for (Term term : builtinSet.baseTerms()) {
            Term transformedTerm = (Term) term.accept(this);
            changed = changed || (transformedTerm != term);
            builder.concatenate(transformedTerm);
        }
        return changed ? builder.build() : builtinSet;
    }

    @Override
    public ASTNode transform(MetaVariable metaVariable) {
        return transform((Token) metaVariable);
    }

    @Override
    public ASTNode transform(Rule rule) {
        Term processedLeftHandSide = (Term) rule.leftHandSide().accept(this);
        Term processedRightHandSide = (Term) rule.rightHandSide().accept(this);
        List<Term> processedRequires = new ArrayList<Term>(rule.requires().size());
        for (Term conditionItem : rule.requires()) {
            processedRequires.add((Term) conditionItem.accept(this));
        }
        List<Term> processedEnsures = new ArrayList<Term>(rule.ensures().size());
        for (Term conditionItem : rule.ensures()) {
            processedEnsures.add((Term) conditionItem.accept(this));
        }
        Set<Variable> processedFreshConstants = new HashSet<>(rule.freshConstants().size());
        for (Variable variable : rule.freshConstants()) {
            processedFreshConstants.add((Variable) variable.accept(this));
        }
        Set<Variable> processedFreshVariables = new HashSet<>(rule.freshVariables().size());
        for (Variable variable : rule.freshVariables()) {
            processedFreshVariables.add((Variable) variable.accept(this));
        }
        ConjunctiveFormula processedLookups
                = (ConjunctiveFormula) rule.lookups().accept(this);

        Map<CellLabel, Term> processedLhsOfReadCell = null;
        Map<CellLabel, Term> processedRhsOfWriteCell = null;
        if (rule.isCompiledForFastRewriting()) {
            processedLhsOfReadCell = new HashMap<>();
            for (Map.Entry<CellLabel, Term> entry : rule.lhsOfReadCell().entrySet()) {
                processedLhsOfReadCell.put(entry.getKey(), (Term) entry.getValue().accept(this));
            }
            processedRhsOfWriteCell = new HashMap<>();
            for (Map.Entry<CellLabel, Term> entry : rule.rhsOfWriteCell().entrySet()) {
                processedRhsOfWriteCell.put(entry.getKey(), (Term) entry.getValue().accept(this));
            }
        }

        if (processedLeftHandSide != rule.leftHandSide()
                || processedRightHandSide != rule.rightHandSide()
                || processedRequires.equals(rule.requires())
                || processedEnsures.equals(rule.ensures())
                || processedFreshConstants.equals(rule.freshConstants())
                || processedLookups != rule.lookups()) {
            return new Rule(
                    rule.label(),
                    processedLeftHandSide,
                    processedRightHandSide,
                    processedRequires,
                    processedEnsures,
                    processedFreshConstants,
                    processedFreshVariables,
                    processedLookups,
                    rule.isCompiledForFastRewriting(),
                    processedLhsOfReadCell,
                    processedRhsOfWriteCell,
                    rule.cellsToCopy(),
                    rule.matchingInstructions(),
                    rule,
                    context);
        } else {
            return rule;
        }
    }

    @Override
    public ASTNode transform(ConjunctiveFormula conjunctiveFormula) {
        ConjunctiveFormula transformedConjunctiveFormula = ConjunctiveFormula.of(context);

        for (Map.Entry<Variable, Term> entry : conjunctiveFormula.substitution().entrySet()) {
            transformedConjunctiveFormula = transformedConjunctiveFormula.add(
                    (Term) entry.getKey().accept(this),
                    (Term) entry.getValue().accept(this));
        }

        for (Equality equality : conjunctiveFormula.equalities()) {
            transformedConjunctiveFormula = transformedConjunctiveFormula.add(
                    (Term) equality.leftHandSide().accept(this),
                    (Term) equality.rightHandSide().accept(this));
        }

        for (DisjunctiveFormula disjunctiveFormula : conjunctiveFormula.disjunctions()) {
            transformedConjunctiveFormula = transformedConjunctiveFormula.add(
                    (DisjunctiveFormula) disjunctiveFormula.accept(this));
        }

        if (context.global().stage == Stage.REWRITING) {
            transformedConjunctiveFormula = transformedConjunctiveFormula.simplify();
        }
        return !transformedConjunctiveFormula.equals(conjunctiveFormula) ?
                transformedConjunctiveFormula :
                conjunctiveFormula;
    }

    @Override
    public ASTNode transform(DisjunctiveFormula disjunctiveFormula) {
        DisjunctiveFormula transformedDisjunctiveFormula = new DisjunctiveFormula(
                disjunctiveFormula.conjunctions().stream()
                        .map(c -> (ConjunctiveFormula) c.accept(this))
                        .collect(Collectors.toList()), context);
        return !transformedDisjunctiveFormula.equals(disjunctiveFormula) ?
                transformedDisjunctiveFormula :
                disjunctiveFormula;
    }

    @Override
    public ASTNode transform(Term node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(Variable variable) {
        return variable;
    }

}
