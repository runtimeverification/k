// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FloatToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.utils.BitSet;
import org.kframework.builtin.KLabels;

import java.util.ArrayList;
import java.util.Arrays;
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
public abstract class CopyOnWriteTransformer implements Transformer {

    private static final String KSEQUENCE_KLABEL = "#KSequence";
    protected final TermContext context;

    public CopyOnWriteTransformer(TermContext context) {
        this.context = context;
    }

    public CopyOnWriteTransformer() {
        this(null);
    }

    @Override
    public String getName() {
        return this.getClass().toString();
    }

    /**
     * Decides whether to use the {@link GlobalContext} carried by {@code term}
     * or the one provided externally in {@link CopyOnWriteTransformer#context}.
     * <p>
     * YilongL: I think we should eventually get rid of {@code TermContext} from
     * this class and always use the {@code GlobalContext} carried in {@code term}.
     * This requires us to properly reset the data inside {@code GlobalContext} after
     * deserialization. However, a single {@link Definition} is currently shared
     * between multiple KRun instances in kserver mode so the reset cannot be easily
     * done and we have to rely on such ad-hoc mechanism to bypass the invalid
     * {@code GlobalContext} inside those {@code term}'s that belong to the
     * {@code Definition} object.
     * </p>
     */
    private GlobalContext resolveGlobalContext(HasGlobalContext term) {
        return context == null ? term.globalContext() : context.global();
    }

    @Override
    public JavaSymbolicObject transform(Collection collection) {
        throw new UnsupportedOperationException();
    }

    @Override
    public JavaSymbolicObject transform(ConstrainedTerm constrainedTerm) {
        Term term = (Term) constrainedTerm.term().accept(this);
        ConjunctiveFormula constraint = (ConjunctiveFormula) constrainedTerm.constraint().accept(this);
        if (term != constrainedTerm.term() || constraint != constrainedTerm.constraint()) {
            constrainedTerm = new ConstrainedTerm(term, constraint, constrainedTerm.termContext().fork());
        }
        return constrainedTerm;
    }

    @Override
    public JavaSymbolicObject transform(KLabelConstant kLabelConstant) {
        return kLabelConstant;
    }

    @Override
    public JavaSymbolicObject transform(Hole hole) {
        return hole;
    }

    @Override
    public JavaSymbolicObject transform(KLabelInjection kLabelInjection) {
        Term term = (Term) kLabelInjection.term().accept(this);
        if (term != kLabelInjection.term()) {
            kLabelInjection = new KLabelInjection(term);
        }
        return kLabelInjection;
    }

    @Override
    public JavaSymbolicObject transform(InjectedKLabel injectedKLabel) {
        Term term = (Term) injectedKLabel.injectedKLabel().accept(this);
        if (term != injectedKLabel.injectedKLabel()) {
            injectedKLabel = new InjectedKLabel(term);
        }
        return injectedKLabel;
    }

    @Override
    public JavaSymbolicObject transform(RuleAutomatonDisjunction ruleAutomatonDisjunction) {
        List<Pair<Term, BitSet>> children = ruleAutomatonDisjunction.disjunctions().stream()
                .map(p -> Pair.of((Term) p.getLeft().accept(this), p.getRight()))
                .collect(Collectors.toList());
        if (children.equals(ruleAutomatonDisjunction.disjunctions())) {
            return ruleAutomatonDisjunction;
        } else {
            return new RuleAutomatonDisjunction(
                    children,
                    resolveGlobalContext(ruleAutomatonDisjunction));
        }
    }

    @Override
    public JavaSymbolicObject transform(InnerRHSRewrite innerRHSRewrite) {
        Term[] theNewRHS = new Term[innerRHSRewrite.theRHS.length];
        for (int i = 0; i < theNewRHS.length; i++) {
            if (innerRHSRewrite.theRHS[i] != null)
                theNewRHS[i] = (Term) innerRHSRewrite.theRHS[i].accept(this);
        }
        if (Arrays.equals(theNewRHS, innerRHSRewrite.theRHS)) {
            return innerRHSRewrite;
        } else {
            return new InnerRHSRewrite(theNewRHS);
        }
    }

    @Override
    public JavaSymbolicObject transform(KItemProjection kItemProjection) {
        Term term = (Term) kItemProjection.term().accept(this);
        if (term != kItemProjection.term()) {
            kItemProjection = new KItemProjection(kItemProjection.kind(), term);
        }
        return kItemProjection;
    }

    @Override
    public JavaSymbolicObject transform(KItem kItem) {
        Term kLabel = (Term) kItem.kLabel().accept(this);
        Term kList = (Term) kItem.kList().accept(this);
        if (kLabel.toString().equals(KSEQUENCE_KLABEL) && kList instanceof KList) {
            KList castList = (KList) kList;
            kList = normalizeKSeqList(castList);
        }
        if (kLabel != kItem.kLabel() || kList != kItem.kList()) {
            kItem = KItem.of(kLabel, kList, resolveGlobalContext(kItem), kItem.att());
        }

        return kItem;
    }

    private Term normalizeKSeqList(KList kList) {
        if (kList.size() > 1 && (kList.get(0) instanceof KItem) && KLabels.KSEQ.equals(((KItem) (kList.get(0))).klabel())) {
            KItem kSeq = (KItem) (kList.get(0));
            if (kSeq.kList() instanceof KList) {
                KList kSeqList = (KList) kSeq.klist();
                Term rightNormalizedChild = addRightAssoc(kSeqList.get(1), kList.get(1));
                return KList.concatenate(kSeqList.get(0), rightNormalizedChild);
            }
        }
        return kList;
    }

    private Term addRightAssoc(Term term, Term toBeAdded) {
        if (term instanceof KItem && KLabels.KSEQ.equals(((KItem) term).klabel())) {
            KItem kItem = (KItem) term;
            if (kItem.klist() instanceof KList) {
                KList kList = (KList) kItem.kList();
                Term rightTerm = addRightAssoc(kList.get(1), toBeAdded);
                return KItem.of((Term) kItem.klabel(), KList.concatenate(kList.get(0), rightTerm), kItem.globalContext(),
                        kItem.att());
            }
            return kItem;
        }
        //construct new KSequence Term
        GlobalContext globalContext = term instanceof HasGlobalContext ?
                resolveGlobalContext((HasGlobalContext) term) : context.global();
        return KItem.of(KLabelConstant.of(KLabels.KSEQ, context.definition()), KList.concatenate(term, toBeAdded),
                globalContext, term.att());
    }

    @Override
    public JavaSymbolicObject transform(Token token) {
        return token;
    }

    @Override
    public JavaSymbolicObject transform(UninterpretedToken uninterpretedToken) {
        return transform((Token) uninterpretedToken);
    }

    @Override
    public JavaSymbolicObject transform(BitVector bitVector) {
        return transform((Token) bitVector);
    }

    @Override
    public JavaSymbolicObject transform(BoolToken boolToken) {
        return transform((Token) boolToken);
    }

    @Override
    public JavaSymbolicObject transform(IntToken intToken) {
        return transform((Token) intToken);
    }

    @Override
    public JavaSymbolicObject transform(FloatToken floatToken) {
        return transform((Token) floatToken);
    }

    @Override
    public JavaSymbolicObject transform(StringToken stringToken) {
        return transform((Token) stringToken);
    }

    @Override
    public JavaSymbolicObject transform(KCollection kCollection) {
        throw new UnsupportedOperationException();
    }

    @Override
    public JavaSymbolicObject transform(KLabel kLabel) {
        return kLabel;
    }

    @Override
    public JavaSymbolicObject transform(KList kList) {
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
    public JavaSymbolicObject transform(KSequence kSequence) {
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
    public JavaSymbolicObject transform(BuiltinList builtinList) {
        boolean changed = false;
        BuiltinList.Builder builder = BuiltinList.builder(
                builtinList.sort,
                builtinList.operatorKLabel,
                builtinList.unitKLabel,
                resolveGlobalContext(builtinList));
        for (Term term : builtinList.children) {
            Term transformedTerm = (Term) term.accept(this);
            changed = changed || (transformedTerm != term);
            builder.add(transformedTerm);
        }
        return changed ? builder.build() : builtinList;
    }

    @Override
    public JavaSymbolicObject transform(BuiltinMap builtinMap) {
        boolean changed = false;
        BuiltinMap.Builder builder = BuiltinMap.builder(resolveGlobalContext(builtinMap));

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
    public JavaSymbolicObject transform(BuiltinSet builtinSet) {
        boolean changed = false;
        BuiltinSet.Builder builder = BuiltinSet.builder(resolveGlobalContext(builtinSet));
        for (Term element : builtinSet.elements()) {
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
    public JavaSymbolicObject transform(MetaVariable metaVariable) {
        return transform((Token) metaVariable);
    }

    @Override
    public JavaSymbolicObject transform(Rule rule) {
        Term processedLeftHandSide = (Term) rule.leftHandSide().accept(this);
        Term processedRightHandSide = (Term) rule.rightHandSide().accept(this);
        List<Term> processedRequires = new ArrayList<>(rule.requires().size());
        for (Term conditionItem : rule.requires()) {
            processedRequires.add((Term) conditionItem.accept(this));
        }
        List<Term> processedEnsures = new ArrayList<>(rule.ensures().size());
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
                    rule.att()
            );
        } else {
            return rule;
        }
    }

    @Override
    public JavaSymbolicObject transform(ConjunctiveFormula conjunctiveFormula) {
        Substitution<Variable, Term> transformedSubstitution = ImmutableMapSubstitution.empty();
        List<Pair<Term, Term>> transformedEntries = new ArrayList<>();
        for (Map.Entry<Variable, Term> entry : conjunctiveFormula.substitution().entrySet()) {
            Term key = (Term) entry.getKey().accept(this);
            Term value = (Term) entry.getValue().accept(this);
            if (key instanceof Variable) {
                Substitution<Variable, Term> tmp = transformedSubstitution.plus((Variable) key, value);
                if (tmp != null) {
                    transformedSubstitution = tmp;
                } else {
                    transformedEntries.add(Pair.of(key, value));
                }
            } else {
                transformedEntries.add(Pair.of(key, value));
            }
        }

        ConjunctiveFormula transformedConjunctiveFormula = ConjunctiveFormula.of(
                transformedSubstitution,
                resolveGlobalContext(conjunctiveFormula));

        for (Pair<Term, Term> pair : transformedEntries) {
            transformedConjunctiveFormula = transformedConjunctiveFormula.add(
                    pair.getLeft(),
                    pair.getRight());
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

        if (conjunctiveFormula.globalContext().stage == Stage.REWRITING) {
            // TODO(YilongL): I don't think this piece of code belongs here
            // because a SubstitutionTransformer may only want to do substitution
            transformedConjunctiveFormula = context == null ?
                    transformedConjunctiveFormula.simplify() :
                    transformedConjunctiveFormula.simplify(context);
        }
        return !transformedConjunctiveFormula.equals(conjunctiveFormula) ?
                transformedConjunctiveFormula :
                conjunctiveFormula;
    }

    @Override
    public JavaSymbolicObject transform(DisjunctiveFormula disjunctiveFormula) {
        DisjunctiveFormula transformedDisjunctiveFormula = new DisjunctiveFormula(
                disjunctiveFormula.conjunctions().stream()
                        .map(c -> (ConjunctiveFormula) c.accept(this))
                        .collect(Collectors.toList()), resolveGlobalContext(disjunctiveFormula));
        return !transformedDisjunctiveFormula.equals(disjunctiveFormula) ?
                transformedDisjunctiveFormula :
                disjunctiveFormula;
    }

    @Override
    public JavaSymbolicObject transform(Term node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public JavaSymbolicObject transform(Variable variable) {
        return variable;
    }

}
