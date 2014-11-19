// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.AssociativeCommutativeCollection;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.CellLabel;
import org.kframework.backend.java.kil.ConcreteCollectionVariable;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.RewriteEngineUtils;
import org.kframework.kil.loader.Context;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.beust.jcommander.internal.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;

import org.apache.commons.lang3.tuple.Pair;


/**
 * @author YilongL
 */
public class NonACPatternMatcher {

    /**
     * Represents the substitution after the pattern matching.
     */
    private Map<Variable, Term> substitution;

    private final Deque<Pair<Term, Term>> tasks = new ArrayDeque<>();

    private final List<Pair<Term, Term>> taskBuffer = Lists.newArrayList();

    private Pair<Term, Term> crntTask;

    private boolean failed = false;

    private final boolean matchOnFunctionSymbol;

    private final TermContext termContext;

    public NonACPatternMatcher(TermContext context) {
        this(false, context);
    }

    public NonACPatternMatcher(boolean matchOnFunctionSymbol, TermContext context) {
        this.matchOnFunctionSymbol = matchOnFunctionSymbol;
        this.termContext = context;
    }

    /**
     * Matches the subject term against the pattern.
     *
     * @param subject
     *            the subject term
     * @param pattern
     *            the pattern term
     * @return the substitution if the matching succeeds; otherwise, {@code null}
     */
    public Map<Variable, Term> patternMatch(Term subject, Term pattern) {
        /*
         * We make no assumption about whether the subject will be ground in the
         * matching algorithm. As for the pattern, all symbolic terms inside it
         * must be variables (no function KLabels, KItem projections, or
         * data-structure lookup/update).
         */

        substitution = Maps.newHashMapWithExpectedSize(32);
        tasks.clear();
        taskBuffer.clear();
        tasks.addFirst(Pair.of(subject, pattern));
        failed = false;
        if (match()) {
            // TODO(AndreiS): this ad-hoc evaluation is converting from the KLabel/KList format
            // (used during associative matching) back to builtin representation
            if (termContext.definition().context().krunOptions != null
                    && termContext.definition().context().krunOptions.experimental.prove != null) {
                PatternMatcher.evaluateSubstitution(substitution, termContext);
            }
            return substitution;
        } else {
            return null;
        }
    }

    private void check(boolean condition) {
        failed = failed || !condition;
    }

    private boolean match() {
        while (!failed) {
            for (int i = taskBuffer.size() - 1; i >= 0; i--) {
                tasks.addFirst(taskBuffer.get(i));
            }
            taskBuffer.clear();
            if (tasks.isEmpty()) {
                return true;
            }

            crntTask = tasks.pop();
            Term subject = crntTask.getLeft();
            Term pattern = crntTask.getRight();

            if (pattern instanceof Variable) {
                Variable variable = (Variable) pattern;

                /* special case for concrete collections  */
                check(!(variable instanceof ConcreteCollectionVariable)
                        || ((ConcreteCollectionVariable) variable).match(subject));
                if (failed) {
                    return false;
                }

                /* add substitution */
                addSubstitution(variable, subject);
            } else {
                check(!subject.isSymbolic() || subject instanceof KItem && matchOnFunctionSymbol);
                if (failed) {
                    return false;
                }

                if (subject instanceof Cell) {
                    if (pattern instanceof Cell) {
                        match((Cell) subject, (Cell) pattern);
                    } else if (pattern instanceof CellCollection) {
                        match((Cell) subject, (CellCollection) pattern);
                    } else {
                        return false;
                    }
                } else if (subject instanceof CellCollection) {
                    if (pattern instanceof CellCollection) {
                        match((CellCollection) subject, (CellCollection) pattern);
                    } else {
                        return false;
                    }
                } else if (subject instanceof KLabelConstant) {
                    check(subject.equals(pattern));
                } else if (subject instanceof KItem) {
                    if (pattern instanceof KItem) {
                        match((KItem) subject, (KItem) pattern);
                    } else if (pattern instanceof KSequence) {
                        match((KItem) subject, (KSequence) pattern);
                    } else if (pattern instanceof KList) {
                        match((KItem) subject, (KList) pattern);
                    } else {
                        return false;
                    }
                } else if (subject instanceof KSequence) {
                    if (pattern instanceof KSequence) {
                        match((KSequence) subject, (KSequence) pattern);
                    } else if (pattern instanceof KList) {
                        match((KSequence) subject, (KList) pattern);
                    } else {
                        return false;
                    }
                } else if (subject instanceof KList) {
                    if (pattern instanceof KList) {
                        match((KList) subject, (KList) pattern);
                    } else {
                        return false;
                    }
                } else if (subject instanceof Token) {
                    if (subject.kind() == Kind.KITEM) {
                        if (pattern instanceof KSequence) {
                            match((Token) subject, (KSequence) pattern);
                        } else if (pattern instanceof KList) {
                            match((Token) subject, (KList) pattern);
                        } else {
                            check(subject.equals(pattern));
                        }
                    } else {
                        check(subject.equals(pattern));
                    }
                } else if (subject instanceof KLabelInjection) {
                    if (pattern instanceof KLabelInjection) {
                        match((KLabelInjection) subject, (KLabelInjection) pattern);
                    } else {
                        return false;
                    }
                } else if (subject instanceof Hole) {
                    check(subject.equals(pattern));
                } else if (subject instanceof BuiltinList && matchOnFunctionSymbol) {
                    if (pattern instanceof BuiltinList) {
                        match((BuiltinList) subject, (BuiltinList) pattern);
                    } else {
                        return false;
                    }
                } else if (subject instanceof AssociativeCommutativeCollection || subject instanceof BuiltinList) {
                    return false;
                } else {
                    throw KExceptionManager.internalError("unexpected subject type: found " + subject.getClass().getSimpleName());
                }
            }
        }

        return false;
    }

    private void addMatchingTask(Term subject, Term pattern) {
        taskBuffer.add(Pair.of(subject, pattern));
    }

    /**
     * Binds a variable in the pattern to a subterm of the subject; calls
     * {@link NonACPatternMatcher#fail()} when the binding fails.
     *
     * @param variable
     *            the variable
     * @param term
     *            the term
     */
    private void addSubstitution(Variable variable, Term term) {
        /* KList is the only possible singleton collection because we enforce
         * the second argument of KItem#of to have kind KList */
        if (term.kind() == Kind.KLIST) {
            term = KCollection.downKind(term);
        }

        check(termContext.definition().subsorts().isSubsortedEq(variable.sort(), term.sort()));
        if (failed) {
            return;
        }

        Term subst = substitution.get(variable);
        if (subst == null) {
            substitution.put(variable, term);
        } else {
            check(subst.equals(term));
        }
    }

    private void match(Cell cell, Cell otherCell) {
        check(cell.getLabel().equals(otherCell.getLabel()));
        if (!failed) {
            addMatchingTask(cell.getContent(), otherCell.getContent());
        }
    }

    private void match(Cell cell, CellCollection pattern) {
        check(pattern.concreteSize() == 1);
        if (!failed) {
            /* YilongL: there is no need to assert AC-matching here, because
             * even if both cells are multiplicity cells, there is still only
             * one possible way to match */

            addMatchingTask(cell, pattern.cells().iterator().next());
            if (pattern.hasFrame()) {
                addSubstitution(pattern.frame(), CellCollection.EMPTY);
            }
        }
    }

    private void match(CellCollection cellCollection, CellCollection otherCellCollection) {
        Context context = termContext.definition().context();

        Set<CellLabel> unifiableCellLabels = Sets.intersection(cellCollection.labelSet(), otherCellCollection.labelSet());
        check(otherCellCollection.labelSet().size() == unifiableCellLabels.size());
        if (failed) {
            return;
        }

        int numOfDiffCellLabels = cellCollection.labelSet().size() - unifiableCellLabels.size();

        Variable frame = cellCollection.hasFrame() ? cellCollection.frame() : null;
        Variable otherFrame = otherCellCollection.hasFrame()? otherCellCollection.frame() : null;

        if (frame != null) {
            check(otherFrame != null);
            if (failed) {
                return;
            }

            addSubstitution(otherFrame, cellCollection.removeAll(unifiableCellLabels, context));
        } else {
            if (otherFrame != null) {
                addSubstitution(otherFrame, cellCollection.removeAll(unifiableCellLabels, context));
            } else {
                check(numOfDiffCellLabels == 0);
                if (failed) {
                    return;
                }
            }
        }

        for (CellLabel label : unifiableCellLabels) {
            assert cellCollection.get(label).size() == 1 && otherCellCollection.get(label).size() == 1 :
                "AC-matching not supported; consider using the AC pattern matcher instead";

            /* YilongL: it's okay for two multiplicity cells to pass the above
             * AC-matching check because there is really only one possible way
             * for the matching to succeed */
            match(cellCollection.get(label).iterator().next(),
                    otherCellCollection.get(label).iterator().next());
        }

    }

    private void match(KItem kItem, KItem pattern) {
        Term kLabel = kItem.kLabel();
        Term kList = kItem.kList();
        addMatchingTask(kLabel, pattern.kLabel());
        // TODO(AndreiS): deal with KLabel variables
        if (kLabel instanceof KLabelConstant) {
            KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
            if (kLabelConstant.isMetaBinder()) {
                // TODO(AndreiS): deal with non-concrete KLists
                assert kList instanceof KList;
                Multimap<Integer, Integer> binderMap = kLabelConstant.getBinderMap();
                List<Term> terms = new ArrayList<>(((KList) kList).getContents());
                for (Integer boundVarPosition : binderMap.keySet()) {
                    Term boundVars = terms.get(boundVarPosition);
                    Set<Variable> variables = boundVars.variableSet();
                    Map<Variable,Variable> freshSubstitution = Variable.getFreshSubstitution(variables);
                    Term freshBoundVars = boundVars.substituteWithBinders(freshSubstitution, termContext);
                    terms.set(boundVarPosition, freshBoundVars);
                    for (Integer bindingExpPosition : binderMap.get(boundVarPosition)) {
                        Term bindingExp = terms.get(bindingExpPosition-1);
                        Term freshbindingExp = bindingExp.substituteWithBinders(freshSubstitution, termContext);
                        terms.set(bindingExpPosition-1, freshbindingExp);
                    }
                }
                kList = KList.concatenate(terms);
            }
        }
        addMatchingTask(kList, pattern.kList());
    }

    private void match(KItem kItem, KSequence pattern) {
        check(pattern.concreteSize() == 1);
        if (!failed) {
            addMatchingTask(kItem, pattern.get(0));
            if (pattern.hasFrame()) {
                addSubstitution(pattern.frame(), KSequence.EMPTY);
            }
        }
    }

    private void match(KItem kItem, KList pattern) {
        check(pattern.concreteSize() == 1);
        if (!failed) {
            addMatchingTask(kItem, pattern.get(0));
            if (pattern.hasFrame()) {
                addSubstitution(pattern.frame(), KList.EMPTY);
            }
        }
    }

    private void match(KSequence kSequence, KList pattern) {
        check(pattern.concreteSize() == 1);
        if (!failed) {
            addMatchingTask(kSequence, pattern.get(0));
            if (pattern.hasFrame()) {
                addSubstitution(pattern.frame(), KList.EMPTY);
            }
        }
    }

    private void match(KSequence kSequence, KSequence pattern) {
        matchKCollection(kSequence, pattern);
    }

    private void match(KList kList, KList pattern) {
        matchKCollection(kList, pattern);
    }

    private void matchKCollection(KCollection kCollection, KCollection pattern) {
        assert kCollection.getClass().equals(pattern.getClass());

        int len = kCollection.concreteSize();
        int otherLen = pattern.concreteSize();
        check(len >= otherLen);
        if (failed) {
            return;
        }

        if (len >= otherLen) {
            if (pattern.hasFrame()) {
                addSubstitution(pattern.frame(), kCollection.fragment(otherLen));
            } else {
                check(!kCollection.hasFrame() && len == otherLen);
                if (failed) {
                    return;
                }
            }

            // kCollection.size() == length
            for (int index = 0; index < otherLen; ++index) {
                addMatchingTask(kCollection.get(index), pattern.get(index));
            }
        }
    }

    private void match(Token token, KSequence pattern) {
        check(pattern.concreteSize() == 1);
        if (!failed) {
            addMatchingTask(token, pattern.get(0));
            if (pattern.hasFrame()) {
                addSubstitution(pattern.frame(), KSequence.EMPTY);
            }
        }
    }

    private void match(Token token, KList pattern) {
        check(pattern.concreteSize() == 1);
        if (!failed) {
            addMatchingTask(token, pattern.get(0));
            if (pattern.hasFrame()) {
                addSubstitution(pattern.frame(), KList.EMPTY);
            }
        }
    }

    private void match(KLabelInjection kLabelInjection, KLabelInjection pattern) {
        addMatchingTask(kLabelInjection.term(), pattern.term());
    }

    private void match(BuiltinList builtinList, BuiltinList pattern) {
        addMatchingTask(
                builtinList.toK(termContext),
                pattern.toK(termContext));
    }

    /**
     * Matches a subject term against a rule. Returns the instantiation when the
     * rule can be applied for sure (all side-conditions are cleared). Note
     * that, however, {@code null} doesn't mean that this rule cannot apply
     * definitely; it is possible that side-conditions are blocked by symbolic
     * argument(s).
     *
     * @param subject
     *            the subject term
     * @param rule
     *            the rule
     * @param context
     *            the term context
     * @return the instantiation of variables
     */
    public static Map<Variable, Term> match(Term subject, Rule rule, TermContext context) {
        NonACPatternMatcher matcher = new NonACPatternMatcher(rule.isFunction() || rule.isLemma(), context);

        Map<Variable, Term> result = matcher.patternMatch(subject, rule.leftHandSide());
        return result != null ? RewriteEngineUtils.evaluateConditions(rule, result, context) : null;
    }

}
