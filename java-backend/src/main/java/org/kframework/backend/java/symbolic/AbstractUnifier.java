// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.InjectedKLabel;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.Profiler;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.tuple.Pair;
import com.google.common.collect.Multimap;


/**
 * @author AndreiS
 */
public abstract class AbstractUnifier implements Unifier {
    /**
     * Left-hand side of a minimal equality causing this unification to fail.
     * Must be set if this unification fails.
     */
    private Term unificationFailureLeftHandSide;
    /**
     * Right-hand side of a minimal equality causing this unification to fail.
     * Must be set if this unification fails.
     */
    private Term unificationFailureRightHandSide;

    public Term unificationFailureLeftHandSide() {
        return unificationFailureLeftHandSide;
    }

    public Term unificationFailureRightHandSide() {
        return unificationFailureRightHandSide;
    }

    /**
     * Fails the unification task.
     */
    protected void fail(Term term, Term otherTerm) {
        unificationFailureLeftHandSide = term;
        unificationFailureRightHandSide = otherTerm;
        failed = true;
        if (RuleAuditing.isAuditBegun()) {
            System.err.println("matching/unification failure: " + term + " and " + otherTerm);
        }
    }

    private final Deque<Pair<Term, Term>> tasks = new ArrayDeque<>();
    private final Deque<Pair<Term, Term>> taskBuffer = new ArrayDeque<>();

    protected boolean failed = false;

    //private boolean matchOnFunctionSymbol;
    //
    protected TermContext termContext;

    void addUnificationTask(Term term, Term otherTerm) {
        taskBuffer.push(Pair.of(term, otherTerm));
    }

    /**
     * Performs generic operations for the unification of two terms.
     * Term-specific operations are then delegated to the specific {@code unify}
     * method by overloading. That is to say, in general, the safe way to unify
     * any two terms is to invoke this generic {@code unify} method; do not
     * invoke the specialized ones directly unless you know exactly what you are
     * doing.
     */
    protected boolean unify() {
        tasks.clear();
        failed = false;
        flushTaskBuffer();
        while (!failed && !tasks.isEmpty()) {
            Pair<Term, Term> task = tasks.pop();
            Term term = task.getLeft();
            Term otherTerm = task.getRight();

            if (term.kind().isComputational()) {
                assert otherTerm.kind().isComputational() : otherTerm;

                term = KCollection.upKind(term, otherTerm.kind());
                otherTerm = KCollection.upKind(otherTerm, term.kind());
            }

            assert term.kind() == otherTerm.kind();

            if (term.hashCode() == otherTerm.hashCode() && term.equals(otherTerm)) {
                continue;
            } else if (term.isGround() && otherTerm.isGround()
                    && term.isNormal() && otherTerm.isNormal()) {
                fail(term, otherTerm);
                break;
            }

            if (stop(term, otherTerm)) {
                flushTaskBuffer();
                continue;
            }

            /* unify */
            if (term instanceof CellCollection && otherTerm instanceof CellCollection) {
                if (Profiler.isRunning(Profiler.PATTERN_MATCH_TIMER)) {
                    Profiler.stopTimer(Profiler.PATTERN_MATCH_TIMER);
                    unify((CellCollection) term, (CellCollection) otherTerm);
                    Profiler.startTimer(Profiler.PATTERN_MATCH_TIMER);
                } else {
                    unify((CellCollection) term, (CellCollection) otherTerm);
                }
            } else if (term instanceof KItem && otherTerm instanceof KItem) {
                unify((KItem) term, (KItem) otherTerm);
            } else if (term instanceof KLabelConstant && otherTerm instanceof KLabelConstant) {
                unify((KLabelConstant) term, (KLabelConstant) otherTerm);
            } else if (term instanceof KList && otherTerm instanceof KList) {
                unify((KList) term, (KList) otherTerm);
            } else if (term instanceof KSequence && otherTerm instanceof KSequence) {
                unify((KSequence) term, (KSequence) otherTerm);
            } else if (term instanceof Token && otherTerm instanceof Token) {
                unify((Token) term, (Token) otherTerm);
            } else if (term instanceof InjectedKLabel && otherTerm instanceof InjectedKLabel) {
                unify((InjectedKLabel) term, (InjectedKLabel) otherTerm);
            } else if (term instanceof KLabelInjection && otherTerm instanceof KLabelInjection) {
                unify((KLabelInjection) term, (KLabelInjection) otherTerm);
            } else if (term instanceof Hole && otherTerm instanceof Hole) {
                unify((Hole) term, (Hole) otherTerm);
            } else if (term instanceof Bottom && otherTerm instanceof Bottom) {
                unify((Bottom) term, (Bottom) otherTerm);
            } else if (term instanceof BuiltinList && otherTerm instanceof BuiltinList) {
                unify((BuiltinList) term, (BuiltinList) otherTerm);
            } else if (term instanceof BuiltinMap && otherTerm instanceof BuiltinMap) {
                unify((BuiltinMap) term, (BuiltinMap) otherTerm);
            } else if (term instanceof BuiltinSet && otherTerm instanceof BuiltinSet) {
                unify((BuiltinSet) term, (BuiltinSet) otherTerm);
            } else {
                fail(term, otherTerm);
                break;
                //if (!term.getClass().equals(otherTerm.getClass())) {
                //    throw KEMException.internalError(
                //            "mismatched types: " + term.getClass().getSimpleName()
                //            + " and " + otherTerm.getClass().getSimpleName());
                //} else {
                //    throw KEMException.internalError(
                //            "unexpected type: " + term.getClass().getSimpleName());
                //}
            }

            flushTaskBuffer();
        }
        return !failed;
    }

    private void flushTaskBuffer() {
        while (!taskBuffer.isEmpty()) {
            tasks.push(taskBuffer.pop());
        }
    }

    abstract boolean stop(Term term, Term otherTerm);

    @Override
    public void unify(Bottom bottom, Bottom term) {
        fail(bottom, term);
    }

    @Override
    public void unify(Hole hole, Hole term) {
        if (!hole.equals(term)) {
            fail(hole, term);
        }
    }

    @Override
    public void unify(InjectedKLabel injectedKLabel, InjectedKLabel otherInjectedKLabel) {
        addUnificationTask(injectedKLabel.injectedKLabel(), otherInjectedKLabel.injectedKLabel());
    }

    @Override
    public void unify(KItem kItem, KItem patternKItem) {
        Term kLabel = kItem.kLabel();
        Term kList = kItem.kList();
        addUnificationTask(kLabel, patternKItem.kLabel());
        // TODO(AndreiS): deal with KLabel variables
        if (kLabel instanceof KLabelConstant) {
            KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
            if (kLabelConstant.isMetaBinder()) {
                // TODO(AndreiS): deal with non-concrete KLists
                assert kList instanceof KList;
                Multimap<Integer, Integer> binderMap = kLabelConstant.getMetaBinderMap();
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
        addUnificationTask(kList, patternKItem.kList());
    }

    @Override
    public void unify(KLabelConstant kLabelConstant, KLabelConstant term) {
        if (!kLabelConstant.equals(term)) {
            fail(kLabelConstant, term);
        }
    }

    @Override
    public void unify(KLabelInjection kLabelInjection, KLabelInjection otherKLabelInjection) {
        addUnificationTask(kLabelInjection.term(), otherKLabelInjection.term());
    }

    @Override
    public void unify(KList kList, KList otherKList) {
        unify((KCollection) kList, (KCollection) otherKList);
    }

    @Override
    public void unify(KSequence kSequence, KSequence otherKSequence) {
        unify((KCollection) kSequence, (KCollection) otherKSequence);
    }

    @Override
    public void unify(Token token, Token term) {
        if (!token.equals(term)) {
            fail(token, term);
        }
    }

    public abstract void unify(KCollection kCollection, KCollection otherKCollection);

}