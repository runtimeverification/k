// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.common.collect.Multimap;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.util.DoubleLinkedList;
import org.kframework.builtin.KLabels;
import org.kframework.kore.Assoc;
import static org.kframework.Collections.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;


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

    private final DoubleLinkedList<Pair<Term, Term>> tasks = new DoubleLinkedList<>();
    private final DoubleLinkedList<Pair<Term, Term>> taskBuffer = new DoubleLinkedList<>();

    protected boolean failed = false;

    //private boolean matchOnFunctionSymbol;
    //
    protected final TermContext termContext;

    private final KLabelConstant kSeqLabel;
    private final KLabelConstant kDotLabel;
    private final KItem kDot;

    protected AbstractUnifier(TermContext termContext) {
        this.termContext = termContext;
        kSeqLabel = KLabelConstant.of(KLabels.KSEQ, termContext.definition());
        kDotLabel = KLabelConstant.of(KLabels.DOTK, termContext.definition());
        kDot = KItem.of(kDotLabel, KList.concatenate(), termContext.global());
    }

    void addUnificationTask(Term term, Term otherTerm) {
        taskBuffer.add(Pair.of(term, otherTerm));
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

                if (term.kind() != otherTerm.kind()) {
                    if (term.kind() == Kind.KITEM) {
                        if (otherTerm instanceof KList && ((KList) otherTerm).concreteSize() == 1) {
                            if (((KList) otherTerm).hasFrame()) {
                                add(KList.EMPTY, ((KList) otherTerm).frame());
                            }
                            otherTerm = ((KList) otherTerm).get(0);
                        }
                        if (otherTerm instanceof KSequence && ((KSequence) otherTerm).concreteSize() == 1) {
                            if (((KSequence) otherTerm).hasFrame()) {
                                add(KSequence.EMPTY, ((KSequence) otherTerm).frame());
                            }
                            otherTerm = ((KSequence) otherTerm).get(0);
                        }
                    } else if (otherTerm.kind() == Kind.KITEM) {
                        if (term instanceof KList && ((KList) term).concreteSize() == 1) {
                            if (((KList) term).hasFrame()) {
                                add(((KList) term).frame(), KList.EMPTY);
                            }
                            term = ((KList) term).get(0);
                        }
                        if (term instanceof KSequence && ((KSequence) term).concreteSize() == 1) {
                            if (((KSequence) term).hasFrame()) {
                                add(((KSequence) term).frame(), KSequence.EMPTY);
                            }
                            term = ((KSequence) term).get(0);
                        }
                    } else if (term.kind() == Kind.K) {
                        if (otherTerm instanceof KList && ((KList) otherTerm).concreteSize() == 1) {
                            if (((KList) otherTerm).hasFrame()) {
                                add(KList.EMPTY, ((KList) otherTerm).frame());
                            }
                            otherTerm = ((KList) otherTerm).get(0);
                        }
                    } else if (otherTerm.kind() == Kind.K) {
                        if (term instanceof KList && ((KList) term).concreteSize() == 1) {
                            if (((KList) term).hasFrame()) {
                                add(((KList) term).frame(), KList.EMPTY);
                            }
                            term = ((KList) term).get(0);
                        }
                    }
                }

                if (isKSeq(term) || isKSeq(otherTerm)) {
                    term = getCanonicalKSeq(term);
                    otherTerm = getCanonicalKSeq(otherTerm);

                    if (isKSeq(term)) {
                        otherTerm = upKSeq(otherTerm);
                    }
                    if (isKSeq(otherTerm)) {
                        term = upKSeq(term);
                    }
                }

                if (term.kind() != otherTerm.kind()) {
                    term = KCollection.upKind(term, otherTerm.kind());
                    otherTerm = KCollection.upKind(otherTerm, term.kind());
                }
            }

            assert term.kind() == otherTerm.kind();

            // the code below is commented out due to hashCode not being updated for mutable cells
            //if (term.hashCode() == otherTerm.hashCode() && term.equals(otherTerm)) {
            //    continue;
            //} else if (term.isGround() && otherTerm.isGround()
            //        && term.isNormal() && otherTerm.isNormal()) {
            //    fail(term, otherTerm);
            //    break;
            //}

            if (stop(term, otherTerm)) {
                flushTaskBuffer();
                continue;
            }

            /* unify */
            if (term instanceof CellCollection && otherTerm instanceof CellCollection) {
                unify((CellCollection) term, (CellCollection) otherTerm);
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

    public static boolean isKSeq(Term term) {
        return term instanceof KItem && ((KItem) term).kLabel().toString().equals(KLabels.KSEQ);
    }

    public static boolean isKSeqVar(Term term) {
        return term instanceof Variable && term.sort().equals(Sort.KSEQUENCE);
    }

    private Term upKSeq(Term otherTerm) {
        if (!isKSeq(otherTerm) && !isKSeqVar(otherTerm))
            otherTerm = KItem.of(kSeqLabel, KList.concatenate(otherTerm, kDot), termContext.global());
        return otherTerm;
    }

    private Term getCanonicalKSeq(Term term) {
        return stream(Assoc.flatten(kSeqLabel, Seq(term), kDotLabel).reverse())
                .map(Term.class::cast)
                .reduce((a, b) -> KItem.of(kSeqLabel, KList.concatenate(b, a), termContext.global()))
                .orElse(kDot);
    }

    private void flushTaskBuffer() {
        tasks.pushAll(taskBuffer);
    }

    abstract void add(Term left, Term right);

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
                    Map<Variable,Variable> freshSubstitution = Variable.rename(variables);
                    Term freshBoundVars = boundVars.substituteWithBinders(freshSubstitution);
                    terms.set(boundVarPosition, freshBoundVars);
                    for (Integer bindingExpPosition : binderMap.get(boundVarPosition)) {
                        Term bindingExp = terms.get(bindingExpPosition-1);
                        Term freshbindingExp = bindingExp.substituteWithBinders(freshSubstitution);
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