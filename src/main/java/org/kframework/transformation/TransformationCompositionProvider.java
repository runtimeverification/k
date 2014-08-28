package org.kframework.transformation;

import java.util.Map;
import java.util.Set;

import org.kframework.kil.Attributes;
import org.kframework.krun.api.KRunResult;
import org.kframework.krun.tools.Executor;

import com.google.common.collect.Sets;
import com.google.inject.Inject;
import com.google.inject.Provider;
import com.google.inject.TypeLiteral;

public class TransformationCompositionProvider<P, Q, R> implements TransformationProvider<Transformation<P, R>> {

    private final TransformationProvider<Transformation<P, Q>> firstStep;
    private final TransformationProvider<Transformation<Q, R>> secondStep;
    private final ActivatedTransformationProvider<P, R> onlyStep;
    private final Executor.Tool executionStep;
    private final Map<ToolActivation, Provider<Transformation<P, R>>> possibleOnlySteps;
    private final Map<ToolActivation, Provider<Transformation<P, Q>>> possibleFirstSteps;
    private final Map<ToolActivation, Provider<Transformation<Q, R>>> possibleSecondSteps;

    private final TypeLiteral<P> ptype;
    private final TypeLiteral<Q> qtype;
    private final TypeLiteral<R> rtype;

    static class Holder<P, Q, R> {
        @Inject(optional=true) TransformationProvider<Transformation<P, Q>> firstStep;
        @Inject(optional=true) TransformationProvider<Transformation<Q, R>> secondStep;
        @Inject(optional=true) ActivatedTransformationProvider<P, R> onlyStep;
        @Inject(optional=true) Map<ToolActivation, Provider<Transformation<P, R>>> possibleOnlySteps;
        @Inject(optional=true) Map<ToolActivation, Provider<Transformation<P, Q>>> possibleFirstSteps;
        @Inject(optional=true) Map<ToolActivation, Provider<Transformation<Q, R>>> possibleSecondSteps;
    }

    @Inject
    public TransformationCompositionProvider(
            Holder<P, Q, R> holder,
            Executor.Tool executionStep,
            TypeLiteral<P> ptype,
            TypeLiteral<Q> qtype,
            TypeLiteral<R> rtype) {
        this.firstStep = holder.firstStep;
        this.secondStep = holder.secondStep;
        this.onlyStep = holder.onlyStep;
        this.possibleOnlySteps = holder.possibleOnlySteps;
        this.possibleFirstSteps = holder.possibleFirstSteps;
        this.possibleSecondSteps = holder.possibleSecondSteps;
        this.executionStep = executionStep;
        this.ptype = ptype;
        this.qtype = qtype;
        this.rtype = rtype;
    }

    private <I, O> Transformation<I, O> processSubTransformation(TransformationProvider<Transformation<I, O>> provider) throws AmbiguousTransformationException {
        Transformation<I, O> result;
        if (provider != null) {
            try {
                result = provider.get();
            } catch (TransformationNotSatisfiedException e) {
                result = null;
            }
        } else {
            result = null;
        }
        return result;
    }

    @Override
    public Transformation<P, R> get() throws AmbiguousTransformationException, TransformationNotSatisfiedException {
        final Transformation<P, R> onlyStep = processSubTransformation(this.onlyStep);
        Transformation<P, Q> originalFirstStep = processSubTransformation(this.firstStep);
        final Transformation<P, Q> firstStep;
        if (onlyStep == null && originalFirstStep == null && ptype.equals(TypeLiteral.get(Void.class)) && qtype.equals(new TypeLiteral<KRunResult<?>>() {})) {
            firstStep = (Transformation<P, Q>) executionStep;
        } else {
            firstStep = originalFirstStep;
        }
        final Transformation<Q, R> secondStep = processSubTransformation(this.secondStep);
        Transformation<P, R> composed = new Transformation<P, R>() {

            @Override
            public R run(P p, Attributes attrs) {
                return secondStep.run(firstStep.run(p, attrs), attrs);
            }

            @Override
            public String getName() {
                return firstStep.getName() + " -> " + secondStep.getName();
            }

        };
        if (onlyStep == null) {
            if (firstStep == null && secondStep != null) {
                throw new TransformationNotSatisfiedException(ptype, qtype, possibleFirstSteps.keySet());
            }
            if (secondStep == null && firstStep != null) {
                throw new TransformationNotSatisfiedException(qtype, rtype, possibleSecondSteps.keySet());
            }
            if (firstStep == null && secondStep == null) {
                Set<ToolActivation> possibleSteps = Sets.newHashSet();
                if (possibleOnlySteps != null) {
                    possibleSteps.addAll(possibleOnlySteps.keySet());
                }
                possibleSteps.addAll(Sets.intersection(possibleFirstSteps.keySet(), possibleSecondSteps.keySet()));
                throw new TransformationNotSatisfiedException(ptype, rtype, possibleSteps);
            }
            return composed;
        } else if (firstStep != null && secondStep != null) {
            throw new AmbiguousTransformationException(onlyStep, composed);
        }
        return onlyStep;
    }
}
