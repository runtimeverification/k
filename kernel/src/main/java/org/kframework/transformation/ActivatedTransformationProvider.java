// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.transformation;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.kframework.utils.errorsystem.KExceptionManager;

import com.beust.jcommander.JCommander;
import com.google.inject.Inject;
import com.google.inject.Provider;
import com.google.inject.TypeLiteral;

/**
 * Implementation of a provider for an atomic transformation.
 *
 * Modules provide transformations by binding them to a particular
 * option or option value. For example, if I use the --ltlmc option,
 * then the transformation for LTL model checking activates. This implementation
 * loads the set of transformations from an object of type P to an object of type R,
 * determines which transformations, if any, of that set have been activated,
 * and responds appropriately. If none are active, it throws a {@link TransformationNotSatisfiedException}.
 * If two or more are active, it throws a {@link AmbiguousTransformationException}.
 * If only one is active, it provides that implementation.
 * @author dwightguth
 *
 * @param <P> The type of the input to be transformed
 * @param <R> The type of the output to be provided
 */
public class ActivatedTransformationProvider<P, R> implements TransformationProvider<Transformation<P, R>> {

    private final JCommander jc;
    private final KExceptionManager kem;
    private final Map<ToolActivation, Provider<Transformation<P, R>>> availableTransformations;

    private final TypeLiteral<P> ptype;
    private final TypeLiteral<R> rtype;

    @Inject
    ActivatedTransformationProvider(
            JCommander jc,
            KExceptionManager kem,
            TypeLiteral<P> ptype,
            TypeLiteral<R> rtype,
            Map<ToolActivation, Provider<Transformation<P, R>>> availableTransformations) {
        this.jc = jc;
        this.kem = kem;
        this.ptype = ptype;
        this.rtype = rtype;
        this.availableTransformations = availableTransformations;
    }

    @Override
    public Transformation<P, R> get() throws TransformationNotSatisfiedException, AmbiguousTransformationException {
        Set<Provider<Transformation<P, R>>> activatedTransformations = new HashSet<>();
        for (Map.Entry<ToolActivation, Provider<Transformation<P, R>>> entry : availableTransformations.entrySet()) {
            if (entry.getKey().isActive(jc)) {
                activatedTransformations.add(entry.getValue());
            }
        }
        Transformation<P, R> result = null;
        for (Provider<Transformation<P, R>> trans : activatedTransformations) {
            if (result != null) {
                throw new AmbiguousTransformationException(result, trans.get());
            }
            result = trans.get();
        }
        if (result == null) {
            throw new TransformationNotSatisfiedException(ptype, rtype, availableTransformations.keySet());
        }
        return result;
    }
}
