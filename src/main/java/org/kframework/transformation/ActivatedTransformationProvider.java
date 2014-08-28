package org.kframework.transformation;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.kframework.utils.errorsystem.KExceptionManager;

import com.beust.jcommander.JCommander;
import com.google.inject.Inject;
import com.google.inject.Provider;
import com.google.inject.TypeLiteral;

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
