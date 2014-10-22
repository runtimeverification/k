// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BuiltinBitVectorOperations;
import org.kframework.backend.java.builtins.BuiltinBoolOperations;
import org.kframework.backend.java.builtins.BuiltinCollectionOperations;
import org.kframework.backend.java.builtins.BuiltinFloatOperations;
import org.kframework.backend.java.builtins.BuiltinIOOperations;
import org.kframework.backend.java.builtins.BuiltinIntOperations;
import org.kframework.backend.java.builtins.BuiltinListOperations;
import org.kframework.backend.java.builtins.BuiltinMapOperations;
import org.kframework.backend.java.builtins.BuiltinSetOperations;
import org.kframework.backend.java.builtins.BuiltinStringOperations;
import org.kframework.backend.java.builtins.BuiltinSubstitutionOperations;
import org.kframework.backend.java.builtins.BuiltinVisitorOperations;
import org.kframework.backend.java.builtins.FreshOperations;
import org.kframework.backend.java.builtins.MetaK;
import org.kframework.backend.java.builtins.SortMembership;
import org.kframework.backend.java.builtins.TermEquality;
import org.kframework.utils.inject.Builtins;

import com.google.common.collect.ImmutableSet;
import com.google.inject.AbstractModule;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;

public class JavaSymbolicCommonModule extends AbstractModule {

    /**
     * Add new classes containing hooks here.
     */
    @SuppressWarnings("unchecked")
    public static final ImmutableSet<Class<?>> HOOK_MODULES = ImmutableSet.of(
            TermEquality.class,
            BuiltinBoolOperations.class,
            BuiltinIntOperations.class,
            BuiltinFloatOperations.class,
            BuiltinStringOperations.class,
            BuiltinBitVectorOperations.class,
            MetaK.class,
            BuiltinSubstitutionOperations.class,
            BuiltinCollectionOperations.class,
            BuiltinListOperations.class,
            BuiltinMapOperations.class,
            BuiltinSetOperations.class,
            BuiltinIOOperations.class,
            BuiltinVisitorOperations.class,
            UseSMT.class,
            SortMembership.class,
            FreshOperations.class);
    @Override
    protected void configure() {

        MapBinder<Class<?>, Object> builtinFunctionBinder = MapBinder.newMapBinder(binder(),
                new TypeLiteral<Class<?>>() {}, TypeLiteral.get(Object.class), Builtins.class);
        for (Class<?> cls : HOOK_MODULES) {
            builtinFunctionBinder.addBinding(cls).to(cls);
        }
    }
}
