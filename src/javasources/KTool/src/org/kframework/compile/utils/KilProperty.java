package org.kframework.compile.utils;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Represents a contract asserting that a particular AST has a particular
 * property (e.g. does not contain any concrete syntax, does not contain any contexts, etc).
 */
public enum KilProperty {
    NO_CONCRETE_SYNTAX;
    //TODO: add more

    /**
     * Used to annotate code which takes an AST as input which will not work on
     * terms without a particular KilProperty.
     */
    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.TYPE)
    public static @interface DependsOn {
        KilProperty value();
    }

    /**
     * Used to annotate code which outputs an AST which is guaranteed to ensure
     * a particular KilProperty.
     */
    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.TYPE)
    public static @interface Provides {
        KilProperty value();
    }
}
