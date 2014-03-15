package org.kframework.compile.utils;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Represents a contract asserting that a particular AST has a particular
 * property (e.g. does not contain any concrete syntax, does not contain any contexts, etc).
 *
 * Since contracts can be either positive or negative in nature, we could hypothetically specify each
 * KilProperty as its inverse as well as itself. By convention, the positive form of the KilProperty
 * represents the state the KilProperty is in following a successful compilation sequence.
 */
public enum KilProperty {
    NO_CONCRETE_SYNTAX,
    /**
     * True if no rule matches on a  data structure (list, set, map) pattern in the left-hand side.
     */
    NO_DATA_STRUCTURE_PATTERN_MATCHING,
    /**
     * True if all data structures (list, set, map) are represented as instances of {@link org.kframework.kil.DataStructureBuiltin}, and not as instances of {@link org.kframework.kil.KApp} or {@link org.kframework.kil.TermCons}.
     */
    COMPILED_DATA_STRUCTURES,
    /**
     * True if all rules have the form "left => right requires ... ensures ...", where "=>" does not occur in the left or right terms.
     */
    TOP_REWRITING;
    //TODO: add more

    /**
     * Used to annotate code which takes an AST as input which will not work on
     * terms <b>without</b> a particular KilProperty.
     */
    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.TYPE)
    public static @interface Requires {
        KilProperty[] value();
    }

    /**
     * Used to annotate code which takes an AST as input which will not work on
     * terms <b>with</b> a particular KilProperty.
     */
    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.TYPE)
    public static @interface Forbids {
        KilProperty[] value();
    }


    /**
     * Used to annotate code which outputs an AST which is guaranteed to ensure
     * a particular KilProperty.
     */
    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.TYPE)
    public static @interface Ensures {
        KilProperty[] value();
    }

    /**
     * Used to annotate code which outputs an AST which is guaranteed to destroy
     * a particular KilProperty.
     */
    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.TYPE)
    public static @interface Destroys {
        KilProperty[] value();
    }

}
