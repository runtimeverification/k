// Copyright (c) 2014-2015 K Team. All Rights Reserved.
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
 *
 * The goal of this class and its annotations is to eventually annotate all kompilation transformers
 * with the properties that they affect, and then demonstrate that those annotations are complete
 * by means of mutation testing which reorders the transformers and verifies that the output remains
 * the same. We do this so that we have a complete picture of the interdependencies of the
 * compilation stages, which is the first step towards eventually breaking down those dependencies
 * as much as possible.
 */
public enum KilProperty {
    /**
     * True if all syntax declarations have been converted to KLabel declarations
     */
    NO_CONCRETE_SYNTAX_DECLARATIONS,
    /**
     * True if no term uses concrete syntax.
     */
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
