// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.kil;

import com.google.common.reflect.TypeToken;
import com.google.inject.name.Named;
import com.google.inject.name.Names;
import org.kframework.kil.loader.Constants;

import java.io.Serializable;
import java.lang.annotation.Annotation;

/**
 * Represents either an explicit attribute on a {@link Rule} or {@link Production},
 * or node metadata like location.
 * The inherited member attributes is used for location information
 * if this represents an explicitly written attribute.
 */
public class Attribute {

    private Attribute() {}

    public static final String FUNCTION_KEY = "function";
    public static final String SIMPLIFICATION_KEY = "simplification";
    public static final String ASSOCIATIVE_KEY = "assoc";
    public static final String COMMUTATIVE_KEY = "comm";
    public static final String IDEMPOTENT_KEY = "idem";
    public static final String PROJECTION_KEY = "proj";
    public static final String UNIT_KEY = "unit";
    public static final String PREDICATE_KEY = "predicate";
    public static final String KORE_KEY = "kore";
    public static final String ANYWHERE_KEY = Constants.ANYWHERE;
    public static final String PATTERN_KEY = "pattern";
    public static final String PATTERN_FOLDING_KEY = "pattern-folding";
    public static final String HOOK_KEY = "hook";
    public static final String MACRO_KEY = "macro";
    public static final String ALIAS_KEY = "alias";
    public static final String MACRO_REC_KEY = "macro-rec";
    public static final String ALIAS_REC_KEY = "alias-rec";
    public static final String LEMMA_KEY = "lemma";
    public static final String TRUSTED_KEY = "trusted";
    public static final String MATCHING_KEY = "matching";

    public static final String BITWIDTH_KEY = "bitwidth";
    public static final String EXPONENT_KEY = "exponent";
    public static final String SIGNIFICAND_KEY = "significand";
    public static final String SMTHOOK_KEY = "smt-hook";
    public static final String SMTLIB_KEY = "smtlib";
    public static final String SMT_LEMMA_KEY = "smt-lemma";
    public static final String SMT_PRELUDE_KEY = "smt-prelude";

    public static final String ONE_PATH_KEY = "one-path";
    public static final String ALL_PATH_KEY = "all-path";
    // Used to direct configuration abstraction,
    // generated when translating configuration declaration to productions.
    public static final String CELL_KEY = "cell";
    public static final String CELL_FRAGMENT_KEY = "cellFragment";
    public static final String CELL_OPT_ABSENT_KEY = "cellOptAbsent";

    public static final String IMPURE_KEY = "impure";
    public static final String STRICT_KEY = "strict";
    public static final String SEQSTRICT_KEY = "seqstrict";
    public static final String CONCRETE_KEY = "concrete";
    public static final String SYMBOLIC_KEY = "symbolic";
    public static final String LABEL_KEY = "label";
    public static final String UNBOUND_VARIABLES_KEY = "unboundVariables";
}
