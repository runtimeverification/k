// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

public class TestCaseGenerationSettings {

    public static final boolean TWO_PHASE_GENERATION = true;

    public static final boolean PHASE_ONE_BOUND_SUCCESSORS = true;
    public static final boolean PHASE_ONE_BOUND_FREEVARS = true;
    /** Only has effect when {@code TWO_PHASE_GENERATION} is false. */
    public static final boolean PHASE_ONE_ONLY_OUTPUT_GROUND_TERM = false;
    public static final int PHASE_ONE_MAX_NUM_SUCCESSORS = 10;
    public static final int PHASE_ONE_MAX_NUM_FREEVARS = 10;

    public static final int PHASE_TWO_MAX_NUM_SUCCESSORS = 3;
    public static final int PHASE_TWO_MAX_REWRITE_STEPS = 100;

}