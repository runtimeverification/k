package org.kframework.backend.java.util;

public class TestCaseGenerationSettings {

    public static final boolean TWO_PHASE_GENERATION = true;

    public static final boolean PHASE_ONE_BOUND_SUCCESSORS = true;
    public static final boolean PHASE_ONE_BOUND_FREEVARS = false;
    public static final int PHASE_ONE_MAX_NUM_SUCCESSORS = 50;
    public static final int PHASE_ONE_MAX_NUM_FREEVARS = 10;

    public static final int PHASE_TWO_MAX_NUM_SUCCESSORS = 3;

}