// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.general;

import com.google.common.base.Stopwatch;

import java.util.ArrayList;
import java.util.List;

/**
 * This class holds statistics about rewriting. The goal is to be able to compare different indexing
 * schemes and measure progress as we build them.
 * TODO(OwolabiL): This should be removed once I get a good handle on the visual vm way of profiling.
 * <p/>
 * Author: OwolabiL
 * Date: 2/18/14
 * Time: 4:51 PM
 */
public class IndexingStatistics {
    //TODO(OwolabiL): Make this a Singleton class instead
    public static Stopwatch totalRewriteStopwatch = new Stopwatch();
    public static Stopwatch totalKrunStopwatch = new Stopwatch();
    public static Stopwatch totalSearchStopwatch = new Stopwatch();
    public static Stopwatch indexConstructionStopWatch = new Stopwatch();
    public static Stopwatch getRulesForTermStopWatch = new Stopwatch();
    public static Stopwatch getPStringFromTermStopWatch = new Stopwatch();
    public static Stopwatch findMatchingIndicesStopWatch = new Stopwatch();
    public static Stopwatch rewriteStepStopWatch = new Stopwatch();
    public static Stopwatch rewritingStopWatch = new Stopwatch();
    public static Stopwatch preProcessStopWatch = new Stopwatch();
    public static Stopwatch kilTransformationStopWatch = new Stopwatch();
    public static Stopwatch getPStringStopwatch = new Stopwatch();
    public static Stopwatch traverseCellsStopwatch = new Stopwatch();

    public static List<Number> timesForRuleSelection = new ArrayList<>();
    public static List<Number> timesForGettingPStringsFromTerm = new ArrayList<>();
    public static List<Number> timesForFindingMatchingIndices = new ArrayList<>();
    public static List<Number> timesForRewriteSteps = new ArrayList<>();
    public static List<Number> timesForRewriting = new ArrayList<>();
    public static List<Number> rulesSelectedAtEachStep = new ArrayList<>();
    public static List<Number> getPStringTimes = new ArrayList<>();
    public static List<Number> traverseCellsTimes = new ArrayList<>();
    public static List<Number> rulesTried = new ArrayList<>();

    public static void print() {
        System.err.println("=====================================================");
        System.err.println("Total KRun time: " + totalKrunStopwatch);
        System.err.println("Total Search time: " + totalSearchStopwatch);
        System.err.println("Total KRun Preprocessing time: " + preProcessStopWatch);
        System.err.println("\tTime for constructing Index: " + indexConstructionStopWatch);
        System.err.println("\tTime for transforming KIL: " + kilTransformationStopWatch);
        System.err.println("Total Time For Rewriting: " + totalRewriteStopwatch);
        System.err.println("\tTotal time for Rule selection: " +
                computeTotal(timesForRuleSelection) + " ms");
        System.err.println("\t\tTotal time for getting PStrings from term: " +
                computeTotal(timesForGettingPStringsFromTerm) + " ms");
        System.err.println("\t\t\tTotal time for traversing term: " +
                computeTotal(getPStringTimes) + " ms");
        System.err.println("\t\t\tTotal time traversing I/O cells: " +
                computeTotal(traverseCellsTimes) + " ms");
        System.err.println("\t\tTotal time for finding matching indices " +
                computeTotal(timesForFindingMatchingIndices) + " ms");
        System.err.println("\tTotal time for Actual Rewriting: " +
                computeTotal(timesForRewriting) + " ms");
        System.err.println("Total time For Rewrite Steps: " +
                computeTotal(timesForRewriteSteps) + " ms");
        System.err.println("Average time for Rule selection: " +
                computeAverage(timesForRuleSelection) + " \u00B5" + "s");
        System.err.println("\tAverage time for getting PStrings from term: " +
                computeAverage(timesForGettingPStringsFromTerm) + " \u00B5" + "s");
        System.err.println("\tAverage time for finding matching indices: " +
                computeAverage(timesForFindingMatchingIndices) + " \u00B5" + "s");
        System.err.println("Average time for Actual Rewriting: " +
                computeAverage(timesForRewriting) + " \u00B5" + "s");
        System.err.println("Average time For Rewrite Steps: " +
                computeAverage(timesForRewriteSteps) + " \u00B5" + "s");
        System.err.println("Average rules selected at each step: " +
                computeAverage(rulesSelectedAtEachStep));
        System.err.println("Min. Number of rules selected at each step: " +
                computeMin(rulesSelectedAtEachStep));
        System.err.println("Max. Number of rules selected at each step: " +
                computeMax(rulesSelectedAtEachStep));
        System.err.println("Total number of rules tried: " + findTotal(rulesTried));
        System.err.println("Average number of rules tried: " + computeAverage(rulesTried));
        System.err.println("Number of rules tried: " + rulesTried);
//        System.err.println("Times For Rule selection: " + timesForRuleSelection);
//        System.err.println("Times For Rewrite Steps: " + timesForRewriteSteps);
//        System.err.println("Rules selected at each step: " + rulesSelectedAtEachStep);
        System.err.println("=====================================================");
    }

    private static int computeMin(List<Number> rulesSelectedAtEachStep) {
        Number min = rulesSelectedAtEachStep.get(0);
        for (Number num : rulesSelectedAtEachStep) {
            if (!num.equals(0) && num.longValue() < min.longValue()) {
                min = num;
            }
        }
        return (Integer) min;
    }

    private static int computeMax(List<Number> rulesSelectedAtEachStep) {
        Number max = rulesSelectedAtEachStep.get(0);
        for (Number num : rulesSelectedAtEachStep) {
            if (num.longValue() > max.longValue()) {
                max = num;
            }
        }
        return (Integer) max;
    }

    private static double computeTotal(List<Number> times) {
        long sum = 0L;
        for (Number time : times) {
            sum += (Long) time;
        }
        return ((double) sum) / 1000;
    }

    private static double findTotal(List<Number> times) {
        long sum = 0;
        for (Number time : times) {
            sum += (Integer) time;
        }
        return sum;
    }

    private static double computeAverage(List<Number> times) {
        Long sum = 0L;
        for (Number time : times) {
            sum += time.longValue();
        }
        return ((double) sum) / times.size();
    }
}
