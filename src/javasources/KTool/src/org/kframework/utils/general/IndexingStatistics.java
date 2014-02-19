package org.kframework.utils.general;

import com.google.common.base.Stopwatch;

import java.util.ArrayList;
import java.util.List;

/**
 * This class holds statistics about rewriting. The goal is to be able to compare different indexing
 * schemes and measure progress as we build them.
 *
 * Author: OwolabiL
 * Date: 2/18/14
 * Time: 4:51 PM
 */
public class IndexingStatistics {
    //TODO(OwolabiL): Make this a Singleton class instead
    public  static Stopwatch totalRewriteStopwatch = new Stopwatch();
    public  static Stopwatch totalKrunStopwatch = new Stopwatch();
    public  static Stopwatch indexConstructionStopWatch = new Stopwatch();
    public  static Stopwatch getRulesForTermStopWatch = new Stopwatch();
    public  static Stopwatch rewriteStepStopWatch = new Stopwatch();

    public  static List<Long> timesForRuleSelection = new ArrayList<>();
    public  static List<Long> timesForRewriteSteps = new ArrayList<>();
    public  static List<Integer> rulesSelectedAtEachStep = new ArrayList<>();

    public IndexingStatistics() {
    }


    public static void print() {
        System.err.println("=====================================================");
        System.err.println("Total KRun time: " + totalKrunStopwatch);
        System.err.println("Total Time For Rewriting: " + totalRewriteStopwatch);
        System.err.println("Time for constructing Index: " + indexConstructionStopWatch);
        System.err.println("Average time for Rule selection: " +
                computeAverage(timesForRuleSelection) + " \u00B5"+"s");
        System.err.println("Average time For Rewrite Steps: " +
                computeAverage(timesForRewriteSteps) + " \u00B5"+"s");
        System.err.println("Average rules selected at each step: " +
                computeAverages(rulesSelectedAtEachStep));
        System.err.println("times For Rule selection: " + timesForRuleSelection);
        System.err.println("times For Rewrite Steps: " + timesForRewriteSteps);
        System.err.println("Rules selected at each step: " + rulesSelectedAtEachStep);
        System.err.println("=====================================================");
    }

    //TODO(OwolaiL): These two methods should be merged since they have the same erasure
    private static double computeAverages(List<Integer> ruleCounts) {
        Integer sum = 0;
        for (int count: ruleCounts) {
            sum += count;
        }
        return ((double)sum)/ruleCounts.size();
    }

    private static double computeAverage(List<Long> times) {
        Long sum = 0L;
        for (Long time: times) {
             sum+=time;
        }
        return ((double)sum)/times.size();
    }
}
