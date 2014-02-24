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
    public  static Stopwatch getPStringFromTermStopWatch = new Stopwatch();
    public  static Stopwatch findMatchingIndicesStopWatch = new Stopwatch();
    public  static Stopwatch rewriteStepStopWatch = new Stopwatch();
    public  static Stopwatch rewritingStopWatch = new Stopwatch();
    public  static Stopwatch preProcessStopWatch = new Stopwatch();
    public  static Stopwatch kilTransformationStopWatch = new Stopwatch();

    public  static List<Long> timesForRuleSelection = new ArrayList<>();
    public  static List<Long> timesForGettingPStringsFromTerm = new ArrayList<>();
    public  static List<Long> timesForFindingMatchingIndices = new ArrayList<>();
    public  static List<Long> timesForRewriteSteps = new ArrayList<>();
    public  static List<Long> timesForRewriting= new ArrayList<>();
    public  static List<Integer> rulesSelectedAtEachStep = new ArrayList<>();

    public IndexingStatistics() {
    }


    public static void print() {
        System.err.println("=====================================================");
        System.err.println("Total KRun time: " + totalKrunStopwatch);
        System.err.println("Total KRun Preprocessing time: " + preProcessStopWatch);
        System.err.println("\tTime for constructing Index: " + indexConstructionStopWatch);
        System.err.println("\tTime for transforming KIL: " + kilTransformationStopWatch);
        System.err.println("Total Time For Rewriting: " + totalRewriteStopwatch);
        System.err.println("\tTotal time for Rule selection: " +
                computeTotal(timesForRuleSelection) + " ms");
        System.err.println("\t\tTotal time for getting PStrings from term: " +
                computeTotal(timesForGettingPStringsFromTerm) + " ms");
        System.err.println("\t\tTotal time for finding matching indices " +
                computeTotal(timesForFindingMatchingIndices) + " ms");
        System.err.println("\tTotal time for Actual Rewriting: " +
                computeTotal(timesForRewriting) + " ms");
        System.err.println("Total time For Rewrite Steps: " +
                computeTotal(timesForRewriteSteps) + " ms");
        System.err.println("Average time for Rule selection: " +
                computeAverage(timesForRuleSelection) + " \u00B5"+"s");
        System.err.println("\tAverage time for getting PStrings from term: " +
                computeAverage(timesForGettingPStringsFromTerm) + " \u00B5"+"s");
        System.err.println("\tAverage time for finding matching indices: " +
                computeAverage(timesForFindingMatchingIndices) + " \u00B5"+"s");
        System.err.println("Average time for Actual Rewriting: " +
                computeAverage(timesForRewriting) + " \u00B5"+"s");
        System.err.println("Average time For Rewrite Steps: " +
                computeAverage(timesForRewriteSteps) + " \u00B5"+"s");
        System.err.println("Average rules selected at each step: " +
                computeAverages(rulesSelectedAtEachStep));
        System.err.println("Min. Number of rules selected at each step: " +
                computeMin(rulesSelectedAtEachStep));
        System.err.println("Max. Number of rules selected at each step: " +
                computeMax(rulesSelectedAtEachStep));
//        System.err.println("Times For Rule selection: " + timesForRuleSelection);
//        System.err.println("Times For Rewrite Steps: " + timesForRewriteSteps);
//        System.err.println("Rules selected at each step: " + rulesSelectedAtEachStep);
        System.err.println("=====================================================");
    }

    private static int computeMin(List<Integer> rulesSelectedAtEachStep) {
        int min = rulesSelectedAtEachStep.get(0);
        for (int num:rulesSelectedAtEachStep){
            if(num == 0){
                continue;
            }

            if (num < min){
                min = num;
            }
        }
        return min;
    }

    private static int computeMax(List<Integer> rulesSelectedAtEachStep) {
        int max = rulesSelectedAtEachStep.get(0);
        for (int num:rulesSelectedAtEachStep){
            if (num > max){
                max = num;
            }
        }
        return max;
    }

    private static double computeTotal(List<Long> times) {
        long sum = 0L;
        for (long time : times){
            sum +=time;
        }
        return ((double)sum)/1000;
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
