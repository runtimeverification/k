// Copyright (c) 2014 K Team. All Rights Reserved.
package main.btrace.org.kframework.backend.java.profile;

import com.sun.btrace.aggregation.Aggregation;
import com.sun.btrace.aggregation.AggregationFunction;
import com.sun.btrace.annotations.*;
import static com.sun.btrace.BTraceUtils.*;

@BTrace(name="JavaSymbolicKRunStats")
public class JavaKRunTrace {

    private static long KRUN_RUN_TIME               = 0;
    private static long RUN_PARSER_OR_DIE_TIME      = 0;
    private static long INIT_KRUN_TIME              = 0;
    private static long KIL_TO_BACKEND_JAVA_KIL_TIME= 0;
    private static long APPROX_FUNC_EVAL_TIME       = 0;
    private static long DATA_STRUCT_LOOKUP_TIME     = 0;
    private static long DATA_STRUCT_UPDATE_TIME     = 0;
    private static long INDEX_LOOKUP_TIME           = 0;
    private static long UNIFY_TIME                  = 0;
    private static long FAILED_UNIFY_TIME           = 0;
    private static long PREPARE_PATTERN_TIME        = 0;
    private static long CONSTRUCT_NEW_SUBJECT_TIME  = 0;
    private static long TOTAL_REWRITE_TIME          = 0;
    private static long TOTAL_EXEC_TIME             = 0;

    private static Aggregation AVG_SUCCESSFUL_UNIFY_TIME = Aggregations.newAggregation(AggregationFunction.AVERAGE);
    private static Aggregation AVG_FAILED_UNIFY_TIME = Aggregations.newAggregation(AggregationFunction.AVERAGE);

    private static long NUM_RULES_RETRIEVED = 0;
    private static long NUM_RULES_ATTEMPTED = 0;
    private static long NUM_RULES_SUCCEEDED = 0;

    @OnMethod(clazz = "org.kframework.backend.java.symbolic.JavaSymbolicKRun", method = "run",  location = @Location(Kind.RETURN))
    public static void onJavaSymbolicKRunRunReturn(@Duration long duration) {
        KRUN_RUN_TIME += duration / 1000;
    }

    @OnMethod(clazz = "org.kframework.krun.RunProcess", method = "runParserOrDie",  location = @Location(Kind.RETURN))
    public static void onRunParserOrDieReturn(@Duration long duration) {
        RUN_PARSER_OR_DIE_TIME += duration / 1000;
    }

    @OnMethod(clazz = "org.kframework.krun.Main", method = "obtainKRun",  location = @Location(Kind.RETURN))
    public static void onObtainKRunReturn(@Duration long duration) {
        INIT_KRUN_TIME += duration / 1000;
    }

//    @OnMethod(clazz = "org.kframework.backend.java.kil.Term", method = "<init>",  location = @Location(Kind.RETURN))
//    public static void onTermFactoryMethodReturn(@Duration long duration) {
//        // TODO(YilongL): unable to instrument static method in abstract class?
//        KIL_TO_BACKEND_KIL_TIME += duration / 1000;
//    }

    @OnMethod(clazz = "org.kframework.backend.java.symbolic.KILtoBackendJavaKILTransformer", method = "/transform(Definition|Rule|Term)/",  location = @Location(Kind.RETURN))
    public static void onKILtoBackendJavaKILTransformationReturn(@Duration long duration) {
        KIL_TO_BACKEND_JAVA_KIL_TIME += duration / 1000;
    }

    /**
     * Accumulates the wall time of each invocation of the
     * {@link org.kframework.backend.java.kil.KItem#evaluateFunction} method.
     * Hence recursive invocation of the method will be double-counted, which
     * makes the measured time falsely longer than the actual time slightly.
     */
    @OnMethod(clazz = "org.kframework.backend.java.kil.KItem", method = "evaluateFunction",  location = @Location(Kind.RETURN))
    public static void onEvalFunctionReturn(@Duration long duration) {
        // TODO(YilongL): maybe switch to BTrace's builtin profiler in the future
        APPROX_FUNC_EVAL_TIME += duration / 1000;
    }

    @OnMethod(clazz = "/org.kframework.backend.java.kil.(List|Set|Map)Lookup/", method = "evaluateLookup",  location = @Location(Kind.RETURN))
    public static void onDataStructureLookupReturn(@Duration long duration) {
        DATA_STRUCT_LOOKUP_TIME += duration / 1000;
    }

    @OnMethod(clazz = "/org.kframework.backend.java.kil.(Map|Set)Update/", method = "evaluateUpdate",  location = @Location(Kind.RETURN))
    public static void onDataStructureUpdateReturn(@Duration long duration) {
        DATA_STRUCT_UPDATE_TIME += duration / 1000;
    }

    @OnMethod(clazz = "org.kframework.backend.java.symbolic.SymbolicRewriter", method = "getRules", location = @Location(Kind.RETURN))
    public static void onLookupIndex(@Return java.util.List<?> rules, @Duration long duration) {
        INDEX_LOOKUP_TIME += duration / 1000;
        NUM_RULES_RETRIEVED += size(rules);
    }

    @OnMethod(clazz = "org.kframework.backend.java.symbolic.SymbolicRewriter", method = "preparePattern",  location = @Location(Kind.RETURN))
    public static void onConstructPatternTermReturn(@Duration long duration) {
        PREPARE_PATTERN_TIME += duration / 1000;
    }

    @OnMethod(clazz = "org.kframework.backend.java.symbolic.SymbolicRewriter", method = "getUnificationResults",  location = @Location(Kind.RETURN))
    public static void onUnificationReturn(@Return java.util.List<?> constraints, @Duration long duration) {
        UNIFY_TIME += duration / 1000;
        NUM_RULES_ATTEMPTED++;
        if (size(constraints) == 0) {
            FAILED_UNIFY_TIME += duration / 1000;
            Aggregations.addToAggregation(AVG_FAILED_UNIFY_TIME, duration / 1000);
        } else {
            Aggregations.addToAggregation(AVG_SUCCESSFUL_UNIFY_TIME, duration / 1000);
        }
    }

    @OnMethod(clazz = "org.kframework.backend.java.symbolic.SymbolicRewriter", method = "constructNewSubjectTerm",  location = @Location(Kind.RETURN))
    public static void onConstructNewSubjectTermReturn(@Duration long duration) {
        NUM_RULES_SUCCEEDED++;
        CONSTRUCT_NEW_SUBJECT_TIME += duration / 1000;
    }

    @OnMethod(clazz = "org.kframework.backend.java.symbolic.SymbolicRewriter", method = "rewrite", location = @Location(Kind.RETURN))
    public static void onRewriteEngineReturn(@Duration long duration) {
        TOTAL_REWRITE_TIME += duration / 1000;
    }

    @OnMethod(clazz = "org.kframework.krun.Main", method = "execute_Krun", location = @Location(Kind.RETURN))
    public static void onMainReturn(@Duration long duration) {
        TOTAL_EXEC_TIME += duration / 1000;

        println(strcat("Total Exec. Time (ms): ", str(TOTAL_EXEC_TIME / 1000)));
        println(strcat("    Parsing Time (ms): ", str(RUN_PARSER_OR_DIE_TIME / 1000)));
        println(strcat("    Init. KRun Object Time (ms): ", str(INIT_KRUN_TIME / 1000)));
        println(strcat("    JavaSymbolicKRun#run Time (ms): ", str(KRUN_RUN_TIME / 1000)));
        println(strcat("        KIL to Backend KIL Time (ms): ", str(KIL_TO_BACKEND_JAVA_KIL_TIME / 1000)));
        println(strcat("        Total Rewrite Time (ms): ", str(TOTAL_REWRITE_TIME / 1000)));
        println(strcat("            Index Lookup Time (ms): ", str(INDEX_LOOKUP_TIME / 1000)));
        println(strcat("            Preparing Pattern Term Time (ms): ", str(PREPARE_PATTERN_TIME / 1000)));
        println(strcat("            Total Unification Time (ms): ", str(UNIFY_TIME / 1000)));
        println(strcat("                Failed Unification Time (ms): ", str(FAILED_UNIFY_TIME / 1000)));
        println(strcat("                Builtin Data Structure Lookup Time (ms): ", str(DATA_STRUCT_LOOKUP_TIME / 1000)));
        println(strcat("                Builtin Data Structure Update Time (ms): ", str(DATA_STRUCT_UPDATE_TIME / 1000)));
        println(strcat("            Constructing New Subject Term Time (ms): ", str(CONSTRUCT_NEW_SUBJECT_TIME / 1000)));
        println(strcat("            Approx. Function Eval. Time (ms): ", str(APPROX_FUNC_EVAL_TIME / 1000)));
        println();

        println(strcat("#Rules Retrieved: ", str(NUM_RULES_RETRIEVED)));
        println(strcat("#Rules Attempted: ", str(NUM_RULES_ATTEMPTED)));
        println(strcat("#Rules Succeeded: ", str(NUM_RULES_SUCCEEDED)));
        println();

        printAggregation("", AVG_SUCCESSFUL_UNIFY_TIME, "Avg. Time per Successful Unification: %s μs");
        printAggregation("", AVG_FAILED_UNIFY_TIME, "Avg. Time per Failed Unification: %s μs");
    }
}
