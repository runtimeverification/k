// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import org.kframework.utils.OS;
import org.kframework.utils.file.KPaths;

import java.io.File;

/**
 * @author Traian
 */
public class Z3Wrapper {

    public static final String SMT_PRELUDE =
            "(define-sort IntSet () (Array Int Bool))\n" +
            "(define-fun smt_set_mem ((x Int) (s IntSet)) Bool (select s x))\n" +
            "(define-fun smt_set_add ((s IntSet) (x Int)) IntSet  (store s x true))\n" +
            "(define-fun smt_set_emp () IntSet ((as const IntSet) false))\n" +
            "(define-fun smt_set_cup ((s1 IntSet) (s2 IntSet)) IntSet ((_ map or) s1 s2))\n" +
            "(define-fun smt_set_cap ((s1 IntSet) (s2 IntSet)) IntSet ((_ map and) s1 s2))\n" +
            "(define-fun smt_set_com ((s IntSet)) IntSet ((_ map not) s))\n" +
            "(define-fun smt_set_sin ((x Int)) IntSet (smt_set_add smt_set_emp x))\n" +
            "(define-fun smt_set_dif ((s1 IntSet) (s2 IntSet)) IntSet (smt_set_cap s1 (smt_set_com s2)))\n" +
            "(define-fun smt_set_sub ((s1 IntSet) (s2 IntSet)) Bool (= smt_set_emp (smt_set_dif s1 s2)))\n" +
            "(define-fun smt_set_lt  ((s1 IntSet) (s2 IntSet)) Bool (forall ((i Int) (j Int)) (implies (>= i j) (not (and (select s1 i) (select s2 j))))))\n" +
            "(define-fun smt_set_le  ((s1 IntSet) (s2 IntSet)) Bool (forall ((i Int) (j Int)) (implies (>  i j) (not (and (select s1 i) (select s2 j))))))\n" +
            "\n" +
            "(declare-datatypes () ((Tree leaf (node (key Int) (left Tree) (right Tree)))))\n" +
            "(declare-fun smt_tree_keys ((Tree)) IntSet)\n" +
            "(declare-fun smt_tree_height ((Tree)) Int)\n" +
            "(declare-fun smt_bst ((Tree)) Bool)";

    public static boolean initialized = false;
    public static com.microsoft.z3.Context newContext() throws Z3Exception {
        if (!initialized) {
            String libz3 = "libz3";
            switch (OS.current()) {
                case WIN:
                    libz3 += ".dll";
                    break;
                case UNIX:
                    libz3 += ".so";
                    break;
                case OSX:
                    libz3 += ".dylib";
            }
            System.load(KPaths.getJavaLibraryPath() + File.separator + libz3);
            initialized = true;
        }
        return new com.microsoft.z3.Context();
    }

    public static boolean checkQuery(String query) {
        boolean result = false;
        try {
            com.microsoft.z3.Context context = newContext();
            Solver solver = context.MkSolver();
            solver.Assert(context.ParseSMTLIB2String(SMT_PRELUDE + query, null, null, null, null));
            result = solver.Check() == Status.UNSATISFIABLE;
            context.Dispose();
        } catch (Z3Exception e) {
            e.printStackTrace();
        }
        return result;
    }
}

