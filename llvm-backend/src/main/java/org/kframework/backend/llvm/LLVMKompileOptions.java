// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.llvm;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.IStringConverter;
import org.kframework.utils.inject.RequestScoped;

import java.util.Arrays;
import java.util.ArrayList;
import java.util.List;

@RequestScoped
public class LLVMKompileOptions {

    @Parameter(names="-ccopt", description="Add a command line option to the compiler invocation for the llvm backend.", listConverter=SingletonListConverter.class)
    public List<String> ccopts = new ArrayList<>();

    public static class SingletonListConverter implements IStringConverter<List<String>> {
        @Override
        public List<String> convert(String str) {
            return Arrays.asList(str);
        }
    }

    @Parameter(names="--heuristic", description="A string of single characters representing a sequence of heuristics to use during pattern matching compilation. Valid choices are f, d, b, a, l, r, n, p, q, _, N, L, R.")
    public String heuristic = "qbaL";

    @Parameter(names="--iterated", description="Generate iterated pattern matching optimization; time-consuming but significantly reduces matching time.")
    public boolean iterated = false;

    @Parameter(names="--iterated-threshold", description="Threshold heuristic to use when choosing which axioms to optimize. A value of 0 turns the optimization off; a value of 1 turns the optimization on for every axiom. Values in between (expressed as a fraction of two integers, e.g. 1/2), control the aggressiveness of the optimization. Higher values increase compilation times extremely, but also increase the effectiveness of the optimization. Consider decreasing this threshold if compilation is too slow.")
    public String iteratedThreshold = "1/2";

    @Parameter(names="--no-llvm-kompile", description="Do not invoke llvm-kompile. Useful if you want to do it yourself when building with the LLVM backend.")
    public boolean noLLVMKompile;
}
