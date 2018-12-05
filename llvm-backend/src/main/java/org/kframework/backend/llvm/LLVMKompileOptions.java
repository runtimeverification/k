// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.backend.llvm;

import com.beust.jcommander.Parameter;
import org.kframework.utils.inject.RequestScoped;

import java.util.ArrayList;
import java.util.List;

@RequestScoped
public class LLVMKompileOptions {

    @Parameter(names="-ccopt", description="Add a command line option to the compiler invocation for the llvm backend.")
    public List<String> ccopts = new ArrayList<>();

}
