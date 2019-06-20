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
}
