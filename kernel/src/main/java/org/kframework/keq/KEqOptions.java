package org.kframework.keq;


import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.DefinitionLoadingOptions;
import org.kframework.utils.options.SMTOptions;

@RequestScoped
public final class KEqOptions {
    @ParametersDelegate
    public transient GlobalOptions global = new GlobalOptions();

    @ParametersDelegate
    public DefinitionLoadingOptions definitionLoading = new DefinitionLoadingOptions();

    @ParametersDelegate
    public SMTOptions smt = new SMTOptions();

    @Parameter(names={"--definition1", "-d1"}, description="Path to the directory in which the first kompiled " +
            "K definition resides. The default is the unique, only directory with the suffix '-kompiled' " +
            "in the current directory.")
    public String def1;


    @Parameter(names={"--definition2", "-d2"}, description="Path to the directory in which the second kompiled " +
            "K definition resides. The default is the unique, only directory with the suffix '-kompiled' " +
            "in the current directory.")
    public String def2;

    @Parameter(names={"--spec1", "-s1"}, description="Path to specification for first program.")
    public String spec1;

    @Parameter(names={"--spec2", "-s2"}, description="Path to specification for second program.")
    public String spec2;
}