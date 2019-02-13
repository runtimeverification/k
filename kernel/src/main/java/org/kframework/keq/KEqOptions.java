package org.kframework.keq;


import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import org.kframework.main.GlobalOptions;
import org.kframework.unparser.PrintOptions;
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

    @ParametersDelegate
    public PrintOptions print = new PrintOptions();

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

    @Parameter(names={"--spec-module1", "-sm1"}, description="Name of module containing first specification to prove.")
    public String specModule1;

    @Parameter(names={"--spec-module2", "-sm2"}, description="Name of module containing second specification to prove.")
    public String specModule2;

    @Parameter(names={"--def-module1", "-m1"}, description="Name of module in first definition to use as definition.")
    public String defModule1;

    @Parameter(names={"--def-module2", "-m2"}, description="Name of module in second definition to use as definition.")
    public String defModule2;
}