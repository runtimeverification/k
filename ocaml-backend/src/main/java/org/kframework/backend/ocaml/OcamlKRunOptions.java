// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.ocaml;

import com.beust.jcommander.Parameter;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.StringListConverter;

import java.util.Collections;
import java.util.List;

@RequestScoped
public class OcamlKRunOptions {

    @Parameter(names="--ocaml-compile", description="Compile program to run into OCAML binary.")
    public boolean ocamlCompile;

    @Parameter(names="--ocaml-dump-exit-code", description="Exit code which should trigger a dump of the configuration when using --ocaml-compile.")
    public Integer dumpExitCode;

    @Parameter(names="--ocaml-serialize-config", listConverter=StringListConverter.class, description="<string> is a whitespace-separated list of configuration variables to precompute the value of")
    public List<String> serializeConfig = Collections.emptyList();

}
