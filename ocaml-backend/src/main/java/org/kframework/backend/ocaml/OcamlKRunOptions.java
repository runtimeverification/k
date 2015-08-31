// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.ocaml;

import com.beust.jcommander.Parameter;
import org.kframework.utils.inject.RequestScoped;

@RequestScoped
public class OcamlKRunOptions {

    @Parameter(names="--ocaml-compile", description="Compile program to run into OCAML binary.")
    public boolean ocamlCompile;

    @Parameter(names="--ocaml-dump-exit-code", description="Exit code which should trigger a dump of the configuration when using --ocaml-compile.")
    public Integer dumpExitCode;
}
