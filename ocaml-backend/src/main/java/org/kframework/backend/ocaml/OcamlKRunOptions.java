// Copyright (c) 2015-2018 Runtime Verification, Inc. (RV-Match team). All Rights Reserved.
package org.kframework.backend.ocaml;

import com.beust.jcommander.Parameter;
import org.kframework.utils.inject.RequestScoped;

@RequestScoped
public class OcamlKRunOptions {

    @Parameter(names="--ocaml-compile", description="Compile program to run into OCAML binary.")
    public boolean ocamlCompile;

    @Parameter(names="--mini-krun", description="Use minimalist krun pipeline for faster performance.")
    public boolean miniKRun;

    @Parameter(names="--interpret", description="Use even more minimal interpreter pipeline for faster performance.")
    public boolean interpret;

    @Parameter(names="--native-compiler", description="Command to use to perform native linking.")
    public String nativeCompiler;

    @Parameter(names="--argv", description="Additional argument to pass to interpreter binary")
    public String argv = "";
}
