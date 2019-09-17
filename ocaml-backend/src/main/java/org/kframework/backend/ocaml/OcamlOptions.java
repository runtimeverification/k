// Copyright (c) 2015-2018 Runtime Verification, Inc. (RV-Match team). All Rights Reserved.
package org.kframework.backend.ocaml;

import com.beust.jcommander.Parameter;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.StringListConverter;

import java.io.Serializable;
import java.util.Collections;
import java.util.List;

@RequestScoped
public class OcamlOptions implements Serializable {

    public boolean profileRules;

    @Parameter(names="--gen-ml-only", description="Do not compile definition; only generate .ml files.")
    public boolean genMLOnly;

    @Parameter(names="--packages", listConverter=StringListConverter.class, description="<string> is a whitespace-separated list of ocamlfind packages to be included in the compilation of the definition")
    public List<String> packages = Collections.emptyList();

    @Parameter(names="--no-link-prelude", description="Do not link interpreter binaries against constants.cmx, prelude.cmx, plugin.cmx, lexer.cmx, parser.cmx, hooks.cmx and run.cmx. Do not use this if you don't know what you're doing.")
    public boolean noLinkPrelude;

    @Parameter(names="--no-expand-macros", description="Do not expand macros on initial configurations at runtime. Will likely cause incorrect behavior if any macros are used in this term.")
    public boolean noExpandMacros;

    @Parameter(names="--opaque-klabels", description="Declare all the klabels declared by the following secondary definition.")
    public String klabels;

    @Parameter(names="--ocaml-dump-exit-code", description="Exit code which should trigger a dump of the configuration when using --ocaml-compile.")
    public Integer dumpExitCode;

    @Parameter(names="--ocaml-serialize-config", listConverter=StringListConverter.class, description="<string> is a whitespace-separated list of configuration variables to precompute the value of")
    public List<String> serializeConfig = Collections.emptyList();

    @Parameter(names="-O2", description="Optimize in ways that improve performance, but intere with debugging and increase compilation time and code size slightly.")
    public boolean optimize2;

    @Parameter(names="-O3", description="Optimize aggressively in ways that significantly improve performance, but also increase compilation time and code size.")
    public boolean optimize3;

    @Parameter(names="-Og", description="Optimize as much as possible without interfering with debugging experience.")
    public boolean optimizeG;

    @Parameter(names="--reverse-rules", description="Reverse the order of rules as much as possible in order to find most nondeterminism without searching.")
    public boolean reverse;

    @Parameter(names="--check-races", description="Checks for races among regular rules.")
    public boolean checkRaces;

    public boolean ocamlopt() { return optimize2 || optimize3; }
    public boolean optimizeStep() { return optimize3 || optimizeG; }
}
