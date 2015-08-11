// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.ocaml;

import com.beust.jcommander.Parameter;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.StringListConverter;

import java.io.Serializable;
import java.util.Collections;
import java.util.List;

@RequestScoped
public class OcamlOptions implements Serializable {

    @Parameter(names="--ocamlopt", description="Compile ocaml files with ocamlopt. Causes faster rewriting speeds but more time spent compiling.")
    public boolean ocamlopt;

    public boolean profileRules;

    @Parameter(names="--gen-ml-only", description="Do not compile definition; only generate .ml files.")
    public boolean genMLOnly;

    @Parameter(names="--packages", listConverter=StringListConverter.class, description="<string> is a whitespace-separated list of ocamlfind packages to be included in the compilation of the definition")
    public List<String> packages = Collections.emptyList();

    @Parameter(names="--hook-namespaces", listConverter=StringListConverter.class, description="<string> is a whitespace-separated list of namespaces to include in the hooks defined in the definition")
    public List<String> hookNamespaces = Collections.emptyList();

    @Parameter(names="--no-link-prelude", description="Do not link interpreter binaries against constants.cmx and prelude.cmx. Do not use this if you don't know what you're doing.")
    public boolean noLinkPrelude;

}
