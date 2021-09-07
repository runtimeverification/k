// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.kompile;

import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.attributes.Source;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.compile.IncompleteCellUtils;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KToken;
import org.kframework.kore.Sort;
import org.kframework.kore.VisitK;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.inner.ParseInModule;
import org.kframework.parser.inner.generator.RuleGrammarGenerator;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.StringUtil;
import scala.Option;
import scala.Tuple2;
import scala.util.Either;

import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * A class representing a compiled definition. It has everything needed for executing and parsing programs.
 */

public class CompiledDefinition implements Serializable {
    public final KompileOptions kompileOptions;
    private  transient final GlobalOptions globalOptions;
    private final Definition parsedDefinition;
    public final Definition kompiledDefinition;
    public final Sort programStartSymbol;
    public final HashMap<String, Sort> configurationVariableDefaultSorts = new HashMap<>();
    public final KLabel topCellInitializer;
    private final Module languageParsingModule;
    public final Rule exitCodePattern;
    private Map<String, Rule> cachedcompiledPatterns = new ConcurrentHashMap<>();
    private Map<String, Rule> cachedParsedPatterns = new ConcurrentHashMap<>();


    public CompiledDefinition(KompileOptions kompileOptions, GlobalOptions globalOptions, Definition parsedDefinition, Definition kompiledDefinition, FileUtil files, KExceptionManager kem, KLabel topCellInitializer) {
        this.kompileOptions = kompileOptions;
        this.globalOptions = globalOptions;
        this.parsedDefinition = parsedDefinition;
        this.kompiledDefinition = kompiledDefinition;
        initializeConfigurationVariableDefaultSorts(files);
        this.programStartSymbol = configurationVariableDefaultSorts.getOrDefault("$PGM", Sorts.K());
        this.topCellInitializer = topCellInitializer;
        this.languageParsingModule = kompiledDefinition.getModule("LANGUAGE-PARSING").get();
        Rule exitCodeRule;
        if (kompileOptions.isKore()) {
            exitCodeRule = null;
        } else {
            exitCodeRule = getExitCodeRule(parsedDefinition);
        }
        if (exitCodeRule == null) {
            this.exitCodePattern = null;
        } else {
            this.exitCodePattern = new Kompile(kompileOptions, globalOptions, files, kem).compileRule(kompiledDefinition, exitCodeRule);
        }
    }

    private Rule getExitCodeRule(Definition parsedDefinition) {
        Module mainMod = parsedDefinition.mainModule();
        Set<Production> exitProds = stream(mainMod.productions()).filter(p -> p.att().contains("exit")).collect(Collectors.toSet());
        if (exitProds.size() == 0) {
            return null;
        } else if (exitProds.size() > 1) {
            throw KEMException.compilerError("Found more than one or zero productions with 'exit' attribute. Exactly one production, a cell, must have this attribute, designating the exit code of krun. Found:\n" + exitProds);
        }
        Production exitProd = exitProds.iterator().next();
        return Rule(IncompleteCellUtils.make(exitProd.klabel().get(), false, KApply(KLabel("#SemanticCastToInt"), KVariable("_")), false), BooleanUtils.TRUE, BooleanUtils.TRUE);
    }

    private void initializeConfigurationVariableDefaultSorts(FileUtil files) {
        StringBuilder sb = new StringBuilder();
        sb.append("#!/usr/bin/env bash\n\n");
        StringBuilder arr = new StringBuilder("declaredConfigVars=(\n");
        // searching for #SemanticCastTo<Sort>(Map:lookup(_, #token(<VarName>, KConfigVar)))
        Collections.stream(kompiledDefinition.mainModule().rules())
                .forEach(r -> {
                    new VisitK() {
                        @Override
                        public void apply(KApply k) {
                            if (k.klabel().name().startsWith("project:")
                                    && k.items().size() == 1 && k.items().get(0) instanceof KApply) {
                                KApply theMapLookup = (KApply) k.items().get(0);
                                if (KLabels.MAP_LOOKUP.equals(theMapLookup.klabel())
                                        && theMapLookup.size() == 2 && theMapLookup.items().get(1) instanceof KToken) {
                                    KToken t = (KToken) theMapLookup.items().get(1);
                                    if (t.sort().equals(Sorts.KConfigVar())) {
                                        Sort sort = Outer.parseSort(k.klabel().name().substring("project:".length()));
                                        configurationVariableDefaultSorts.put(t.s(), sort);
                                        if (sort.equals(Sorts.K())) {
                                          sort = Sorts.KItem();
                                        }
                                        String str = "declaredConfigVar_" + t.s().substring(1) + "='" + sort.toString() + "'\n";
                                        sb.append(str);
                                        String astr = "    '" + t.s().substring(1) + "'\n";
                                        arr.append(astr);
                                    }
                                }
                            }
                            super.apply(k);
                        }
                    }.apply(r.body());
                });
        sb.append(arr);
        sb.append(")\n");

        for (Production prod : iterable(kompiledDefinition.mainModule().productions())) {
            if (prod.att().contains("cell") && prod.att().contains("parser")) {
                String att = prod.att().get("parser");
                String[][] parts = StringUtil.splitTwoDimensionalAtt(att);
                for (String[] part : parts) {
                    if (part.length != 2) {
                        throw KEMException.compilerError("Invalid value for parser attribute: " + att, prod);
                    }
                    String name = part[0];
                    String module = part[1];
                    sb.append("declaredConfigVarModule_" + name + "='" + module + "'\n");
                }
            }
        }

        files.saveToKompiled("configVars.sh", sb.toString());
    }

    /**
     * The parsed but uncompiled definition
     */
    public Definition getParsedDefinition() {
        return parsedDefinition;
    }

    /**
     * A module containing the compiled definition
     */
    public Module executionModule() {
        return kompiledDefinition.mainModule();
    }

    public String mainSyntaxModuleName() { return parsedDefinition.att().<String>getOptional(Att.SYNTAX_MODULE()).get(); }

    /**
     * @return the module used for generating the program (i.e. ground) parser for the module named moduleName
     * It automatically generates this module unless the user has already defined a module postfixed with
     * {@link RuleGrammarGenerator#POSTFIX}. In latter case, it uses the user-defined module.
     */
    public Option<Module> programParsingModuleFor(String moduleName, KExceptionManager kem) {
        RuleGrammarGenerator gen = new RuleGrammarGenerator(parsedDefinition);

        Option<Module> userProgramParsingModule = parsedDefinition.getModule(moduleName + RuleGrammarGenerator.POSTFIX);
        if (userProgramParsingModule.isDefined()) {
            return userProgramParsingModule;
        } else {
            Option<Module> moduleOption = parsedDefinition.getModule(moduleName);
            Option<Module> programParsingModuleOption = moduleOption.isDefined() ?
                    Option.apply(gen.getProgramsGrammar(moduleOption.get())) :
                    Option.empty();
            return programParsingModuleOption;
        }
    }

    public Module languageParsingModule() { return languageParsingModule; }

    /**
     * Creates a parser for a module and use it to parse a term.
     *
     * @return the parsed term.
     */

    public K parseSingleTerm(Module module, Sort programStartSymbol, KExceptionManager kem, String s, Source source) {
        try (ParseInModule parseInModule = RuleGrammarGenerator.getCombinedGrammar(module, kompileOptions.strict())) {
            Tuple2<Either<Set<KEMException>, K>, Set<KEMException>> res = parseInModule.parseString(s, programStartSymbol, source);
            kem.addAllKException(res._2().stream().map(e -> e.getKException()).collect(Collectors.toSet()));
            if (res._1().isLeft()) {
                throw res._1().left().get().iterator().next();
            }
            return new TreeNodesToKORE(Outer::parseSort, kompileOptions.strict()).down(res._1().right().get());
        }
    }

    public Module getExtensionModule(Module module) {
        return RuleGrammarGenerator.getCombinedGrammar(module, kompileOptions.strict()).getExtensionModule();
    }

    public Rule compilePatternIfAbsent(FileUtil files, KExceptionManager kem, String pattern, Source source) {
        return cachedcompiledPatterns.computeIfAbsent(pattern, p -> new Kompile(kompileOptions, globalOptions, files, kem).parseAndCompileRule(this, p, source,
                Optional.of(parsePatternIfAbsent(files, kem, pattern, source))));
    }

    public Rule parsePatternIfAbsent(FileUtil files, KExceptionManager kem, String pattern, Source source) {
        return cachedParsedPatterns.computeIfAbsent(pattern, p -> new Kompile(kompileOptions, globalOptions, files, kem).parseRule(this, p, source));
    }
}
