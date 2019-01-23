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
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.concrete2kore.ParseInModule;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.file.FileUtil;
import scala.Option;
import scala.Tuple2;
import scala.util.Either;

import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * A class representing a compiled definition. It has everything needed for executing and parsing programs.
 */

public class CompiledDefinition implements Serializable {
    public final KompileOptions kompileOptions;
    private final Definition parsedDefinition;
    public final Definition kompiledDefinition;
    public final Sort programStartSymbol;
    public final HashMap<String, Sort> configurationVariableDefaultSorts = new HashMap<>();
    public final KLabel topCellInitializer;
    private final Module languageParsingModule;
    public final Rule exitCodePattern;
    private Map<String, Rule> cachedcompiledPatterns = new ConcurrentHashMap<>();
    private Map<String, Rule> cachedParsedPatterns = new ConcurrentHashMap<>();


    public CompiledDefinition(KompileOptions kompileOptions, Definition parsedDefinition, Definition kompiledDefinition, FileUtil files, KExceptionManager kem, KLabel topCellInitializer) {
        this.kompileOptions = kompileOptions;
        this.parsedDefinition = parsedDefinition;
        this.kompiledDefinition = kompiledDefinition;
        initializeConfigurationVariableDefaultSorts();
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
            this.exitCodePattern = new Kompile(kompileOptions, files, kem).compileRule(kompiledDefinition, exitCodeRule);
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

    private void initializeConfigurationVariableDefaultSorts() {
        // searching for #SemanticCastTo<Sort>(Map:lookup(_, #token(<VarName>, KConfigVar)))
        Collections.stream(parsedDefinition.mainModule().rules())
                .forEach(r -> {
                    new VisitK() {
                        @Override
                        public void apply(KApply k) {
                            if (k.klabel().name().contains("#SemanticCastTo")
                                    && k.items().size() == 1 && k.items().get(0) instanceof KApply) {
                                KApply theMapLookup = (KApply) k.items().get(0);
                                if (theMapLookup.klabel().name().startsWith("project:")) {
                                    theMapLookup = (KApply) theMapLookup.items().get(0);
                                }
                                if (KLabels.MAP_LOOKUP.equals(theMapLookup.klabel())
                                        && theMapLookup.size() == 2 && theMapLookup.items().get(1) instanceof KToken) {
                                    KToken t = (KToken) theMapLookup.items().get(1);
                                    if (t.sort().equals(Sorts.KConfigVar())) {
                                        Sort sort = Outer.parseSort(k.klabel().name().replace("#SemanticCastTo", ""));
                                        configurationVariableDefaultSorts.put(t.s(), sort);
                                    }
                                }
                            }
                            super.apply(k);
                        }
                    }.apply(r.body());
                });
    }

    /**
     * A function that takes a string and the source of that string and parses it as a program into KAST.
     */
    public BiFunction<String, Source, K> getProgramParser(KExceptionManager kem) {
        return getParser(programParsingModuleFor(mainSyntaxModuleName(), kem).get(), programStartSymbol, kem);
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

    public String mainSyntaxModuleName() { return parsedDefinition.att().<String>getOptional(Att.syntaxModule()).get(); }

    /**
     * @return the module used for generating the program (i.e. ground) parser for the module named moduleName
     * It automatically generates this module unless the user has already defined a module postfixed with
     * {@link RuleGrammarGenerator#POSTFIX}. In latter case, it uses the user-defined module.
     */
    public Option<Module> programParsingModuleFor(String moduleName, KExceptionManager kem) {
        RuleGrammarGenerator gen = new RuleGrammarGenerator(parsedDefinition);

        Option<Module> userProgramParsingModule = parsedDefinition.getModule(moduleName + RuleGrammarGenerator.POSTFIX);
        if (userProgramParsingModule.isDefined()) {
            kem.registerInternalHiddenWarning("Module " + userProgramParsingModule.get().name() + " is user-defined.");
            return userProgramParsingModule;
        } else {
            Option<Module> moduleOption = parsedDefinition.getModule(moduleName);
            Option<Module> programParsingModuleOption = moduleOption.isDefined() ?
                    Option.apply(gen.getProgramsGrammar(moduleOption.get())) :
                    Option.empty();
            if (programParsingModuleOption.isDefined()) {
                kem.registerInternalHiddenWarning("Module " + programParsingModuleOption.get().name() + " has been automatically generated.");
            }
            return programParsingModuleOption;
        }
    }

    public Module languageParsingModule() { return languageParsingModule; }

    /**
     * Creates a parser for a module.
     * Will probably want to move the method out of this class here eventually.
     *
     * @return a function taking a String to be parsed, a Source, and returning the parsed string as K.
     */

    public BiFunction<String, Source, K> getParser(Module module, Sort programStartSymbol, KExceptionManager kem) {
        ParseInModule parseInModule = RuleGrammarGenerator.getCombinedGrammar(module, kompileOptions.strict());

        return (BiFunction<String, Source, K> & Serializable) (s, source) -> {
            Tuple2<Either<Set<ParseFailedException>, K>, Set<ParseFailedException>> res = parseInModule.parseString(s, programStartSymbol, source);
            kem.addAllKException(res._2().stream().map(e -> e.getKException()).collect(Collectors.toSet()));
            if (res._1().isLeft()) {
                throw res._1().left().get().iterator().next();
            }
            return new TreeNodesToKORE(Outer::parseSort, kompileOptions.strict()).down(res._1().right().get());
        };
    }

    public Module getExtensionModule(Module module) {
        return RuleGrammarGenerator.getCombinedGrammar(module, kompileOptions.strict()).getExtensionModule();
    }

    public Rule compilePatternIfAbsent(FileUtil files, KExceptionManager kem, String pattern, Source source) {
        return cachedcompiledPatterns.computeIfAbsent(pattern, p -> new Kompile(kompileOptions, files, kem).parseAndCompileRule(this, p, source,
                Optional.of(parsePatternIfAbsent(files, kem, pattern, source))));
    }

    public Rule parsePatternIfAbsent(FileUtil files, KExceptionManager kem, String pattern, Source source) {
        return cachedParsedPatterns.computeIfAbsent(pattern, p -> new Kompile(kompileOptions, files, kem).parseRule(this, p, source));
    }
}
