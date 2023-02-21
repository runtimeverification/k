// Copyright (c) K Team. All Rights Reserved.
package org.kframework.parser.inner;

import com.google.common.collect.Sets;
import org.apache.commons.io.FileUtils;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.Term;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.inner.disambiguation.*;
import org.kframework.parser.inner.kernel.EarleyParser;
import org.kframework.parser.inner.kernel.Scanner;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;
import scala.Tuple3;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import java.io.File;
import java.io.IOException;
import java.io.Serializable;
import java.nio.charset.StandardCharsets;
import java.util.Collections;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.ConcurrentLinkedQueue;

/**
 * A wrapper that takes a module and one can call the parser
 * for that module in thread safe way.
 * Declarative disambiguation filters are also applied.
 */
public class ParseInModule implements Serializable, AutoCloseable {
    private final Module seedModule;
    private Module extensionModule;
    /**
     * The module in which parsing will be done.
     * Note that this module will be used for disambiguation, and the parsing module can be different.
     * This allows for grammar rewriting and more flexibility in the implementation.
     */
    private Module disambModule;
    /**
     * The exact module used for parsing. This can contain productions and sorts that are not
     * necessarily representable in KORE (sorts like Ne#Ids, to avoid name collisions).
     * In this case the modified production will be annotated with the information from the
     * original production, so disambiguation can be done safely.
     */
    private volatile Module parsingModule;
    private volatile EarleyParser parser = null;
    private final boolean strict;
    private final boolean profileRules;
    private final boolean isBison;
    private final boolean forGlobalScanner;
    private final FileUtil files;
    private final String typeInferenceDebug;

    ParseInModule(Module seedModule, boolean strict, boolean profileRules, boolean isBison, boolean forGlobalScanner, FileUtil files, String typeInferenceDebug) {
        this(seedModule, null, null, null, null, strict, profileRules, isBison, forGlobalScanner, files, typeInferenceDebug);
    }

    ParseInModule(Module seedModule, Scanner scanner, boolean strict, boolean profileRules, boolean isBison, boolean forGlobalScanner, FileUtil files, String typeInferenceDebug) {
        this(seedModule, null, null, null, scanner, strict, profileRules, isBison, forGlobalScanner, files, typeInferenceDebug);
    }

    private ParseInModule(Module seedModule, Module extensionModule, Module disambModule, Module parsingModule, Scanner scanner, boolean strict, boolean profileRules, boolean isBison, boolean forGlobalScanner, FileUtil files, String typeInferenceDebug) {
        this.seedModule = seedModule;
        this.extensionModule = extensionModule;
        this.disambModule = disambModule;
        this.parsingModule = parsingModule;
        this.scanner = scanner;
        this.strict = strict;
        this.profileRules = profileRules;
        this.isBison = isBison;
        this.forGlobalScanner = forGlobalScanner;
        this.files = files;
        this.typeInferenceDebug = typeInferenceDebug;
    }

    /**
     * The original module, which includes all the marker/flags imports.
     * This can be used to invalidate caches.
     * @return Module given by the user.
     */
    public Module seedModule() {
        return seedModule;
    }

    /**
     * An extension module of the seedModule which includes all productions, unmodified, and in addition,
     * contains extra productions auto-defined, like casts.
     * @return Module with extra productions defined during parser generator.
     */
    public Module getExtensionModule() {
        Module extM = extensionModule;
        if (extM == null) {
            Tuple3<Module, Module, Module> mods = RuleGrammarGenerator.getCombinedGrammarImpl(seedModule, isBison, forGlobalScanner);
            extM = mods._1();
            disambModule = mods._2();
            parsingModule = mods._3();
            extensionModule = extM;
        }
        return extM;
    }

    public Module getParsingModule() {
        Module parseM = parsingModule;
        if (parseM == null) {
            Tuple3<Module, Module, Module> mods = RuleGrammarGenerator.getCombinedGrammarImpl(seedModule, isBison, forGlobalScanner);
            extensionModule = mods._1();
            disambModule = mods._2();
            parseM = mods._3();
            parsingModule = parseM;
        }
        return parseM;
    }

    public Module getDisambiguationModule() {
        Module disambM = disambModule;
        if (disambM == null) {
            Tuple3<Module, Module, Module> mods = RuleGrammarGenerator.getCombinedGrammarImpl(seedModule, isBison, forGlobalScanner);
            extensionModule = mods._1();
            disambM = mods._2();
            parsingModule = mods._3();
            disambModule = disambM;
        }
        return disambM;
    }


    public void initialize() {
       Module m = getDisambiguationModule();
       m.definedSorts();
       m.subsorts();
       m.priorities();
       m.leftAssoc();
       m.rightAssoc();
       m.productionsFor();
       m.overloads();
    }

    /**
     * Parse as input the given string and start symbol using the module stored in the object.
     * @param input          the string to parse.
     * @param startSymbol    the start symbol from which to parse.
     * @return the Term representation of the parsed input.
     */
    public Tuple2<Either<Set<KEMException>, K>, Set<KEMException>>
            parseString(String input, Sort startSymbol, Source source) {
        try (Scanner scanner = getScanner()) {
            return parseString(input, startSymbol, "unit test", scanner, source, 1, 1, true, false);
        }
    }

    public Tuple2<Either<Set<KEMException>, K>, Set<KEMException>>
            parseString(String input, Sort startSymbol, String startSymbolLocation, Source source) {
        try (Scanner scanner = getScanner()) {
            return parseString(input, startSymbol, startSymbolLocation, scanner, source, 1, 1, true, false);
        }
    }
    private void getParser(Scanner scanner, Sort startSymbol) {
        EarleyParser p = parser;
        if (p == null) {
            Module m = getParsingModule();
            p = new EarleyParser(m, scanner, startSymbol);
            parser = p;
        }
    }

    private Scanner scanner;
    private final ThreadLocal<TypeInferencer> inferencer = new ThreadLocal<>();
    private final Queue<TypeInferencer> inferencers = new ConcurrentLinkedQueue<>();

    public Scanner getScanner(GlobalOptions go) {
        if (scanner == null) {
            scanner = new Scanner(this, go);
        }
        return scanner;
    }
    public Scanner getScanner() {
        if (scanner == null) {
            scanner = new Scanner(this);
        }
        return scanner;
    }
    public void setScanner(Scanner s) {
        scanner = s;
    }

    public Tuple2<Either<Set<KEMException>, K>, Set<KEMException>>
        parseString(String input, Sort startSymbol, String startSymbolLocation, Scanner scanner, Source source, int startLine, int startColumn, boolean inferSortChecks, boolean isAnywhere) {
        final Tuple2<Either<Set<KEMException>, Term>, Set<KEMException>> result
                = parseStringTerm(input, startSymbol, startSymbolLocation, scanner, source, startLine, startColumn, inferSortChecks, isAnywhere);
        Either<Set<KEMException>, K> parseInfo;
        if (result._1().isLeft()) {
            parseInfo = Left.apply(result._1().left().get());
        } else {
            parseInfo = Right.apply(new TreeNodesToKORE(Outer::parseSort, inferSortChecks && strict).apply(result._1().right().get()));
        }
        return new Tuple2<>(parseInfo, result._2());
    }

    /**
     * Parse the given input. This function is private because the final disambiguation
     * in {@link AmbFilter} eliminates ambiguities that will be equivalent only after
     * calling {@link TreeNodesToKORE#apply(Term)}, but returns a result that is
     * somewhat arbitrary as an actual parser {@link Term}.
     * Fortunately all callers want the result as a K, and can use the public
     * version of this method.
     * @param input
     * @param startSymbol
     * @param source
     * @param startLine
     * @param startColumn
     * @return
     */
    private Tuple2<Either<Set<KEMException>, Term>, Set<KEMException>>
            parseStringTerm(String input, Sort startSymbol, String startSymbolLocation, Scanner scanner, Source source, int startLine, int startColumn, boolean inferSortChecks, boolean isAnywhere) {
        if (!parsingModule.definedSorts().contains(startSymbol.head()))
            throw KEMException.innerParserError("Could not find start symbol: " + startSymbol + " provided to " + startSymbolLocation, source, Location.apply(startLine, startColumn, startLine, startColumn + 1));
        getParser(scanner, startSymbol);

        long start, endParse = 0, startTypeInf = 0, endTypeInf = 0;
        start = profileRules ? System.currentTimeMillis() : 0;

        try {
            Set<KEMException> warn = Sets.newHashSet();
            Term parsed;
            try {
                parsed = parser.parse(input, source, startLine, startColumn);
            } catch (KEMException e) {
                return Tuple2.apply(Left.apply(Collections.singleton(e)), Collections.emptySet());
            }
            endParse = profileRules ? System.currentTimeMillis() : 0;

            Term rez3 = new TreeCleanerVisitor().apply(parsed);
            Either<Set<KEMException>, Term> rez = new CollapseRecordProdsVisitor(rez3).apply(rez3);
            if (rez.isLeft())
                return new Tuple2<>(rez, warn);
            rez = new PriorityVisitor(disambModule.priorities(), disambModule.leftAssoc(), disambModule.rightAssoc()).apply(rez.right().get());
            if (rez.isLeft())
                return new Tuple2<>(rez, warn);
            rez = new KAppToTermConsVisitor(disambModule).apply(rez.right().get());
            if (rez.isLeft())
                return new Tuple2<>(rez, warn);
            rez3 = new PushAmbiguitiesDownAndPreferAvoid().apply(rez.right().get());
            rez3 = new PushTopAmbiguityUp().apply(rez3);
            startTypeInf = profileRules ? System.currentTimeMillis() : 0;

            TypeInferencer currentInferencer;
            if (isDebug(source, startLine)) {
                currentInferencer = new TypeInferencer(disambModule, true);
                inferencers.add(currentInferencer);
            } else {
                currentInferencer = inferencer.get();
                if (currentInferencer == null) {
                    currentInferencer = new TypeInferencer(disambModule, isDebug(source, startLine));
                    inferencer.set(currentInferencer);
                    inferencers.add(currentInferencer);
                }
            }

            rez = new TypeInferenceVisitor(currentInferencer, startSymbol, strict && inferSortChecks, true, isAnywhere).apply(rez3);
            if (rez.isLeft())
                return new Tuple2<>(rez, warn);
            endTypeInf = profileRules ? System.currentTimeMillis() : 0;

            rez = new ResolveOverloadedTerminators(disambModule.overloads()).apply(rez.right().get());
            if (rez.isLeft())
                return new Tuple2<>(rez, warn);
            rez3 = new PushAmbiguitiesDownAndPreferAvoid(disambModule.overloads()).apply(rez.right().get());
            rez = new AmbFilterError(strict && inferSortChecks).apply(rez3);
            if (rez.isLeft())
                return new Tuple2<>(rez, warn);
            Tuple2<Either<Set<KEMException>, Term>, Set<KEMException>> rez2 = new AddEmptyLists(disambModule, startSymbol).apply(rez.right().get());
            warn = Sets.union(rez2._2(), warn);
            if (rez2._1().isLeft())
                return rez2;
            rez3 = new RemoveBracketVisitor().apply(rez2._1().right().get());

            return new Tuple2<>(Right.apply(rez3), warn);
        } finally {
            if (profileRules) {
                try {
                    long stop = System.currentTimeMillis();
                    long totalTime = stop - start;
                    long parseTime = endParse - start;
                    long tiTime = endTypeInf - startTypeInf;
                    File f = File.createTempFile("timing", ".log", files.resolveTemp(""));
                    FileUtils.writeStringToFile(f, String.format("%s:%d\n%5d %s:%d   parse:%4d typeInf:%4d",
                            source.source(), startLine, totalTime, source.source(), startLine, parseTime, tiTime), StandardCharsets.UTF_8);
                } catch (IOException e) {
                  throw KEMException.internalError("Could not write to timing.log", e);
                }
            }
        }
    }

    private boolean isDebug(Source source, int startLine) {
        if (typeInferenceDebug == null) {
            return false;
        }
        return (source.source() + ":" + startLine).endsWith(typeInferenceDebug);
    }

    public void close() {
        if (scanner != null) {
            scanner.close();
        }
        for (TypeInferencer inferencer : inferencers) {
            inferencer.close();
        }
        inferencers.clear();
    }

    public static Term disambiguateForUnparse(Module mod, Term ambiguity) {
        Term rez3 = new PushTopAmbiguityUp().apply(ambiguity);
        Either<Set<KEMException>, Term> rez;
        Tuple2<Either<Set<KEMException>, Term>, Set<KEMException>> rez2;
        try (TypeInferencer inferencer = new TypeInferencer(mod, false)) {
            rez = new TypeInferenceVisitor(inferencer, Sorts.K(), false, false, false).apply(rez3);
        }
        if (rez.isLeft()) {
            rez2 = new AmbFilter(false).apply(rez3);
            return rez2._1().right().get();
        }
        rez3 = new PushAmbiguitiesDownAndPreferAvoid(mod.overloads()).apply(rez.right().get());
        rez2 = new AmbFilter(false).apply(rez3);
        return rez2._1().right().get();
    }
}
