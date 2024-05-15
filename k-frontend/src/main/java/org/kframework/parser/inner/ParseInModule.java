// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner;

import com.google.common.collect.Sets;
import java.io.File;
import java.io.IOException;
import java.io.Serializable;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.stream.Collectors;
import org.apache.commons.io.FileUtils;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.definition.Terminal;
import org.kframework.definition.TerminalLike;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.Term;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.inner.disambiguation.*;
import org.kframework.parser.inner.disambiguation.inference.SortInferencer;
import org.kframework.parser.inner.kernel.EarleyParser;
import org.kframework.parser.inner.kernel.Scanner;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.InnerParsingOptions;
import scala.Tuple2;
import scala.Tuple3;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

/**
 * A wrapper that takes a module and one can call the parser for that module in thread safe way.
 * Declarative disambiguation filters are also applied.
 */
public class ParseInModule implements Serializable, AutoCloseable {
  private final Module seedModule;

  private Module extensionModule;

  /**
   * The module in which parsing will be done. Note that this module will be used for
   * disambiguation, and the parsing module can be different. This allows for grammar rewriting and
   * more flexibility in the implementation.
   */
  private Module disambModule;

  /**
   * The exact module used for parsing. This can contain productions and sorts that are not
   * necessarily representable in KORE (sorts like Ne#Ids, to avoid name collisions). In this case
   * the modified production will be annotated with the information from the original production, so
   * disambiguation can be done safely.
   */
  private volatile Module parsingModule;

  private volatile EarleyParser parser = null;
  private final boolean profileRules;
  private final boolean isBison;
  private final boolean forGlobalScanner;
  private final FileUtil files;
  private final String typeInferenceDebug;
  private final InnerParsingOptions.TypeInferenceMode typeInferenceMode;
  private final boolean partialParseDebug;

  ParseInModule(
      Module seedModule,
      boolean profileRules,
      boolean isBison,
      boolean forGlobalScanner,
      FileUtil files,
      String typeInferenceDebug,
      InnerParsingOptions.TypeInferenceMode typeInferenceMode,
      boolean partialParseDebug) {
    this(
        seedModule,
        null,
        null,
        null,
        null,
        profileRules,
        isBison,
        forGlobalScanner,
        files,
        typeInferenceDebug,
        typeInferenceMode,
        partialParseDebug);
  }

  ParseInModule(
      Module seedModule,
      Scanner scanner,
      boolean profileRules,
      boolean isBison,
      boolean forGlobalScanner,
      FileUtil files,
      String typeInferenceDebug,
      InnerParsingOptions.TypeInferenceMode typeInferenceMode,
      boolean partialParseDebug) {
    this(
        seedModule,
        null,
        null,
        null,
        scanner,
        profileRules,
        isBison,
        forGlobalScanner,
        files,
        typeInferenceDebug,
        typeInferenceMode,
        partialParseDebug);
  }

  private ParseInModule(
      Module seedModule,
      Module extensionModule,
      Module disambModule,
      Module parsingModule,
      Scanner scanner,
      boolean profileRules,
      boolean isBison,
      boolean forGlobalScanner,
      FileUtil files,
      String typeInferenceDebug,
      InnerParsingOptions.TypeInferenceMode typeInferenceMode,
      boolean partialParseDebug) {
    this.seedModule = seedModule;
    this.extensionModule = extensionModule;
    this.disambModule = disambModule;
    this.parsingModule = parsingModule;
    this.scanner = scanner;
    this.profileRules = profileRules;
    this.isBison = isBison;
    this.forGlobalScanner = forGlobalScanner;
    this.files = files;
    this.typeInferenceDebug = typeInferenceDebug;
    this.typeInferenceMode =
        typeInferenceMode == InnerParsingOptions.TypeInferenceMode.DEFAULT
            ? InnerParsingOptions.TypeInferenceMode.SIMPLESUB
            : typeInferenceMode;
    this.partialParseDebug = partialParseDebug;
  }

  /**
   * The original module, which includes all the marker/flags imports. This can be used to
   * invalidate caches.
   *
   * @return Module given by the user.
   */
  public Module seedModule() {
    return seedModule;
  }

  /**
   * An extension module of the seedModule which includes all productions, unmodified, and in
   * addition, contains extra productions auto-defined, like casts.
   *
   * @return Module with extra productions defined during parser generator.
   */
  public Module getExtensionModule() {
    Module extM = extensionModule;
    if (extM == null) {
      Tuple3<Module, Module, Module> mods =
          RuleGrammarGenerator.getCombinedGrammarImpl(seedModule, isBison, forGlobalScanner, false);
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
      Tuple3<Module, Module, Module> mods =
          RuleGrammarGenerator.getCombinedGrammarImpl(seedModule, isBison, forGlobalScanner, false);
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
      Tuple3<Module, Module, Module> mods =
          RuleGrammarGenerator.getCombinedGrammarImpl(seedModule, isBison, forGlobalScanner, false);
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
   *
   * @param input the string to parse.
   * @param startSymbol the start symbol from which to parse.
   * @return the Term representation of the parsed input.
   */
  public Tuple2<Either<Set<KEMException>, K>, Set<KEMException>> parseString(
      String input, Sort startSymbol, Source source) {
    try (Scanner scanner = getScanner()) {
      return parseString(input, startSymbol, "unit test", scanner, source, 1, 1, false);
    }
  }

  /**
   * Print the list of tokens matched by the scanner, the location and the Regex Terminal The output
   * is a valid Markdown table.
   */
  public String tokenizeString(String input, Source source) {
    StringBuilder sb = new StringBuilder();
    try (Scanner scanner = getScanner()) {
      EarleyParser.ParserMetadata mdata =
          new EarleyParser.ParserMetadata(input, scanner, source, 1, 1);
      Map<Integer, TerminalLike> kind2Token =
          scanner.getTokens().entrySet().stream()
              .map(a -> new Tuple2<>(a.getValue()._1, a.getKey()))
              .collect(Collectors.toMap(Tuple2::_1, Tuple2::_2));
      List<Integer> lines = mdata.getLines();
      List<Integer> columns = mdata.getColumns();
      int maxTokenLen = 7, maxLocLen = 10, maxTerminalLen = 10;
      List<String> locs = new ArrayList<>();
      List<String> tokens = new ArrayList<>();
      List<String> terminals = new ArrayList<>();
      List<Scanner.Token> words = mdata.getWords();
      for (Scanner.Token word : mdata.getWords()) {
        String loc =
            String.format(
                "(%d,%d,%d,%d)",
                lines.get(word.startLoc),
                columns.get(word.startLoc),
                lines.get(word.endLoc),
                columns.get(word.endLoc));
        locs.add(loc);
        maxLocLen = Math.max(maxLocLen, loc.length());
        String tok = StringUtil.enquoteKString(word.value);
        tokens.add(tok);
        maxTokenLen = Math.max(maxTokenLen, tok.length());
        String terminal = kind2Token.getOrDefault(word.kind, Terminal.apply("<eof>")).toString();
        terminals.add(terminal);
        maxTerminalLen = Math.max(maxTerminalLen, terminal.length());
      }
      // if the token is absurdly large limit the column to 80 chars to maintain alignment
      maxTokenLen = Math.min(maxTokenLen, 80);
      maxTerminalLen = Math.min(maxTerminalLen, 20);
      sb.append(
          String.format(
              "|%-" + maxTokenLen + "s | %-" + maxLocLen + "s | %-" + maxTerminalLen + "s|\n",
              "\"Match\"",
              "(location)",
              "Terminal"));
      sb.append(
          String.format(
              "|-%s|--%s|-%s|\n",
              "-".repeat(maxTokenLen), "-".repeat(maxLocLen), "-".repeat(maxTerminalLen)));
      for (int i = 0; i < words.size(); i++) {
        sb.append(
            String.format(
                "|%-" + maxTokenLen + "s | %-" + maxLocLen + "s | %-" + maxTerminalLen + "s|\n",
                tokens.get(i),
                locs.get(i),
                terminals.get(i)));
      }
    }
    return sb.toString();
  }

  public Tuple2<Either<Set<KEMException>, K>, Set<KEMException>> parseString(
      String input, Sort startSymbol, String startSymbolLocation, Source source) {
    try (Scanner scanner = getScanner()) {
      return parseString(input, startSymbol, startSymbolLocation, scanner, source, 1, 1, false);
    }
  }

  private void getParser(Scanner scanner, Sort startSymbol) {
    EarleyParser p = parser;
    if (p == null) {
      Module m = getParsingModule();
      p = new EarleyParser(m, scanner, startSymbol, partialParseDebug);
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

  public Tuple2<Either<Set<KEMException>, K>, Set<KEMException>> parseString(
      String input,
      Sort startSymbol,
      String startSymbolLocation,
      Scanner scanner,
      Source source,
      int startLine,
      int startColumn,
      boolean isAnywhere) {
    final Tuple2<Either<Set<KEMException>, Term>, Set<KEMException>> result =
        parseStringTerm(
            input,
            startSymbol,
            startSymbolLocation,
            scanner,
            source,
            startLine,
            startColumn,
            isAnywhere);
    Either<Set<KEMException>, K> parseInfo;
    if (result._1().isLeft()) {
      parseInfo = Left.apply(result._1().left().get());
    } else {
      parseInfo =
          Right.apply(new TreeNodesToKORE(Outer::parseSort).apply(result._1().right().get()));
    }
    return new Tuple2<>(parseInfo, result._2());
  }

  /**
   * Parse the given input. This function is private because the final disambiguation in {@link
   * AmbFilterError} eliminates ambiguities that will be equivalent only after calling {@link
   * TreeNodesToKORE#apply(Term)}, but returns a result that is somewhat arbitrary as an actual
   * parser {@link Term}. Fortunately all callers want the result as a K, and can use the public
   * version of this method.
   *
   * @param input
   * @param startSymbol
   * @param source
   * @param startLine
   * @param startColumn
   * @return
   */
  private Tuple2<Either<Set<KEMException>, Term>, Set<KEMException>> parseStringTerm(
      String input,
      Sort startSymbol,
      String startSymbolLocation,
      Scanner scanner,
      Source source,
      int startLine,
      int startColumn,
      boolean isAnywhere) {
    if (!parsingModule.definedSorts().contains(startSymbol.head()))
      throw KEMException.innerParserError(
          "Could not find start symbol: " + startSymbol + " provided to " + startSymbolLocation,
          source,
          Location.apply(startLine, startColumn, startLine, startColumn + 1));
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
      if (rez.isLeft()) return new Tuple2<>(rez, warn);
      rez =
          new PriorityVisitor(
                  disambModule.priorities(), disambModule.leftAssoc(), disambModule.rightAssoc())
              .apply(rez.right().get());
      if (rez.isLeft()) return new Tuple2<>(rez, warn);
      rez = new KAppToTermConsVisitor(disambModule).apply(rez.right().get());
      if (rez.isLeft()) return new Tuple2<>(rez, warn);
      rez3 = new PushAmbiguitiesDownAndPreferAvoid().apply(rez.right().get());
      rez3 = new PushTopLHSAmbiguityUp().apply(rez3);
      startTypeInf = profileRules ? System.currentTimeMillis() : 0;

      InnerParsingOptions.TypeInferenceMode infModeForTerm =
          SortInferencer.isSupported(rez3)
              ? typeInferenceMode
              : InnerParsingOptions.TypeInferenceMode.Z3;

      if (infModeForTerm == InnerParsingOptions.TypeInferenceMode.SIMPLESUB
          || infModeForTerm == InnerParsingOptions.TypeInferenceMode.CHECKED) {
        rez = new SortInferencer(disambModule).apply(rez3, startSymbol, isAnywhere);
      }
      if (infModeForTerm == InnerParsingOptions.TypeInferenceMode.Z3
          || infModeForTerm == InnerParsingOptions.TypeInferenceMode.CHECKED) {

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
        Either<Set<KEMException>, Term> z3Rez =
            new TypeInferenceVisitor(currentInferencer, startSymbol, isAnywhere).apply(rez3);
        if (infModeForTerm == InnerParsingOptions.TypeInferenceMode.CHECKED) {
          boolean bothLeft = rez.isLeft() && z3Rez.isLeft();
          boolean equalRight =
              rez.isRight() && z3Rez.isRight() && rez.right().get().equals(z3Rez.right().get());
          if (!(bothLeft || equalRight)) {
            throw typeInferenceCheckError(rez3, z3Rez, rez);
          }
        } else {
          rez = z3Rez;
        }
      }

      if (rez.isLeft()) return new Tuple2<>(rez, warn);
      endTypeInf = profileRules ? System.currentTimeMillis() : 0;

      rez = new ResolveOverloadedTerminators(disambModule.overloads()).apply(rez.right().get());
      if (rez.isLeft()) return new Tuple2<>(rez, warn);
      rez3 =
          new PushAmbiguitiesDownAndPreferAvoid(disambModule.overloads()).apply(rez.right().get());
      rez = new AmbFilterError().apply(rez3);
      if (rez.isLeft()) return new Tuple2<>(rez, warn);
      Tuple2<Either<Set<KEMException>, Term>, Set<KEMException>> rez2 =
          new AddEmptyLists(disambModule, startSymbol).apply(rez.right().get());
      warn = Sets.union(rez2._2(), warn);
      if (rez2._1().isLeft()) return rez2;
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
          FileUtils.writeStringToFile(
              f,
              String.format(
                  "%s:%d\n%5d %s:%d   parse:%4d typeInf:%4d",
                  source.source(),
                  startLine,
                  totalTime,
                  source.source(),
                  startLine,
                  parseTime,
                  tiTime),
              StandardCharsets.UTF_8);
        } catch (IOException e) {
          throw KEMException.internalError("Could not write to timing.log", e);
        }
      }
    }
  }

  private static KEMException typeInferenceCheckError(
      Term term, Either<Set<KEMException>, Term> z3, Either<Set<KEMException>, Term> simple) {
    StringBuilder msg = new StringBuilder("Z3 and SimpleSub sort inference algorithms differ!\n");
    msg.append(term.source().isPresent() ? term.source().get().toString() : "").append("\n");
    msg.append(term.location().isPresent() ? term.location().get().toString() : "").append("\n");
    msg.append("\nZ3:\n");
    if (z3.isLeft()) {
      msg.append(
          z3.left().get().stream().map(KEMException::getMessage).collect(Collectors.joining("\n")));
    } else {
      msg.append(z3.right().get());
    }
    msg.append("\n");
    msg.append("\nSimpleSub:\n");
    if (simple.isLeft()) {
      msg.append(
          simple.left().get().stream()
              .map(KEMException::getMessage)
              .collect(Collectors.joining("\n")));
    } else {
      msg.append(simple.right().get());
    }
    msg.append("\n");
    return KEMException.criticalError(msg.toString());
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
}
