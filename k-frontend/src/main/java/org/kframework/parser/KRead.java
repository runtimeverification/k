// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.inner.ParseInModule;
import org.kframework.parser.inner.RuleGrammarGenerator;
import org.kframework.parser.inner.kernel.KSyntax2Bison;
import org.kframework.parser.inner.kernel.Scanner;
import org.kframework.parser.json.JsonParser;
import org.kframework.parser.kast.KastParser;
import org.kframework.utils.OS;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

public record KRead(
    KExceptionManager kem, FileUtil files, InputModes input, GlobalOptions globalOptions) {

  public String showTokens(
      Module mod, CompiledDefinition def, String stringToParse, Source source) {
    return def.showTokens(mod, files, stringToParse, source);
  }

  public K prettyRead(
      Module mod,
      Sort sort,
      String startSymbolLocation,
      CompiledDefinition def,
      Source source,
      String stringToParse,
      boolean partialParseDebug) {
    return prettyRead(
        mod, sort, startSymbolLocation, def, source, stringToParse, this.input, partialParseDebug);
  }

  public K prettyRead(
      Module mod,
      Sort sort,
      String startSymbolLocation,
      CompiledDefinition def,
      Source source,
      String stringToParse,
      InputModes inputMode,
      boolean partialParseDebug) {
    return switch (inputMode) {
      case JSON, KAST -> deserialize(stringToParse, inputMode, source);
      case KORE -> new KoreParser(mod.sortAttributesFor()).parseString(stringToParse);
      case PROGRAM -> def.parseSingleTerm(
          mod, sort, startSymbolLocation, kem, files, stringToParse, source, partialParseDebug);
      case RULE -> throw KEMException.internalError(
          "Should have been handled directly by the kast front end: " + inputMode);
    };
  }

  public void createBisonParser(
      Module mod,
      Sort sort,
      File outputFile,
      boolean glr,
      String bisonFile,
      long stackDepth,
      boolean library) {
    Stopwatch sw = new Stopwatch(globalOptions);
    try (ParseInModule parseInModule =
        RuleGrammarGenerator.getCombinedGrammar(mod, false, true, false, files)) {
      try (Scanner scanner = parseInModule.getScanner(kem.options)) {
        File scannerFile = files.resolveTemp("scanner.l");
        File scanHdr = files.resolveTemp("scanner.h");
        File parserFile = files.resolveTemp("parser.y");
        scanner.writeStandaloneScanner(scannerFile);
        KSyntax2Bison.writeParser(
            parseInModule.getParsingModule(),
            parseInModule.getDisambiguationModule(),
            scanner,
            sort,
            parserFile,
            glr,
            stackDepth,
            kem);
        int exit =
            files
                .getProcessBuilder()
                .directory(files.resolveTemp("."))
                .command(
                    "flex",
                    "--header-file=" + scanHdr.getAbsolutePath(),
                    "-w",
                    scannerFile.getAbsolutePath())
                .inheritIO()
                .start()
                .waitFor();
        if (exit != 0) {
          throw KEMException.internalError("flex returned nonzero exit code: " + exit + "\n");
        }
        exit =
            files
                .getProcessBuilder()
                .directory(files.resolveTemp("."))
                .command(
                    "bison",
                    "-d",
                    "-Wno-other",
                    "-Wno-conflicts-sr",
                    "-Wno-conflicts-rr",
                    parserFile.getAbsolutePath())
                .inheritIO()
                .start()
                .waitFor();
        if (exit != 0) {
          throw KEMException.internalError("bison returned nonzero exit code: " + exit + "\n");
        }
        List<String> command =
            new ArrayList<>(
                Arrays.asList(
                    Scanner.COMPILER,
                    "-DK_BISON_PARSER_SORT=" + sort.name(),
                    files.resolveKInclude("cparser/main.c").getAbsolutePath(),
                    files.resolveTemp("lex.yy.c").getAbsolutePath(),
                    files.resolveTemp("parser.tab.c").getAbsolutePath(),
                    "-iquote",
                    files.resolveTemp(".").getAbsolutePath(),
                    "-iquote",
                    files.resolveKInclude("cparser").getAbsolutePath(),
                    "-o",
                    outputFile.getAbsolutePath()));

        if (library) {
          command.addAll(OS.current().getSharedLibraryCompilerFlags());
        } else {
          command.add("-DK_BISON_PARSER_MAIN");
        }

        if (bisonFile != null) {
          command.add(files.resolveWorkingDirectory(bisonFile).getAbsolutePath());
        }
        exit =
            files
                .getProcessBuilder()
                .command(command.toArray(new String[0]))
                .inheritIO()
                .start()
                .waitFor();
        if (exit != 0) {
          throw KEMException.internalError(
              Scanner.COMPILER + " returned nonzero exit code: " + exit + "\n");
        }
      } catch (IOException | InterruptedException e) {
        throw KEMException.internalError("Failed to execute process.", e);
      }
    }
    sw.printIntermediate("  New Bison parser: " + mod.name());
  }

  public K deserialize(String stringToParse, Source source) {
    return deserialize(stringToParse, this.input, source);
  }

  public static K deserialize(String stringToParse, InputModes inputMode, Source source) {
    return switch (inputMode) {
      case JSON -> JsonParser.parse(stringToParse);
      case KAST -> KastParser.parse(stringToParse, source);
      default -> throw KEMException.criticalError(
          "Unsupported input mode for deserialization: " + inputMode);
    };
  }
}
