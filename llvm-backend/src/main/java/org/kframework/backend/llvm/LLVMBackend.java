// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.backend.llvm;

import com.google.inject.Inject;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.apache.commons.io.FileUtils;
import org.apache.commons.lang3.mutable.MutableInt;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.backend.kore.KoreBackend;
import org.kframework.backend.llvm.matching.Matching;
import org.kframework.backend.llvm.matching.MatchingException;
import org.kframework.compile.Backend;
import org.kframework.kompile.KompileOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.parser.kore.parser.KoreToK;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.collection.Map;

public class LLVMBackend extends KoreBackend {

  private final GlobalOptions globalOptions;
  private final LLVMKompileOptions options;
  private final KExceptionManager kem;
  private final KompileOptions kompileOptions;

  @Inject
  public LLVMBackend(
      KompileOptions kompileOptions,
      GlobalOptions globalOptions,
      FileUtil files,
      KExceptionManager kem,
      LLVMKompileOptions options,
      Tool tool) {
    super(kompileOptions, files, kem, tool);
    this.globalOptions = globalOptions;
    this.options = options;
    this.kompileOptions = kompileOptions;
    this.kem = kem;
  }

  @Override
  public void accept(Backend.Holder h) {
    Stopwatch sw = new Stopwatch(globalOptions);
    String kore = getKompiledString(h.def, true);
    var hookAtts = h.def.kompiledDefinition.mainModule().hookAttributes();
    h.def = null;
    files.saveToKompiled("definition.kore", kore);
    sw.printIntermediate("  Print definition.kore");
    FileUtils.deleteQuietly(files.resolveKompiled("dt"));
    MutableInt warnings = new MutableInt();
    boolean optimize =
        kompileOptions.optimize1 || kompileOptions.optimize2 || kompileOptions.optimize3;
    Matching.writeDecisionTreeToFile(
        files.resolveKompiled("definition.kore"),
        options.heuristic,
        files.resolveKompiled("dt"),
        Matching.getThreshold(getThreshold()),
        !optimize,
        globalOptions.includesExceptionType(ExceptionType.USELESS_RULE),
        options.enableSearch,
        ex -> {
          var translated = translateError(ex, hookAtts);
          kem.addKException(translated);
          if (globalOptions.includesExceptionType(translated.getType())) {
            warnings.increment();
          }
          return null;
        });
    sw.printIntermediate("  Write decision tree");
    if (warnings.intValue() > 0 && kem.options.warnings2errors) {
      throw KEMException.compilerError("Had " + warnings.intValue() + " pattern matching errors.");
    }
    if (options.noLLVMKompile) {
      return;
    }
    if (options.enableSearch && options.llvmKompileOutput != null) {
      throw KEMException.criticalError("Can't use --llvm-kompile-output with --enable-search.");
    }
    if (options.llvmKompileType.equals("python") && options.llvmKompileOutput != null) {
      throw KEMException.criticalError(
          "Can't use --llvm-kompile-output with --llvm-kompile-type python");
    }
    String llvmType =
        switch (options.llvmKompileType) {
          case "main", "search", "static", "library", "python", "c" -> options.llvmKompileType;
          default -> throw KEMException.criticalError(
              "Non-valid argument for --llvm-kompile-type: "
                  + options.llvmKompileType
                  + ". Expected [main|search|library|static|python|c]");
        };

    String llvmOutput = "interpreter";
    if (options.llvmKompileOutput != null) {
      llvmOutput = options.llvmKompileOutput;
    }

    if (options.llvmKompileType.equals("python")) {
      llvmOutput = null;
    }

    llvmKompile(llvmType, llvmOutput);

    if (options.enableSearch) {
      llvmKompile("search", "search");
    }
  }

  private void llvmKompile(String type, String executable) {
    Stopwatch sw = new Stopwatch(globalOptions);
    ProcessBuilder pb = files.getProcessBuilder();
    List<String> args = new ArrayList<>();

    try {
      args.add("llvm-kompile");
      args.add(files.resolveKompiled("definition.kore").getCanonicalPath());
      args.add(files.resolveKompiled("dt").getCanonicalPath());
      args.add(type);

      if (options.enableProofHints || options.enableProofHintDebugging) {
        if (options.enableProofHintDebugging) {
          args.add("--proof-hint-instrumentation-slow");
        } else {
          args.add("--proof-hint-instrumentation");
        }
      }

      if (options.llvmMutableBytes) {
        args.add("--mutable-bytes");
      }

      // Arguments after this point are passed on to Clang.
      args.add("--");

      if (options.debug) {
        args.add("-g");
        args.add("-O1");
      }

      // For Python bindings, we explicitly leave this unset so that python3-config
      // can decide the proper filename.
      if (executable != null) {
        args.add("-o");

        File outputFile = new File(executable);
        if (!new File(executable).isAbsolute()) {
          outputFile = files.resolveKompiled(executable);
        }

        args.add(outputFile.getCanonicalPath());
      }

      if (!options.debug) {
        if (kompileOptions.optimize1) args.add("-O1");
        if (kompileOptions.optimize2) args.add("-O2");
        if (kompileOptions.optimize3)
          args.add("-O2"); // clang -O3 does not make the llvm backend any faster
      }

      args.addAll(options.ccopts);

      if (globalOptions.verbose) {
        System.out.println("  \u250cExecuting: " + String.join(" ", args));
      }

      Process p = pb.command(args).inheritIO().start();
      int exit = p.waitFor();
      if (exit != 0) {
        throw KEMException.criticalError(
            "llvm-kompile returned nonzero exit code: " + exit + "\nExamine output to see errors.");
      }
    } catch (IOException | InterruptedException e) {
      throw KEMException.criticalError("Error with I/O while executing llvm-kompile", e);
    }
    sw.printIntermediate("  \u2514" + executable + ": " + type);
  }

  private Optional<Source> getSource(MatchingException ex) {
    return ex.getSource().map(s -> new Source(s.getSource()));
  }

  private Optional<Location> getLocation(MatchingException ex) {
    return ex.getLocation()
        .map(
            l ->
                new Location(
                    l.getStartLine(), l.getEndLine(), l.getStartColumn(), l.getEndColumn()));
  }

  private String getCounterExampleMessage(MatchingException ex, Map<String, String> hookAtts) {
    return ex.getPattern()
        .map(
            p -> {
              var kast = new KoreToK(hookAtts).apply(p).toString();
              return ex.getMessage() + ": " + kast;
            })
        .orElse(ex.getMessage());
  }

  private KException translateError(MatchingException ex, Map<String, String> hookAtts) {
    switch (ex.getType()) {
      case USELESS_RULE -> {
        return new KException(
            ExceptionType.USELESS_RULE,
            KException.KExceptionGroup.COMPILER,
            ex.getMessage(),
            getSource(ex).orElse(null),
            getLocation(ex).orElse(null));
      }

      case NON_EXHAUSTIVE_MATCH -> {
        return new KException(
            ExceptionType.NON_EXHAUSTIVE_MATCH,
            KException.KExceptionGroup.COMPILER,
            getCounterExampleMessage(ex, hookAtts),
            getSource(ex).orElse(null),
            getLocation(ex).orElse(null));
      }

      case INTERNAL_ERROR -> throw KEMException.internalError(
          ex.getMessage(), ex, getLocation(ex), getSource(ex));

      case COMPILER_ERROR -> throw KEMException.compilerError(
          ex.getMessage(), ex, getLocation(ex), getSource(ex));
    }

    throw KEMException.criticalError("Unhandled pattern matching exception", ex);
  }

  private String getThreshold() {
    if (!options.iterated && !kompileOptions.optimize3) {
      return "0";
    }
    return options.iteratedThreshold;
  }

  @Override
  public Set<Att.Key> excludedModuleTags() {
    return new HashSet<>(Collections.singletonList(Att.SYMBOLIC()));
  }
}
