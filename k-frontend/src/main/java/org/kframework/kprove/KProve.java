// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kprove;

import static org.kframework.Collections.*;

import com.google.inject.Inject;
import java.nio.charset.StandardCharsets;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import org.kframework.RewriterResult;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.rewriter.Rewriter;
import org.kframework.unparser.KPrint;
import org.kframework.unparser.ToJson;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;

public record KProve(
    KExceptionManager kem,
    FileUtil files,
    KPrint kprint,
    KProveOptions kproveOptions,
    CompiledDefinition compiledDefinition,
    ProofDefinitionBuilder proofDefinitionBuilder,
    Function<Definition, Rewriter> rewriterGenerator,
    Stopwatch sw) {
  private static final int KPROVE_SUCCESS_EXIT_CODE = 0;
  private static final int KPROVE_MISMATCH_CONFIG_CODE = 1;

  @Inject
  public KProve {}

  public int run() {
    if (!kproveOptions.specFile(files).exists()) {
      throw KEMException.criticalError(
          "Definition file doesn't exist: " + kproveOptions.specFile(files).getAbsolutePath());
    }

    Tuple2<Definition, Module> compiled =
        proofDefinitionBuilder.build(kproveOptions.specFile(files), kproveOptions.specModule);

    Rewriter rewriter = rewriterGenerator.apply(compiled._1());
    Module specModule = compiled._2();

    if (kproveOptions.emitJson) {
      files.saveToKompiled(
          "prove-definition.json", new String(ToJson.apply(compiled._1()), StandardCharsets.UTF_8));
    }

    if (kproveOptions.emitJsonSpec != null) {
      Set<String> names =
          stream(compiled._1().modules()).map(Module::name).collect(Collectors.toSet());
      Set<Module> specMods =
          stream(specModule.importedModules())
              .filter(m -> !names.contains(m.name()))
              .collect(Collectors.toSet());
      specMods.add(specModule);
      files.saveToWorkingDirectory(
          kproveOptions.emitJsonSpec, ToJson.apply(specMods, specModule.name()));
    }

    RewriterResult results = rewriter.prove(specModule, true);
    sw.printIntermediate("Backend");
    kprint.prettyPrint(
        compiled._1(),
        compiled._1().getModule("LANGUAGE-PARSING").get(),
        kprint::outputFile,
        results.k());
    sw.printTotal("Total");

    int errCode = results.exitCode().orElse(0);
    switch (errCode) {
      case KPROVE_SUCCESS_EXIT_CODE -> {}
      case KPROVE_MISMATCH_CONFIG_CODE -> {
        kem.addKException(
            new KException(
                KException.ExceptionType.ERROR,
                KException.KExceptionGroup.PROVER,
                "backend terminated because the configuration cannot be rewritten further. See"
                    + " output for more details."));
      }
      default -> {
        kem.addKException(
            new KException(
                KException.ExceptionType.ERROR,
                KException.KExceptionGroup.PROVER,
                "backend crashed with exit code " + errCode));
      }
    }

    return results.exitCode().orElse(KEMException.TERMINATED_WITH_ERRORS_EXIT_CODE);
  }
}
