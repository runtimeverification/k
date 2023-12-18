// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kompile;

import com.google.inject.Inject;
import com.google.inject.Module;
import com.google.inject.Provider;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;
import org.kframework.compile.Backend;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.Usage;
import org.kframework.utils.options.InnerParsingOptions;
import org.kframework.utils.options.OuterParsingOptions;

public class KompileFrontEnd extends FrontEnd {

  public static List<Module> getModules() {
    List<Module> modules = new ArrayList<>();
    modules.add(new KompileModule());
    modules.add(new JCommanderModule());
    modules.add(new CommonModule());
    return modules;
  }

  private final KompileOptions options;
  private final OuterParsingOptions outerOptions;
  private final InnerParsingOptions innerOptions;
  private final Provider<Backend> koreBackend;
  private final Stopwatch sw;
  private final KExceptionManager kem;
  private final BinaryLoader loader;
  private final Provider<FileUtil> files;

  @Inject
  KompileFrontEnd(
      KompileOptions options,
      OuterParsingOptions outerOptions,
      InnerParsingOptions innerOptions,
      GlobalOptions globalOptions,
      @Usage String usage,
      Provider<Backend> koreBackend,
      Stopwatch sw,
      KExceptionManager kem,
      BinaryLoader loader,
      JarInfo jarInfo,
      Provider<FileUtil> files) {
    super(kem, globalOptions, usage, jarInfo, files);
    this.options = options;
    this.outerOptions = outerOptions;
    this.innerOptions = innerOptions;
    this.koreBackend = koreBackend;
    this.sw = sw;
    this.kem = kem;
    this.loader = loader;
    this.files = files;
  }

  @Override
  public int run() {
    if (!outerOptions.mainDefinitionFile(files.get()).exists()) {
      throw KEMException.criticalError(
          "Definition file doesn't exist: "
              + outerOptions.mainDefinitionFile(files.get()).getAbsolutePath());
    }

    Kompile kompile =
        new Kompile(
            options,
            outerOptions,
            innerOptions,
            globalOptions,
            files.get(),
            kem,
            sw,
            innerOptions.profileRules == null);
    Backend backend = koreBackend.get();
    CompiledDefinition def =
        kompile.run(
            outerOptions.mainDefinitionFile(files.get()),
            options.mainModule(files.get()),
            options.syntaxModule(files.get()),
            backend.steps(),
            backend.excludedModuleTags());
    kompile = null;
    files.get().saveToKompiled("mainModule.txt", def.executionModule().name());
    files.get().saveToKompiled("mainSyntaxModule.txt", def.mainSyntaxModuleName());
    try {
      URL rdmUrl = JarInfo.class.getResource("README.md");
      if (rdmUrl != null) {
        String rdm = FileUtil.read(new BufferedReader(new InputStreamReader(rdmUrl.openStream())));
        files.get().saveToKompiled("README.md", rdm);
      }
    } catch (IOException ignored) {
    }
    sw.printIntermediate("Kompile to kore");
    loader.saveOrDie(files.get().resolveKompiled("compiled.bin"), def);
    files.get().saveToKompiled("backend.txt", options.backend); // used by the krun script
    sw.printIntermediate("Save to disk");
    Backend.Holder h = new Backend.Holder(def);
    def = null;
    backend.accept(h);
    sw.printIntermediate("Backend");
    loader.saveOrDie(files.get().resolveKompiled("timestamp"), "");
    sw.printTotal("Total");
    return 0;
  }
}
