// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kompile;

import static org.kframework.kompile.Kompile.CACHE_FILE_NAME;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import com.google.inject.Inject;
import java.io.Serializable;
import java.util.Collections;
import java.util.List;
import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.Backends;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.InnerParsingOptions;
import org.kframework.utils.options.OuterParsingOptions;
import org.kframework.utils.options.OutputDirectoryOptions;
import org.kframework.utils.options.SMTOptions;
import org.kframework.utils.options.StringListConverter;

@RequestScoped
public class KompileOptions implements Serializable {
  public enum OptionType {
    DEFAULT,
    USER_PROVIDED
  }

  @Inject
  public KompileOptions() {}

  /**
   * WARNING: this field will be non-null in kompile tool, but null when KompileOption is
   * deserialized, as part of CompiledDefinition, in any other tool. usability depends on context.
   */
  @ParametersDelegate private final transient GlobalOptions global = new GlobalOptions();

  /**
   * Use only in the Guice Provider method, so it can be replaced by GlobalOptions from other tools.
   */
  GlobalOptions getGlobalOptions_UseOnlyInGuiceProvider() {
    return global;
  }

  @ParametersDelegate public OuterParsingOptions outerParsing = new OuterParsingOptions();

  @ParametersDelegate public transient InnerParsingOptions innerParsing = new InnerParsingOptions();

  @ParametersDelegate public OutputDirectoryOptions outputDirectory = new OutputDirectoryOptions();

  // Common options
  @Parameter(
      names = "--backend",
      description =
          "Choose a backend. <backend> is one of [llvm|haskell|kore]. Each creates the kompiled K"
              + " definition.",
      descriptionKey = "backend")
  public String backend = Backends.LLVM;

  @Parameter(
      names = "--main-module",
      descriptionKey = "name",
      description =
          "Specify main module in which a program starts to execute. This information is used by"
              + " 'krun'. The default is the name of the given K definition file without the"
              + " extension (.k).")
  private String mainModule;

  public record MainModule(String name, OptionType type) {}

  public MainModule mainModule(FileUtil files) {
    if (mainModule == null) {
      return new MainModule(
          FilenameUtils.getBaseName(outerParsing.mainDefinitionFile(files).getName()).toUpperCase(),
          OptionType.DEFAULT);
    }
    return new MainModule(mainModule, OptionType.USER_PROVIDED);
  }

  @Parameter(
      names = "--syntax-module",
      descriptionKey = "name",
      description =
          "Specify main module for syntax. This information is used by 'krun'. (Default:"
              + " <main-module>-SYNTAX).")
  private String syntaxModule;

  public record SyntaxModule(String name, OptionType type) {}

  public SyntaxModule syntaxModule(FileUtil files) {
    if (syntaxModule == null) {
      return new SyntaxModule(mainModule(files).name() + "-SYNTAX", OptionType.DEFAULT);
    }
    return new SyntaxModule(syntaxModule, OptionType.USER_PROVIDED);
  }

  @Parameter(names = "--coverage", description = "Generate coverage data when executing semantics.")
  public boolean coverage;

  @Parameter(
      names = "--hook-namespaces",
      listConverter = StringListConverter.class,
      description =
          "<string> is a whitespace-separated list of namespaces to include in the hooks defined in"
              + " the definition",
      descriptionKey = "string",
      hidden = true)
  public List<String> hookNamespaces = Collections.emptyList();

  @Parameter(
      names = "-O1",
      description =
          "Optimize in ways that improve performance and code size, but interfere with debugging"
              + " and increase compilation time slightly.")
  public boolean optimize1;

  @Parameter(
      names = "-O2",
      description =
          "Optimize further in ways that improve performance and code size, but interfere with"
              + " debugging more and increase compilation time somewhat.")
  public boolean optimize2;

  @Parameter(
      names = "-O3",
      description =
          "Optimize aggressively in ways that significantly improve performance, but interfere with"
              + " debugging significantly and also increase compilation time and code size"
              + " substantially.")
  public boolean optimize3;

  @Parameter(
      names = "-E",
      description =
          "Perform outer parsing and then stop and pretty print the definition to standard output."
              + " Useful for converting a K definition into a completely self-contained file when"
              + " reporting a bug.")
  public boolean preprocess;

  @Parameter(
      names = "--bison-lists",
      description =
          "Make List and NeList left associative. This is useful for creating Bison parsers that"
              + " use bounded stack space.",
      hidden = true)
  public boolean bisonLists;

  @ParametersDelegate public SMTOptions smt = new SMTOptions();

  @Parameter(
      names = "--cache-file",
      description =
          "Location of parse cache file. Default is $KOMPILED_DIR/" + CACHE_FILE_NAME + ".",
      hidden = true)
  public String cacheFile;

  @Parameter(
      names = "--emit-json",
      description = "Emit JSON serialized version of parsed and kompiled definitions.")
  public boolean emitJson = false;

  @Parameter(
      names = "--gen-bison-parser",
      description =
          "Emit bison parser for the PGM configuration variable within the syntax module of your"
              + " definition into the kompiled definition.")
  public boolean genBisonParser;

  @Parameter(
      names = "--gen-glr-bison-parser",
      description =
          "Emit GLR bison parser for the PGM configuration variable within the syntax module of"
              + " your definition into the kompiled definition.")
  public boolean genGlrBisonParser;

  @Parameter(
      names = "--bison-file",
      description = "C file containing functions to link into bison parser.",
      descriptionKey = "file",
      hidden = true)
  public String bisonFile;

  @Parameter(
      names = "--bison-stack-max-depth",
      description = "Maximum size of bison parsing stack.",
      descriptionKey = "size",
      hidden = true)
  public long bisonStackMaxDepth = 10000;

  @Parameter(
      names = "--bison-parser-library",
      description = "Generate a shared library rather than an executable for Bison parsers",
      hidden = true)
  public boolean genBisonParserLibrary;

  @Parameter(
      names = "--top-cell",
      description =
          "Choose the top configuration cell when more than one is provided. Does nothing if only"
              + " one top cell exists.")
  public String topCell;

  @Parameter(
      names = "--debug-type-inference",
      description =
          "Filename and source line of rule to debug type inference for. This is generally an"
              + " option used only by maintainers.",
      descriptionKey = "file",
      hidden = true)
  public String debugTypeInference;

  @Parameter(
      names = {"--post-process"},
      description = "JSON KAST => JSON KAST converter to run on definition after kompile pipeline.",
      descriptionKey = "command",
      hidden = true)
  public String postProcess;

  // TODO(dwightguth): remove this when it is no longer needed
  @Parameter(
      names = {"--disable-ceil-simplification-rules"},
      description =
          "Disable all rules with the simplification attribute whose left-hand side has a #Ceil at"
              + " the top.",
      hidden = true)
  public boolean disableCeilSimplificationRules;

  @Parameter(
      names = {"--allow-anywhere-haskell"},
      description = "Disable error message for anywhere rules on the Haskell backend.",
      hidden = true)
  public boolean allowAnywhereRulesHaskell;

  @Parameter(
      names = "--enable-kore-antileft",
      description = "Enable generation of legacy antileft priority predicates.",
      hidden = true)
  public boolean enableKoreAntileft;

  @Parameter(
      names = "--kore-backend-steps",
      description =
          "Specify a comma separated list of pipeline stages to apply to the definition after parsing",
      hidden = true)
  public String koreBackendSteps;

  @Parameter(
      names = "--outer-parsed-json",
      description =
          "Treat the definition file as an already outer parsed KAST definition in JSON format",
      hidden = true)
  public boolean outerParsedJson;
}
