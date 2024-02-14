// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.unparser;

import com.beust.jcommander.Parameter;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import org.kframework.utils.options.BaseEnumConverter;
import org.kframework.utils.options.StringListConverter;

public class PrintOptions {

  public PrintOptions() {}

  public PrintOptions(OutputModes output) {
    this.output = output;
  }

  @Parameter(
      names = "--color",
      description = "Use colors in output. Default is on.",
      descriptionKey = "mode",
      converter = ColorModeConverter.class)
  private ColorSetting color;

  public ColorSetting color(boolean ttyStdout, Map<String, String> env) {
    boolean colorize = outputFile == null && ttyStdout;
    ColorSetting colors = color;
    if (colors == null) {
      try {
        if (!colorize) {
          colors = ColorSetting.OFF;
        } else if (Integer.parseInt(env.get("K_COLOR_SUPPORT")) >= 256) {
          colors = ColorSetting.EXTENDED;
        } else {
          colors = ColorSetting.ON;
        }
      } catch (NumberFormatException e) {
        colors = ColorSetting.ON;
      }
    }
    return colors;
  }

  public static class ColorModeConverter extends BaseEnumConverter<ColorSetting> {

    public ColorModeConverter(String optionName) {
      super(optionName);
    }

    @Override
    public Class<ColorSetting> enumClass() {
      return ColorSetting.class;
    }
  }

  @Parameter(
      names = "--output-file",
      description = "Store output in the file instead of displaying it.",
      descriptionKey = "file")
  public String outputFile;

  @Parameter(
      names = {"--output", "-o"},
      descriptionKey = "mode",
      converter = OutputModeConverter.class,
      description =
          "How to display krun results. <mode> is either"
              + " [pretty|program|kast|binary|json|kore|none].")
  public OutputModes output = OutputModes.PRETTY;

  public static class OutputModeConverter extends BaseEnumConverter<OutputModes> {

    public OutputModeConverter(String optionName) {
      super(optionName);
    }

    @Override
    public Class<OutputModes> enumClass() {
      return OutputModes.class;
    }
  }

  @Parameter(
      names = {"--output-omit"},
      descriptionKey = "KLabels",
      listConverter = StringListConverter.class,
      description = "KLabels to omit from the output.")
  public List<String> omittedKLabels = new ArrayList<String>();

  @Parameter(
      names = {"--output-tokenize"},
      descriptionKey = "KLabels",
      listConverter = StringListConverter.class,
      description = "KLabels to tokenize underneath (reducing output size).")
  public List<String> tokenizedKLabels = new ArrayList<String>();

  @Parameter(
      names = {"--output-flatten"},
      descriptionKey = "KLabels",
      listConverter = StringListConverter.class,
      description = "(Assoc) KLabels to flatten into one list.")
  public List<String> flattenedKLabels = new ArrayList<String>();

  @Parameter(
      names = {"--output-tokast"},
      descriptionKey = "KLabels",
      listConverter = StringListConverter.class,
      description = "KLabels to output as KAST tokens.")
  public List<String> tokastKLabels = new ArrayList<String>();

  @Parameter(
      names = {"--no-alpha-renaming"},
      listConverter = StringListConverter.class,
      description = "Do not alpha rename anonymous variables in output.")
  public boolean noAlphaRenaming = false;

  @Parameter(
      names = {"--no-substitution-filtering"},
      listConverter = StringListConverter.class,
      description = "Do not remove conjuncts of anonymous variables from substitution in output.")
  public boolean noFilterSubstitution = false;

  @Parameter(
      names = {"--no-sort-collections"},
      listConverter = StringListConverter.class,
      description = "Do not sort collections before printing (for speed).")
  public boolean noSortCollections = false;
}
