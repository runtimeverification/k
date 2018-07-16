// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.krun;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;
import org.kframework.unparser.OutputModes;
import org.kframework.krun.ColorSetting;
import org.kframework.utils.options.BaseEnumConverter;

import java.util.Map;

public class PrettyPrintOptions {

    public PrettyPrintOptions() {
    }

    //TODO(dwightguth): remove in Guice 4.0
    @Inject
    public PrettyPrintOptions(Void v) {
    }

    @Parameter(names = "--color", description = "Use colors in output. Default is on.", converter=ColorModeConverter.class)
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

    @Parameter(names="--output-file", description="Store output in the file instead of displaying it.")
    public String outputFile;

    @Parameter(names={"--output", "-o"}, converter=OutputModeConverter.class,
            description="How to display krun results. <mode> is either [pretty|program|kast|binary|none].")
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

}
