// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.krun;

import java.awt.Color;

import org.kframework.utils.ColorUtil;
import org.kframework.utils.options.BaseEnumConverter;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;

public class ColorOptions {

    public ColorOptions() {}

    //TODO(dwightguth): remove in Guice 4.0
    @Inject
    public ColorOptions(Void v) {}

    @Parameter(names="--color", description="Use colors in output. Default is on.")
    private ColorSetting color;

    public ColorSetting color() {
        if (color == null) {
            return ColorSetting.ON;
        }
        return color;
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

    @Parameter(names="--terminal-color", description="Background color of the terminal. Cells won't be colored in this color.")
    private String terminalColor = "black";

    public Color terminalColor() {
        return ColorUtil.getColorByName(terminalColor);
    }
}
