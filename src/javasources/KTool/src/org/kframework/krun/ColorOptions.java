package org.kframework.krun;

import java.awt.Color;

import org.kframework.utils.ColorUtil;
import org.kframework.utils.options.BaseEnumConverter;

import com.beust.jcommander.Parameter;

public class ColorOptions {

    @Parameter(names="--color", description="Use colors in output. Default is on.")
    private ColorSetting color;

    public ColorSetting color(boolean redirectStdout) {
        if (color == null) {
            if (redirectStdout) {
                return ColorSetting.OFF;
            }
            return ColorSetting.ON;
        }
        return color;
    }

    public static class ColorModeConverter extends BaseEnumConverter<ColorSetting> {

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