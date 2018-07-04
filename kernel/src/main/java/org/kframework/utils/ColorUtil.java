// Copyright (c) 2012-2018 K Team. All Rights Reserved.
package org.kframework.utils;

import org.kframework.unparser.ColorSetting;

import java.awt.Color;
import java.awt.color.ColorSpace;
import java.lang.reflect.Field;
import java.util.Collections;
import java.util.Map;
import java.util.HashMap;

public final class ColorUtil {

    private ColorUtil() {}

    private static Map<String, Color> colors;

    /**
     * Terminal code corresponding to closest color for this one, from the list of basic 8
     * terminal codes only.
     */
    private static Map<Color, String> ansiColorsToTerminalCodes;

    /**
     * Terminal code corresponding to closest color for this one, from the list of 216 colors supported by
     * linux terminals.
     */
    private static Map<Color, String> eightBitColorsToTerminalCodes;

    /**
     * A cache to avoid computing the closest terminal color for a given color each time it is needed.
     */
    private static Map<Map<Color, String>, Map<Color, String>> colorToCodeConvertCache;

    public static Map<String, Color> colors() {
        colors = doInitColors();
        return Collections.unmodifiableMap(colors);
    }

    static {
        colors = doInitColors();
        ansiColorsToTerminalCodes = initAnsiColors();
        eightBitColorsToTerminalCodes = initEightBitColors();
        colorToCodeConvertCache = initColorToCodeConvertCache();
    }

    private static HashMap<Map<Color, String>, Map<Color, String>> initColorToCodeConvertCache() {
        HashMap<Map<Color, String>, Map<Color, String>> map = new HashMap<>();
        map.put(ansiColorsToTerminalCodes, new HashMap<Color, String>());
        map.put(eightBitColorsToTerminalCodes, new HashMap<Color, String>());
        return map;
    }

    private static Map<String, Color> doInitColors() {
        Map<String, Color> colors = new HashMap<String, Color>();
        colors.put("black", Color.black);
        colors.put("blue", Color.blue);
        colors.put("brown", getColorByRgb("#C08040"));
        colors.put("cyan", Color.cyan);
        colors.put("darkgray", Color.darkGray);
        colors.put("gray", Color.gray);
        colors.put("green", Color.green);
        colors.put("lightgray", Color.lightGray);
        colors.put("lime", getColorByRgb("#C0FF00"));
        colors.put("magenta", Color.magenta);
        colors.put("olive", getColorByRgb("#808000"));
        colors.put("orange", Color.orange);
        colors.put("pink", Color.pink);
        colors.put("purple", getColorByRgb("#C00040"));
        colors.put("red", Color.red);
        colors.put("teal", getColorByRgb("#008080"));
        colors.put("violet", getColorByRgb("#800080"));
        colors.put("white", Color.white);
        colors.put("yellow", Color.yellow);
        colors.put("Apricot", getColorByRgb("#FBB982"));
        colors.put("Aquamarine", getColorByRgb("#00B5BE"));
        colors.put("Bittersweet", getColorByRgb("#C04F17"));
        colors.put("Black", getColorByRgb("#221E1F"));
        colors.put("Blue", getColorByRgb("#2D2F92"));
        colors.put("BlueGreen", getColorByRgb("#00B3B8"));
        colors.put("BlueViolet", getColorByRgb("#473992"));
        colors.put("BrickRed", getColorByRgb("#B6321C"));
        colors.put("Brown", getColorByRgb("#792500"));
        colors.put("BurntOrange", getColorByRgb("#F7921D"));
        colors.put("CadetBlue", getColorByRgb("#74729A"));
        colors.put("CarnationPink", getColorByRgb("#F282B4"));
        colors.put("Cerulean", getColorByRgb("#00A2E3"));
        colors.put("CornflowerBlue", getColorByRgb("#41B0E4"));
        colors.put("Cyan", getColorByRgb("#00AEEF"));
        colors.put("Dandelion", getColorByRgb("#FDBC42"));
        colors.put("DarkOrchid", getColorByRgb("#A4538A"));
        colors.put("Emerald", getColorByRgb("#00A99D"));
        colors.put("ForestGreen", getColorByRgb("#009B55"));
        colors.put("Fuchsia", getColorByRgb("#8C368C"));
        colors.put("Goldenrod", getColorByRgb("#FFDF42"));
        colors.put("Gray", getColorByRgb("#949698"));
        colors.put("Green", getColorByRgb("#00A64F"));
        colors.put("GreenYellow", getColorByRgb("#DFE674"));
        colors.put("JungleGreen", getColorByRgb("#00A99A"));
        colors.put("Lavender", getColorByRgb("#F49EC4"));
        colors.put("LimeGreen", getColorByRgb("#8DC73E"));
        colors.put("Magenta", getColorByRgb("#EC008C"));
        colors.put("Mahogany", getColorByRgb("#A9341F"));
        colors.put("Maroon", getColorByRgb("#AF3235"));
        colors.put("Melon", getColorByRgb("#F89E7B"));
        colors.put("MidnightBlue", getColorByRgb("#006795"));
        colors.put("Mulberry", getColorByRgb("#A93C93"));
        colors.put("NavyBlue", getColorByRgb("#006EB8"));
        colors.put("OliveGreen", getColorByRgb("#3C8031"));
        colors.put("Orange", getColorByRgb("#F58137"));
        colors.put("OrangeRed", getColorByRgb("#ED135A"));
        colors.put("Orchid", getColorByRgb("#AF72B0"));
        colors.put("Peach", getColorByRgb("#F7965A"));
        colors.put("Periwinkle", getColorByRgb("#7977B8"));
        colors.put("PineGreen", getColorByRgb("#008B72"));
        colors.put("Plum", getColorByRgb("#92268F"));
        colors.put("ProcessBlue", getColorByRgb("#00B0F0"));
        colors.put("Purple", getColorByRgb("#99479B"));
        colors.put("RawSienna", getColorByRgb("#974006"));
        colors.put("Red", getColorByRgb("#ED1B23"));
        colors.put("RedOrange", getColorByRgb("#F26035"));
        colors.put("RedViolet", getColorByRgb("#A1246B"));
        colors.put("Rhodamine", getColorByRgb("#EF559F"));
        colors.put("RoyalBlue", getColorByRgb("#0071BC"));
        colors.put("RoyalPurple", getColorByRgb("#613F99"));
        colors.put("RubineRed", getColorByRgb("#ED017D"));
        colors.put("Salmon", getColorByRgb("#F69289"));
        colors.put("SeaGreen", getColorByRgb("#3FBC9D"));
        colors.put("Sepia", getColorByRgb("#671800"));
        colors.put("SkyBlue", getColorByRgb("#46C5DD"));
        colors.put("SpringGreen", getColorByRgb("#C6DC67"));
        colors.put("Tan", getColorByRgb("#DA9D76"));
        colors.put("TealBlue", getColorByRgb("#00AEB3"));
        colors.put("Thistle", getColorByRgb("#D883B7"));
        colors.put("Turquoise", getColorByRgb("#00B4CE"));
        colors.put("Violet", getColorByRgb("#58429B"));
        colors.put("VioletRed", getColorByRgb("#EF58A0"));
        colors.put("White", getColorByRgb("#FFFFFF"));
        colors.put("WildStrawberry", getColorByRgb("#EE2967"));
        colors.put("Yellow", getColorByRgb("#FFF200"));
        colors.put("YellowGreen", getColorByRgb("#98CC70"));
        colors.put("YellowOrange", getColorByRgb("#FAA21A"));

        addSvgnamesColors(colors);

        return Collections.unmodifiableMap(colors);
    }

    private static void addSvgnamesColors(Map<String, Color> colors) {
        Object[][] svgColors = {
            {"AliceBlue", .94, .972, 1},
            {"AntiqueWhite", .98, .92, .844},
            {"Aqua", 0, 1, 1},
            {"Aquamarine", .498, 1, .83},
            {"Azure", .94, 1, 1},
            {"Beige", .96, .96, .864},
            {"Bisque", 1, .894, .77},
            {"Black", 0, 0, 0},
            {"BlanchedAlmond", 1, .92, .804},
            {"Blue", 0, 0, 1},
            {"BlueViolet", .54, .17, .888},
            {"Brown", .648, .165, .165},
            {"BurlyWood", .87, .72, .53},
            {"CadetBlue", .372, .62, .628},
            {"Chartreuse", .498, 1, 0},
            {"Chocolate", .824, .41, .116},
            {"Coral", 1, .498, .312},
            {"CornflowerBlue", .392, .585, .93},
            {"Cornsilk", 1, .972, .864},
            {"Crimson", .864, .08, .235},
            {"Cyan", 0, 1, 1},
            {"DarkBlue", 0, 0, .545},
            {"DarkCyan", 0, .545, .545},
            {"DarkGoldenrod", .72, .525, .044},
            {"DarkGray", .664, .664, .664},
            {"DarkGreen", 0, .392, 0},
            {"DarkGrey", .664, .664, .664},
            {"DarkKhaki", .74, .716, .42},
            {"DarkMagenta", .545, 0, .545},
            {"DarkOliveGreen", .332, .42, .185},
            {"DarkOrange", 1, .55, 0},
            {"DarkOrchid", .6, .196, .8},
            {"DarkRed", .545, 0, 0},
            {"DarkSalmon", .912, .59, .48},
            {"DarkSeaGreen", .56, .736, .56},
            {"DarkSlateBlue", .284, .24, .545},
            {"DarkSlateGray", .185, .31, .31},
            {"DarkSlateGrey", .185, .31, .31},
            {"DarkTurquoise", 0, .808, .82},
            {"DarkViolet", .58, 0, .828},
            {"DeepPink", 1, .08, .576},
            {"DeepSkyBlue", 0, .75, 1},
            {"DimGray", .41, .41, .41},
            {"DimGrey", .41, .41, .41},
            {"DodgerBlue", .116, .565, 1},
            {"FireBrick", .698, .132, .132},
            {"FloralWhite", 1, .98, .94},
            {"ForestGreen", .132, .545, .132},
            {"Fuchsia", 1, 0, 1},
            {"Gainsboro", .864, .864, .864},
            {"GhostWhite", .972, .972, 1},
            {"Gold", 1, .844, 0},
            {"Goldenrod", .855, .648, .125},
            {"Gray", .5, .5, .5},
            {"Green", 0, .5, 0},
            {"GreenYellow", .68, 1, .185},
            {"Grey", .5, .5, .5},
            {"Honeydew", .94, 1, .94},
            {"HotPink", 1, .41, .705},
            {"IndianRed", .804, .36, .36},
            {"Indigo", .294, 0, .51},
            {"Ivory", 1, 1, .94},
            {"Khaki", .94, .9, .55},
            {"Lavender", .9, .9, .98},
            {"LavenderBlush", 1, .94, .96},
            {"LawnGreen", .488, .99, 0},
            {"LemonChiffon", 1, .98, .804},
            {"LightBlue", .68, .848, .9},
            {"LightCoral", .94, .5, .5},
            {"LightCyan", .88, 1, 1},
            {"LightGoldenrod", .933, .867, .51},
            {"LightGoldenrodYellow", .98, .98, .824},
            {"LightGray", .828, .828, .828},
            {"LightGreen", .565, .932, .565},
            {"LightGrey", .828, .828, .828},
            {"LightPink", 1, .712, .756},
            {"LightSalmon", 1, .628, .48},
            {"LightSeaGreen", .125, .698, .668},
            {"LightSkyBlue", .53, .808, .98},
            {"LightSlateBlue", .518, .44, 1},
            {"LightSlateGray", .468, .532, .6},
            {"LightSlateGrey", .468, .532, .6},
            {"LightSteelBlue", .69, .77, .87},
            {"LightYellow", 1, 1, .88},
            {"Lime", 0, 1, 0},
            {"LimeGreen", .196, .804, .196},
            {"Linen", .98, .94, .9},
            {"Magenta", 1, 0, 1},
            {"Maroon", .5, 0, 0},
            {"MediumAquamarine", .4, .804, .668},
            {"MediumBlue", 0, 0, .804},
            {"MediumOrchid", .73, .332, .828},
            {"MediumPurple", .576, .44, .86},
            {"MediumSeaGreen", .235, .7, .444},
            {"MediumSlateBlue", .484, .408, .932},
            {"MediumSpringGreen", 0, .98, .604},
            {"MediumTurquoise", .284, .82, .8},
            {"MediumVioletRed", .78, .084, .52},
            {"MidnightBlue", .098, .098, .44},
            {"MintCream", .96, 1, .98},
            {"MistyRose", 1, .894, .884},
            {"Moccasin", 1, .894, .71},
            {"NavajoWhite", 1, .87, .68},
            {"Navy", 0, 0, .5},
            {"NavyBlue", 0, 0, .5},
            {"OldLace", .992, .96, .9},
            {"Olive", .5, .5, 0},
            {"OliveDrab", .42, .556, .136},
            {"Orange", 1, .648, 0},
            {"OrangeRed", 1, .27, 0},
            {"Orchid", .855, .44, .84},
            {"PaleGoldenrod", .932, .91, .668},
            {"PaleGreen", .596, .985, .596},
            {"PaleTurquoise", .688, .932, .932},
            {"PaleVioletRed", .86, .44, .576},
            {"PapayaWhip", 1, .936, .835},
            {"PeachPuff", 1, .855, .725},
            {"Peru", .804, .52, .248},
            {"Pink", 1, .752, .796},
            {"Plum", .868, .628, .868},
            {"PowderBlue", .69, .88, .9},
            {"Purple", .5, 0, .5},
            {"Red", 1, 0, 0},
            {"RosyBrown", .736, .56, .56},
            {"RoyalBlue", .255, .41, .884},
            {"SaddleBrown", .545, .27, .075},
            {"Salmon", .98, .5, .448},
            {"SandyBrown", .956, .644, .376},
            {"SeaGreen", .18, .545, .34},
            {"Seashell", 1, .96, .932},
            {"Sienna", .628, .32, .176},
            {"Silver", .752, .752, .752},
            {"SkyBlue", .53, .808, .92},
            {"SlateBlue", .415, .352, .804},
            {"SlateGray", .44, .5, .565},
            {"SlateGrey", .44, .5, .565},
            {"Snow", 1, .98, .98},
            {"SpringGreen", 0, 1, .498},
            {"SteelBlue", .275, .51, .705},
            {"Tan", .824, .705, .55},
            {"Teal", 0, .5, .5},
            {"Thistle", .848, .75, .848},
            {"Tomato", 1, .39, .28},
            {"Turquoise", .25, .88, .815},
            {"Violet", .932, .51, .932},
            {"VioletRed", .816, .125, .565},
            {"Wheat", .96, .87, .7},
            {"White", 1, 1, 1},
            {"WhiteSmoke", .96, .96, .96},
            {"Yellow", 1, 1, 0},
            {"YellowGreen", .604, .804, .196},
        };
        for (Object[] rawColor : svgColors) {
            colors.put((String) rawColor[0], new Color(toFloat(rawColor[1]), toFloat(rawColor[2]), toFloat(rawColor[3])));
        }
    }

    private static float toFloat(Object rawColor) {
        return rawColor instanceof Integer ? (float) (Integer) rawColor : (float) (double) rawColor;
    }

    private static Color getColorByRgb(String rgb) {
        int r = Integer.valueOf(rgb.substring(1, 3), 16);
        int g = Integer.valueOf(rgb.substring(3, 5), 16);
        int b = Integer.valueOf(rgb.substring(5, 7), 16);
        return new Color(r, g, b);
    }

    private static Map<Color, String> initAnsiColors() {
        Map<Color, String> map = new HashMap<Color, String>(8);
        map.put(Color.black, getBasicTerminalCode(30));
        map.put(Color.red, getBasicTerminalCode(31));
        map.put(Color.green, getBasicTerminalCode(32));
        map.put(Color.yellow, getBasicTerminalCode(33));
        map.put(Color.blue, getBasicTerminalCode(34));
        map.put(Color.magenta, getBasicTerminalCode(35));
        map.put(Color.cyan, getBasicTerminalCode(36));
        map.put(Color.white, getBasicTerminalCode(37));

        return Collections.unmodifiableMap(map);
    }

    /**
     * Basic colors codes have the form \e[&lt;code&gt;m . You can test them by running in your terminal:
     * echo -en "\e[35mTEST"
     */
    private static String getBasicTerminalCode(int code) {
        return "\u001b[" + code + "m";
    }

    private static Map<Color, String> initEightBitColors() {
        Map<Integer, Integer> coordMap = new HashMap<Integer, Integer>();
        coordMap.put(0,0);
        coordMap.put(1,95);
        coordMap.put(2,135);
        coordMap.put(3,175);
        coordMap.put(4,215);
        coordMap.put(5,255);

        Map<Color, String> map = new HashMap<Color, String>();
        for (int i = 0; i < 6; i++) {
            for (int j = 0; j < 6; j++) {
                for (int k = 0; k < 6; k++) {
                    int code = i *36 + j * 6 + k + 16;
                    Color color = new Color(coordMap.get(i),coordMap.get(j),coordMap.get(k));
                    map.put(color, getEightBitTerminalCode(code));
                }
            }
        }

        return Collections.unmodifiableMap(map);
    }

    /**
     * 8-bit format example: echo -en "\e[38;5;180mTEST"
     */
    private static String getEightBitTerminalCode(int code) {
        return "\u001b[38;5;" + code + "m";
    }

    public synchronized static String RgbToAnsi(String rgb, ColorSetting colorSetting) {
        switch(colorSetting) {
            case OFF:
                return "";
            case ON:
                return getClosestTerminalCode(colors.get(rgb), ansiColorsToTerminalCodes);
            case EXTENDED:
                return getClosestTerminalCode(colors.get(rgb), eightBitColorsToTerminalCodes);
            default:
                throw new UnsupportedOperationException("colorSettung: " + colorSetting);
        }
    }

    private static String getClosestTerminalCode(Color rgb, Map<Color, String> codesMap) {
        if (rgb == null)
            return "";
        if (colorToCodeConvertCache.get(codesMap).get(rgb) == null) {
            colorToCodeConvertCache.get(codesMap).put(rgb, getClosestTerminalCodeImpl(rgb, codesMap));
        }
        return colorToCodeConvertCache.get(codesMap).get(rgb);
    }

    private static String getClosestTerminalCodeImpl(Color rgb, Map<Color, String> codesMap) {
        double minColorError = Double.MAX_VALUE;
        Color minColor = null;
        for (Color ansi : codesMap.keySet()) {
            double colorError = getColorError(rgb, ansi);
            if (colorError < minColorError) {
                minColorError = colorError;
                minColor = ansi;
            }
        }
        return codesMap.get(minColor);
    }

    public static final String ANSI_NORMAL = "\u001b[0m";

    private static final double sl = 1.0;
    private static final double kc = 1.0;
    private static final double kh = 1.0;
    // graphic args
    private static final double kl = 1.0;
    private static final double k1 = 0.045;
    private static final double k2 = 0.015;

    public static final class CIELab extends ColorSpace {
        private static final ColorSpace CIEXYZ = ColorSpace.getInstance(ColorSpace.CS_CIEXYZ);

        private final double xn, yn, zn;

        CIELab() {
            super(ColorSpace.TYPE_Lab, 3);
            float[] ref = Color.white.getColorComponents(CIEXYZ, null);
            xn = ref[0];
            yn = ref[1];
            zn = ref[2];
        }

        @Override
        public float[] toRGB(float[] floats) {
            return CIEXYZ.toRGB(toCIEXYZ(floats));
        }

        @Override
        public float[] fromRGB(float[] floats) {
            return fromCIEXYZ(CIEXYZ.fromRGB(floats));
        }

        @Override
        public float[] toCIEXYZ(float[] floats) {
            double l = floats[0];
            double a = floats[1];
            double b = floats[2];
            double x = xn * finv((l + 16.0)/116.0 + a/500.0);
            double y = yn * finv((l + 16.0)/116.0);
            double z = zn * finv((l + 16.0)/116.0 - b/200.0);
            return new float[]{ (float)x, (float)y, (float)z };
        }

        @Override
        public float[] fromCIEXYZ(float[] floats) {
            double x = floats[0];
            double y = floats[1];
            double z = floats[2];
            double l = 116.0 * f(y/yn) - 16.0;
            double a = 500.0 * (f(x/xn) - f(y/yn));
            double b = 200.0 * (f(y/yn) - f(z/zn));
            return new float[]{ (float)l, (float)a, (float)b };
        }

        private static final double delta = 6.0/29.0;
        private static final double f0 = 4.0/29.0;

        private double f(double t) {
           if (t > delta*delta*delta) {
               return Math.cbrt(t);
           }
           return t/(3*delta*delta) + f0;
        }

        private double finv(double t) {
            if (t > delta) {
                return t*t*t;
            }
            return 3*delta*delta*(t - f0);
        }
    }

    // Computes the CIE94 color difference of two colors
    private static double getColorError(Color color1, Color color2) {
        float[] rgb1 = color1.getRGBColorComponents(null);
        float[] rgb2 = color2.getRGBColorComponents(null);

        ColorSpace labSpace = new CIELab();
        float[] lab1 = labSpace.fromRGB(rgb1);
        float[] lab2 = labSpace.fromRGB(rgb2);

        double deltaL = lab1[0] - lab2[0];
        double deltaA = lab1[1] - lab2[1];
        double deltaB = lab1[2] - lab2[2];

        double c1 = Math.sqrt(lab1[1]*lab1[1] + lab1[2]*lab1[2]);
        double c2 = Math.sqrt(lab2[1]*lab2[1] + lab2[2]*lab2[2]);
        double deltaC = c1 - c2;

        double deltaH = deltaA*deltaA + deltaB*deltaB - deltaC*deltaC;
        deltaH = deltaH < 0 ? 0 : Math.sqrt(deltaH);

        double sc = 1.0 + k1*c1;
        double sh = 1.0 + k2*c1;

        double l = deltaL/(kl*sl);
        double c = deltaC/(kc*sc);
        double h = deltaH/(kh*sh);
        double i = l*l + c*c + h*h;
        return i < 0 ? 0 : Math.sqrt(i);
    }

    public static Color getColorByName(String colorName) {
        try {
            // Find the field and value of colorName
            Field field = Class.forName("java.awt.Color").getField(colorName);
            return (Color)field.get(null);
        } catch (ClassNotFoundException | NoSuchFieldException | IllegalAccessException e) {
            return null;
        }
    }
}
