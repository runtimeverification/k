package org.kframework.utils;

import org.kframework.krun.ColorSetting;

import java.awt.Color;
import java.util.Collections;
import java.util.Map;
import java.util.HashMap;

public class ColorUtil {

	public final static Map<String, Color> colors = initColors();

    /**
     * Terminal code corresponding to closest color for this one, from the list of basic 8
     * terminal codes only.
     */
    private final static Map<Color, String> ansiColorsToTerminalCodes = initAnsiColors();

    /**
     * Terminal code corresponding to closest color for this one, from the list of 216 colors supported by
     * linux terminals.
     */
    private final static Map<Color, String> eightBitColorsToTerminalCodes = initEightBitColors();

    /**
     * A cache to avoid computing the closest terminal color for a given color each time it is needed.
     */
    private final static Map<Map<Color, String>, Map<Color, String>> colorToCodeConvertCache
        = initColorToCodeConvertCache();

    private static HashMap<Map<Color, String>, Map<Color, String>> initColorToCodeConvertCache() {
        HashMap<Map<Color, String>, Map<Color, String>> map = new HashMap<>();
        map.put(ansiColorsToTerminalCodes, new HashMap<Color, String>());
        map.put(eightBitColorsToTerminalCodes, new HashMap<Color, String>());
        return map;
    }

    private static Map<String, Color> initColors() {
        Map<String, Color> colors = new HashMap<String, Color>();
		colors.put("black", Color.black);
		colors.put("blue", Color.blue);
		colors.put("brown", getColor("#C08040"));
		colors.put("cyan", Color.cyan);
		colors.put("darkgray", Color.darkGray);
		colors.put("gray", Color.gray);
		colors.put("green", Color.green);
		colors.put("lightgray", Color.lightGray);
		colors.put("lime", getColor("#C0FF00"));
		colors.put("magenta", Color.magenta);
		colors.put("olive", getColor("#808000"));
		colors.put("orange", Color.orange);
		colors.put("pink", Color.pink);
		colors.put("purple", getColor("#C00040"));
		colors.put("red", Color.red);
		colors.put("teal", getColor("#008080"));
		colors.put("violet", getColor("#800080"));
		colors.put("white", Color.white);
		colors.put("yellow", Color.yellow);
		colors.put("Apricot", getColor("#FBB982"));
		colors.put("Aquamarine", getColor("#00B5BE"));
		colors.put("Bittersweet", getColor("#C04F17"));
		colors.put("Black", getColor("#221E1F"));
		colors.put("Blue", getColor("#2D2F92"));
		colors.put("BlueGreen", getColor("#00B3B8"));
		colors.put("BlueViolet", getColor("#473992"));
		colors.put("BrickRed", getColor("#B6321C"));
		colors.put("Brown", getColor("#792500"));
		colors.put("BurntOrange", getColor("#F7921D"));
		colors.put("CadetBlue", getColor("#74729A"));
		colors.put("CarnationPink", getColor("#F282B4"));
		colors.put("Cerulean", getColor("#00A2E3"));
		colors.put("CornflowerBlue", getColor("#41B0E4"));
		colors.put("Cyan", getColor("#00AEEF"));
		colors.put("Dandelion", getColor("#FDBC42"));
		colors.put("DarkOrchid", getColor("#A4538A"));
		colors.put("Emerald", getColor("#00A99D"));
		colors.put("ForestGreen", getColor("#009B55"));
		colors.put("Fuchsia", getColor("#8C368C"));
		colors.put("Goldenrod", getColor("#FFDF42"));
		colors.put("Gray", getColor("#949698"));
		colors.put("Green", getColor("#00A64F"));
		colors.put("GreenYellow", getColor("#DFE674"));
		colors.put("JungleGreen", getColor("#00A99A"));
		colors.put("Lavender", getColor("#F49EC4"));
		colors.put("LimeGreen", getColor("#8DC73E"));
		colors.put("Magenta", getColor("#EC008C"));
		colors.put("Mahogany", getColor("#A9341F"));
		colors.put("Maroon", getColor("#AF3235"));
		colors.put("Melon", getColor("#F89E7B"));
		colors.put("MidnightBlue", getColor("#006795"));
		colors.put("Mulberry", getColor("#A93C93"));
		colors.put("NavyBlue", getColor("#006EB8"));
		colors.put("OliveGreen", getColor("#3C8031"));
		colors.put("Orange", getColor("#F58137"));
		colors.put("OrangeRed", getColor("#ED135A"));
		colors.put("Orchid", getColor("#AF72B0"));
		colors.put("Peach", getColor("#F7965A"));
		colors.put("Periwinkle", getColor("#7977B8"));
		colors.put("PineGreen", getColor("#008B72"));
		colors.put("Plum", getColor("#92268F"));
		colors.put("ProcessBlue", getColor("#00B0F0"));
		colors.put("Purple", getColor("#99479B"));
		colors.put("RawSienna", getColor("#974006"));
		colors.put("Red", getColor("#ED1B23"));
		colors.put("RedOrange", getColor("#F26035"));
		colors.put("RedViolet", getColor("#A1246B"));
		colors.put("Rhodamine", getColor("#EF559F"));
		colors.put("RoyalBlue", getColor("#0071BC"));
		colors.put("RoyalPurple", getColor("#613F99"));
		colors.put("RubineRed", getColor("#ED017D"));
		colors.put("Salmon", getColor("#F69289"));
		colors.put("SeaGreen", getColor("#3FBC9D"));
		colors.put("Sepia", getColor("#671800"));
		colors.put("SkyBlue", getColor("#46C5DD"));
		colors.put("SpringGreen", getColor("#C6DC67"));
		colors.put("Tan", getColor("#DA9D76"));
		colors.put("TealBlue", getColor("#00AEB3"));
		colors.put("Thistle", getColor("#D883B7"));
		colors.put("Turquoise", getColor("#00B4CE"));
		colors.put("Violet", getColor("#58429B"));
		colors.put("VioletRed", getColor("#EF58A0"));
		colors.put("White", getColor("#FFFFFF"));
		colors.put("WildStrawberry", getColor("#EE2967"));
		colors.put("Yellow", getColor("#FFF200"));
		colors.put("YellowGreen", getColor("#98CC70"));
		colors.put("YellowOrange", getColor("#FAA21A"));

        return Collections.unmodifiableMap(colors);
	}

    public static Color getColor(String rgb) {
		int r = Integer.valueOf(rgb.substring(1, 3), 16);
		int g = Integer.valueOf(rgb.substring(3, 5), 16);
		int b = Integer.valueOf(rgb.substring(5, 7), 16);
		return new Color(r, g, b);
	}

    private static Map<Color, String> initAnsiColors() {
        Map<Color, String> map = new HashMap<Color, String>(8);
        //white and black may not be visible on all terminals, so we cheat and display them normally
        map.put(Color.white, getBasicTerminalCode(0));
        map.put(Color.black, getBasicTerminalCode(0));
        map.put(Color.red, getBasicTerminalCode(31));
        map.put(Color.green, getBasicTerminalCode(32));
        map.put(Color.blue, getBasicTerminalCode(34));
        map.put(Color.cyan, getBasicTerminalCode(36));
        map.put(Color.magenta, getBasicTerminalCode(35));
        map.put(Color.yellow, getBasicTerminalCode(33));

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

        //Ansi colors will have priority over 8-bit ones, including all the hacks.
        map.putAll(ansiColorsToTerminalCodes);

        return Collections.unmodifiableMap(map);
    }

    /**
     * 8-bit format example: echo -en "\e[38;5;180mTEST"
     */
    private static String getEightBitTerminalCode(int code) {
        return "\u001b[38;5;" + code + "m";
    }

    public static String RgbToAnsi(Color rgb, ColorSetting colorSetting) {
        switch(colorSetting) {
            case OFF:
                return "";
            case ON:
                return getClosestTerminalCode(rgb, ansiColorsToTerminalCodes);
            case EXTENDED:
                return getClosestTerminalCode(rgb, eightBitColorsToTerminalCodes);
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
        int minColorError = Integer.MAX_VALUE;
        Color minColor = null;
        for (Color ansi : codesMap.keySet()) {
            int colorError = getColorError(rgb, ansi);
            if (colorError < minColorError) {
                minColorError = colorError;
                minColor = ansi;
            }
        }
        return codesMap.get(minColor);
    }

    public static final String ANSI_NORMAL = "\u001b[0m";

	private static int getColorError(Color c1, Color c2) {
		int r = c1.getRed() - c2.getRed();
		int g = c1.getGreen() - c2.getGreen();
		int b = c1.getBlue() - c2.getBlue();

		return r*r + g*g + b*b;
	}
}
