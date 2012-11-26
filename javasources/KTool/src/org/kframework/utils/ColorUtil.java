package org.kframework.utils;

import java.awt.Color;
import java.util.Map;
import java.util.HashMap;

public class ColorUtil {

	public static Map<String, Color> colors;
	public static Map<Color, String> ansiColors;
	static {
		colors = new HashMap<String, Color>();
		ansiColors = new HashMap<Color, String>();
		//white and black may not be visible on all terminals, so we cheat and display them normally
		ansiColors.put(Color.white, "0");
		ansiColors.put(Color.black, "0");
		ansiColors.put(Color.red, "31");
		ansiColors.put(Color.green, "32");
		ansiColors.put(Color.blue, "34");
		ansiColors.put(Color.cyan, "36");
		ansiColors.put(Color.magenta, "35");
		ansiColors.put(Color.yellow, "33");
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
	}

	public static Color getColor(String rgb) {
		int r = Integer.valueOf(rgb.substring(1, 3), 16);
		int g = Integer.valueOf(rgb.substring(3, 5), 16);
		int b = Integer.valueOf(rgb.substring(5, 7), 16);
		return new Color(r, g, b);
	}

	public static String RgbToAnsi(Color rgb) {
		if (rgb == null) 
			return "";
		int min = Integer.MAX_VALUE;
		Color minColor = null;
	 	for (Color ansi : ansiColors.keySet()) {
			int error = colorError(rgb, ansi);
			if (min > error) {
				minColor = ansi;
				min = error;
			}
		}
		return "\u001b[" + ansiColors.get(minColor) + "m";
	}

	public static final String ANSI_NORMAL = "\u001b[0m";
	public static int colorError(Color c1, Color c2) {
		int r = c1.getRed() - c2.getRed();
		int g = c1.getGreen() - c2.getGreen();
		int b = c1.getBlue() - c2.getBlue();

		return r*r + g*g + b*b;
	}
}
