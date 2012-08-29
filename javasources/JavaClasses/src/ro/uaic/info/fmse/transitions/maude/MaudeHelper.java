package ro.uaic.info.fmse.transitions.maude;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class MaudeHelper {

	public static List<String> separators = new ArrayList<String>();
	public static Set<String> declaredSorts = new HashSet<String>();
	public static Set<String> basicSorts = getBasicSorts();
	public static Set<String> kLabels = new HashSet<String>();
	public static Set<String> constantSorts = getConstantSorts();
	
	
	private static Set<String> getBasicSorts() {
		Set<String> basic = new HashSet<String>();
		
		basic.add("Bag");
		basic.add("K");
		basic.add("List");
		basic.add("Set");
		basic.add("Map");
		basic.add("BagItem");
		basic.add("CellLabel");
//		basic.add("KItem");
		basic.add("ListItem");
		basic.add("SetItem");
		basic.add("MapItem");
		basic.add("KLabel");
		basic.add("List{K}");
		basic.add("KResult");
		basic.add("#Id");
		basic.add("#String");
		basic.add("#Float");
		basic.add("#Rat");
		basic.add("#Int");
		basic.add("#Bool");
		basic.add("#ModelCheckerState");
		basic.add("#ModelCheckResult");
		basic.add("#LTLFormula");
		basic.add("#Prop");

		return basic;
	}

	private static Set<String> getConstantSorts() {
		Set<String> basic = new HashSet<String>();
		
		basic.add("#Id");
		basic.add("#String");
		basic.add("#Float");
		basic.add("#Rat");
		basic.add("#Int");
		basic.add("#Bool");
		basic.add("KLabel");
		basic.add("CellLabel");
		
		return basic;
	}
}
