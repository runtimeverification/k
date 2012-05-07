package ro.uaic.info.fmse.transitions.maude;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class MaudeHelper {

	public static List<String> separators = new ArrayList<String>();
	public static Set<String> declaredSorts = new HashSet<String>();
	public static List<String> basicSorts = getBasicSorts();
	public static Set<String> kLabels = new HashSet<String>();
	
	private static List<String> getBasicSorts() {
		List<String> basic = new LinkedList<String>();
		
		basic.add("Bag");
		basic.add("K");
		basic.add("List");
		basic.add("Set");
		basic.add("Map");
		basic.add("BagItem");
//		basic.add("KItem");
		basic.add("ListItem");
		basic.add("SetItem");
		basic.add("MapItem");
		basic.add("KLabel");
		basic.add("List{K}");
		basic.add("KResult");
		
		return basic;
	}
	
	
}
