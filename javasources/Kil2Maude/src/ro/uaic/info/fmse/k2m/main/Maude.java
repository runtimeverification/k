/**
 * 
 */
package ro.uaic.info.fmse.k2m.main;

import generated.Constants;
import generated.TagFactory;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import ro.uaic.info.fmse.k2m.preprocessor.Preprocessor;
import ro.uaic.info.fmse.k2m.tag.NotGeneratedConstants;
import ro.uaic.info.fmse.k2m.tag.Tag;
import ro.uaic.info.fmse.utils.strings.StringUtil;
import ro.uaic.info.fmse.utils.xml.XML;


/**
 * @author andrei.arusoaie
 * 
 */
public class Maude {

	private Document doc;
	private Map<String, String> consMap;

	public static Set<String> declaredSorts;
	public static Set<String> mainSorts;
	public static Set<String> basicSorts;
	public static Set<String> listSeparators;
	public static Map<String, String> sortToSeparator;

	public Maude(String kil) {
		doc = XML.getDocument(kil);

		// preprocessor
		Preprocessor preprocessor = new Preprocessor();
		doc = preprocessor.process(doc);
		
		// init consMap
		initConsMap();

		// initialize: map list sorts to separator
		initSortToSeparator();

		// initialize others
		init();
	}

	private void initSortToSeparator()
	{
		sortToSeparator = new HashMap<String, String>();
		
		NodeList userLists = doc.getElementsByTagName(Constants.USERLIST_userlist_TAG);
		for(int i = 0; i < userLists.getLength(); i++)
		{
			Element userList = (Element)userLists.item(i);
			String mainSort = userList.getAttribute(NotGeneratedConstants.MAINSORT);
			String separator = userList.getAttribute(Constants.SEPARATOR_separator_ATTR);
			
			if (!mainSort.equals("") && !separator.equals(""))
				sortToSeparator.put(mainSort, separator);
		}
	}
	
	private static void init() {
		listSeparators = new HashSet<String>();

		declaredSorts = new HashSet<String>();
		declaredSorts.add("K");
		declaredSorts.add("KLabel");
		declaredSorts.add("Map");
		declaredSorts.add("Set");
		declaredSorts.add("List");
		declaredSorts.add("Bag");

		declaredSorts.add("MapItem");
		declaredSorts.add("SetItem");
		declaredSorts.add("ListItem");
		declaredSorts.add("BagItem");

		declaredSorts.add("List{K}");
		declaredSorts.add("KResult");

		mainSorts = new HashSet<String>();
		mainSorts.addAll(declaredSorts);

		basicSorts = new HashSet<String>();
		basicSorts.add("K");
		basicSorts.add("Map");
		basicSorts.add("Set");
		basicSorts.add("List");
		basicSorts.add("Bag");

	}

	private void initConsMap()
	{
		consMap = new HashMap<String, String>();

		// This should be removed.
//		consMap.put("ListDlKDr1List", "_`,`,_");

		NodeList productions = doc.getElementsByTagName(Constants.PRODUCTION_production_TAG);
		for (int i = 0; i < productions.getLength(); i++) {
			
			Element production = (Element)productions.item(i);
			String cons = production.getAttribute(NotGeneratedConstants.CONS);
			if (!cons.equals(""))
			{
				String label = production.getAttribute(NotGeneratedConstants.LABEL);
				cons = cons.substring(1, cons.length() - 1);
				// label = StringUtil.escape(label);
				consMap.put(cons, label);
			}
		}		
	}

	/**
	 * @return
	 * @throws Exception
	 */
	public String getMEL() throws Exception {

		// for(Entry<String, String> entry : consMap.entrySet())
		// {
		// System.out.println("Cons: " + entry.getKey() + " value: " +
		// entry.getValue());
		// }
		// System.exit(1);

		// for(Entry<String, String> entry : sortToSeparator.entrySet())
		// {
		// System.out.println("Sort: " + entry.getKey() + " separator: " +
		// entry.getValue());
		// }
		// System.exit(1);

		List<Tag> list = new LinkedList<Tag>();

		NodeList modules = doc.getElementsByTagName("module");
		for (int i = 0; i < modules.getLength(); i++)
			list.add(TagFactory.createTag((Element) modules.item(i), consMap));

		String mel = "";
		for (Tag tag : list)
			mel += tag.toMaude() + "\n";

		return mel;
	}

	public String getAst(String pgmKil) throws Exception {

		Document xml = XML.getDocument(pgmKil);

		// check the thing..
		// ParsingError.check(xml);
		
		List<Tag> list = new LinkedList<Tag>();

		NodeList nodes = xml.getFirstChild().getChildNodes();
		for (int i = 0; i < nodes.getLength(); i++)
			if (nodes.item(i).getNodeType() == Node.ELEMENT_NODE) {
				list.add(TagFactory.createTag((Element) nodes.item(i), consMap));
			}

		String ast = "";
		for (Tag tag : list)
			ast += tag.toAst() + "\n";
		
		return ast;
	}
}
