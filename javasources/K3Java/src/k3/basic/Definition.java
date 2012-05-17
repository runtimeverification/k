package k3.basic;

import java.io.File;
import java.io.IOException;
import java.security.KeyStore.Entry;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import k.utils.Error;
import k.utils.FileUtil;
import k.utils.GlobalSettings;
import k.utils.KPaths;
import k.utils.StringUtil;
import k.utils.Tag;
import k.utils.XmlLoader;
import k2parser.KParser;
import k3.basic.Item.ItemType;
import k3.basic.Sentence.SentenceType;

import org.w3c.dom.DOMException;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class Definition implements Cloneable {
	private List<Module> modules;
	private Map<String, Module> modulesMap;
	private List<String> filePaths;
	private File mainFile;
	private String mainModule;
	private String languageModuleName;

	public Definition() {
		modulesMap = new HashMap<String, Module>();
		modules = new ArrayList<Module>();
		filePaths = new ArrayList<String>();
	}

	public Definition clone() {
		try {
			super.clone();
			Definition def2 = new Definition();
			def2.mainFile = mainFile;
			def2.languageModuleName = languageModuleName;

			for (Module m : modules) {
				Module m2 = m.clone();
				def2.modules.add(m2);
				def2.modulesMap.put(m2.getModuleName(), m2);
			}
			for (String f : filePaths)
				def2.filePaths.add(f);

			return def2;
		} catch (CloneNotSupportedException e) {
			e.printStackTrace();
		}
		return null;
	}

	/**
	 * Given a file, this method parses it and creates a list of modules of all the included files.
	 * 
	 * @param filepath
	 */
	public void slurp(File file, boolean firstTime) {
		if (!file.exists()) {
			Error.externalReport("Could not find file: " + file.getAbsolutePath());
		}
		try {
			String cannonicalPath = file.getCanonicalPath();
			if (!filePaths.contains(cannonicalPath)) {
				if (file.getAbsolutePath().endsWith(".k")) {
					String content = FileUtil.getFileContent(file.getAbsolutePath());

					String parsed = KParser.ParseKString(content);
					Document doc = XmlLoader.getXMLDoc(parsed);
					XmlLoader.addFilename(doc.getFirstChild(), file.getAbsolutePath());
					XmlLoader.reportErrors(doc);

					if (firstTime) {
						// add automatically the autoinclude.k file
						if (GlobalSettings.verbose)
							System.out.println("Including file: " + "autoinclude.k");
						File newFilePath = buildInclPath(file, "autoinclude.k");
						slurp(newFilePath, false);
					}

					NodeList xmlIncludes = doc.getDocumentElement().getElementsByTagName(Tag.require);
					for (int i = 0; i < xmlIncludes.getLength(); i++) {
						String inclFile = xmlIncludes.item(i).getAttributes().getNamedItem("value").getNodeValue();
						if (GlobalSettings.verbose)
							System.out.println("Including file: " + inclFile);
						File newFilePath = buildInclPath(file, inclFile);
						slurp(newFilePath, false);
					}

					NodeList xmlModules = doc.getDocumentElement().getElementsByTagName(Tag.module);

					for (int i = 0; i < xmlModules.getLength(); i++) {
						Module km = new Module(xmlModules.item(i), cannonicalPath);
						// set the module type as predefined if it is located in the /include directory
						// used later when including SHARED module
						if (file.getAbsolutePath().startsWith(new File(KPaths.getKBase(false) + "/include/").getAbsolutePath()))
							km.setPredefined(true);
						modules.add(km);
						modulesMap.put(km.getModuleName(), km);
					}
					filePaths.add(cannonicalPath);
				} else {
					Error.externalReport("File: " + file.getCanonicalPath() + " is not .k");
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private File buildInclPath(File currFile, String inclFile) throws IOException {
		File file = currFile;
		String base = file.getParentFile().getAbsolutePath();
		String filepath = base + System.getProperty("file.separator") + inclFile;
		file = new File(filepath);

		if (!file.exists()) {
			file = new File(KPaths.getKBase(false) + "/include/" + inclFile);
			if (file.exists()) {
				return new File(file.getCanonicalPath());
			}

			file = new File(filepath);
			Error.externalReport("Could not find file: " + inclFile + " imported from " + currFile);
		}
		return new File(file.getCanonicalPath());
	}

	public String getSDFForDefinition() {
		String sdf = "module Integration\n\n";
		sdf += "imports Common\n";
		sdf += "imports KTechnique\n";
		sdf += "imports KBuiltinsBasic\n\n";
		sdf += "exports\n\n";

		List<Production> outsides = new ArrayList<Production>();
		// List<Production> constants = new ArrayList<Production>();
		Map<String, String> constants = new HashMap<String, String>();
		Set<Sort> sorts = new HashSet<Sort>(); // list of declared sorts
		Set<Terminal> terminalList = getTerminals(false);
		// list of sorts declared as being list
		Set<Sort> listSorts = new HashSet<Sort>();

		for (Module m : modules) {
			for (Sentence s : m.getSentences()) {
				if (s.getType() == SentenceType.SYNTAX) {
					Syntax syn = (Syntax) s;
					sorts.add(syn.getSort());
					List<Priority> prilist = new ArrayList<Priority>();
					for (Priority prt : syn.getPriorities()) {
						Priority p = new Priority();
						p.setBlockAssoc(prt.getBlockAssoc());
						// p.getProductions().add(e)

						// filter the productions according to their form
						for (Production prd : prt.getProductions()) {
							for (Item it : prd.getItems())
								if (it.getType() == ItemType.SORT)
									sorts.add((Sort) it);

							// if the user declares a klabel in the attributes list, declare it as a KLabel constant
							if (prd.getAttributes().containsKey("klabel")) {
								// TODO: don't add this for now, it creates ambiguities
								//constants.put(prd.getAttributes().get("klabel"), "KLabel");
								//terminalList.add(new Terminal(prd.getAttributes().get("klabel")));
							}

							if (prd.getAttributes().containsKey("bracket")) {
								// do nothing for programs
							} else if (prd.isSubsort()) {
								outsides.add(prd);
							} else if (prd.getItems().get(0).getType() == ItemType.TERMINAL && prd.getItems().size() == 1
									&& (prd.getItems().size() == 1 && prd.getProdSort().getSortName().startsWith("#") || prd.getProdSort().getSortName().equals("KLabel"))) {
								// constants.add(prd);
								String terminal = ((Terminal) prd.getItems().get(0)).getTerminal();
								String sort = prd.getProdSort().getSortName();
								constants.put(terminal, sort);
							} else if (prd.getItems().get(0).getType() == ItemType.TERMINAL && prd.getItems().get(prd.getItems().size() - 1).getType() == ItemType.TERMINAL) {
								outsides.add(prd);
							} else if (prd.getProdSort().isBaseSort()) {
								// TODO: pentru sorturile mari, care nu sunt K, adauga si prioritatile fata de =>
								outsides.add(prd);
							} else if (prd.getItems().get(0).getType() == ItemType.USERLIST) {
								outsides.add(prd);
								listSorts.add(prd.getProdSort());
							} else {
								p.getProductions().add(prd);
							}
						}
						if (p.getProductions().size() > 0)
							prilist.add(p);
					}

					if (prilist.size() > 0) {
						sdf += "context-free priorities\n";

						for (Priority prt : prilist) {
							if (prt.getBlockAssoc() == null)
								sdf += "{\n";
							else
								sdf += "{ " + prt.getBlockAssoc() + ":\n";
							for (Production p : prt.getProductions()) {
								sdf += "	" + getSDFProdsInPriority(p.getItems(), listSorts) + "-> ";
								if (p.getProdSort().isBaseSort())
									sdf += p.getProdSort().getSortName();
								else
									sdf += "K";
								sdf += getSDFAttributes(p.getAttributes()) + "\n";
							}
							sdf += "} > ";
						}
						sdf += "{\n";
						sdf += "	K \"~>\" K -> K\n";
						sdf += "}\n\n";
					}
				}
			}
		}

		sdf += "context-free syntax\n";
		sdf += "	K -> InsertDzK\n";
		for (Production p : outsides) {
			if (p.isListDecl()) {
				System.out.println("This should not happend, Syntactic lists should be cons list when parsing K3 definitions. Check me.");
				System.exit(0);
			} else if (!p.isSubsort()) {
				sdf += "	" + getSDFProds(p.getItems()) + "-> ";
				if (p.getProdSort().isBaseSort()) {
					sdf += StringUtil.escapeSortName(p.getProdSort().getSortName());
				} else
					sdf += "K";
				sdf += getSDFAttributes(p.getAttributes()) + "\n";
			}
		}

		sdf += "\n\n";
		// print variables, HOLEs
		for (Sort s : sorts) {
			if (!s.isBaseSort()) {
				sdf += "	VARID  \":\" \"" + s.getSortName() + "\"        -> K            {cons(\"" + StringUtil.escapeSortName(s.getSortName()) + "12Var\")}\n";
			}
		}
		sdf += "\n";
		for (Sort s : sorts) {
			if (!s.isBaseSort()) {
				sdf += "	\"HOLE\" \":\" \"" + s.getSortName() + "\"      -> K            {cons(\"" + StringUtil.escapeSortName(s.getSortName()) + "12Hole\")}\n";
			}
		}

		sdf += "\n\n";
		sdf += "	DzInt		-> K\n";
		sdf += "	DzBool		-> K\n";
		sdf += "	DzId		-> K\n";
		sdf += "	DzString	-> K\n";

		sdf += "\n";
		sdf += "	DzDzInt		-> DzInt	{cons(\"DzInt1Const\")}\n";
		sdf += "	DzDzBool	-> DzBool	{cons(\"DzBool1Const\")}\n";
		sdf += "	DzDzId		-> DzId		{cons(\"DzId1Const\")}\n";
		sdf += "	DzDzString	-> DzString	{cons(\"DzString1Const\")}\n";

		sdf += "\n";
		sdf += "	DzDzINT		-> DzDzInt\n";
		sdf += "	DzDzBOOL	-> DzDzBool\n";
		sdf += "	DzDzSTRING	-> DzDzString\n";

		sdf += "\n";
		sdf += "lexical syntax\n";
		sdf += "	%% constants\n";
		for (Map.Entry<String, String> p : constants.entrySet()) {
			sdf += "	\"" + p.getKey() + "\" -> Dz" + StringUtil.escapeSortName(p.getValue()) + "\n";
		}

		sdf += "\n	%% terminals reject\n";
		for (Terminal t : terminalList) {
			if (t.getTerminal().matches("$?[A-Z][^\\:\\;\\(\\)\\<\\>\\~\\n\\r\\t\\,\\ \\[\\]\\=\\+\\-\\*\\/\\|\\{\\}\\.]*")) {
				sdf += "	\"" + t.getTerminal() + "\" -> VARID {reject}\n";
			}
		}

		sdf += getFollowRestrictionsForTerminals(false);

		return sdf + "\n";
	}

	public String getSDFForPrograms() {
		String sdf = "module Program\n\n";
		sdf += "imports Common\n";
		sdf += "imports KBuiltinsBasic\n";
		sdf += "exports\n\n";
		sdf += "context-free syntax\n";

		List<Production> outsides = new ArrayList<Production>();
		List<Production> constants = new ArrayList<Production>();
		Set<Sort> sorts = new HashSet<Sort>(); // list of inserted sorts that need to avoid the priority filter
		Set<Sort> startSorts = new HashSet<Sort>(); // list of sorts that are start symbols
		Set<Sort> listSorts = new HashSet<Sort>(); // list of sorts declared as being list
		Set<Sort> userSort = new HashSet<Sort>(); // list of sorts declared by the user (to be declared later as Start symbols if no declaration for Start was found)

		// gather modules for syntax
		String mainSynModName;
		if (GlobalSettings.synModule == null)
			mainSynModName = mainModule + "-SYNTAX";
		else
			mainSynModName = GlobalSettings.synModule;
		Module mainSyntax = modulesMap.get(mainSynModName);
		Set<Module> synMods = new HashSet<Module>();
		List<Module> synQue = new LinkedList<Module>();

		synQue.add(mainSyntax);
		if (mainSyntax == null) {
			Error.silentReport("Could not find a module for program syntax: " + mainSynModName);
		} else {

			while (!synQue.isEmpty()) {
				Module m = synQue.remove(0);
				if (!synMods.contains(m)) {
					synMods.add(m);
					List<Sentence> ss = m.getSentences();
					for (Sentence s : ss)
						if (s.getType() == SentenceType.INCLUDING) {
							String mname = ((Including) s).getIncludedModuleName();
							Module mm = modulesMap.get(mname);
							// if the module starts with # it means it is predefined in maude
							if (!mname.startsWith("#"))
								if (mm != null)
									synQue.add(mm);
								else
									Error.silentReport("Could not find module: " + mname + " imported from: " + m.getModuleName());
						}
				}
			}

			for (Module m : synMods) {
				for (Sentence s : m.getSentences()) {
					if (s.getType() == SentenceType.SYNTAX) {
						Syntax syn = (Syntax) s;
						userSort.add(syn.getSort());
						List<Priority> prilist = new ArrayList<Priority>();
						for (Priority prt : syn.getPriorities()) {
							Priority p = new Priority();
							p.setBlockAssoc(prt.getBlockAssoc());

							// filter the productions according to their form
							for (Production prd : prt.getProductions()) {
								if (prd.isSubsort()) {
									outsides.add(prd);
									if (prd.getProdSort().equals(new Sort("Start")))
										startSorts.add((Sort) prd.getItems().get(0));
								} else if (prd.getItems().get(0).getType() == ItemType.TERMINAL && prd.getItems().size() == 1 && prd.getProdSort().getSortName().startsWith("#")) {
									constants.add(prd);
								} else if (prd.getItems().get(0).getType() == ItemType.TERMINAL && prd.getItems().get(prd.getItems().size() - 1).getType() == ItemType.TERMINAL) {
									outsides.add(prd);
								} else if (prd.getItems().get(0).getType() == ItemType.USERLIST) {
									outsides.add(prd);
									listSorts.add(prd.getProdSort());
								} else {
									p.getProductions().add(prd);
								}
							}
							if (p.getProductions().size() > 0)
								prilist.add(p);
						}
						if (prilist.size() > 0) {
							if (prilist.size() <= 1 && syn.getPriorities().get(0).getBlockAssoc() == null) {
								// weird bug in SDF - if you declare only one production in a priority block, it gives parse errors
								// you need to have at least 2 productions or a block association
								Priority prt = prilist.get(0);
								for (Production p : prt.getProductions())
									outsides.add(p);
							} else {
								sdf += "context-free priorities\n";

								for (Priority prt : prilist) {
									if (prt.getBlockAssoc() == null)
										sdf += "{\n";
									else
										sdf += "{ " + prt.getBlockAssoc() + ":\n";
									for (Production p : prt.getProductions()) {
										sdf += "	";
										List<Item> items = p.getItems();
										for (int i = 0; i < items.size(); i++) {
											Item itm = items.get(i);
											if (itm.getType() == ItemType.TERMINAL) {
												Terminal t = (Terminal) itm;
												sdf += "\"" + t.getTerminal() + "\" ";
											} else if (itm.getType() == ItemType.SORT) {
												Sort srt = (Sort) itm;
												// if we are on the first or last place and this sort is not a list, just print the sort
												if (i == 0 || i == items.size() - 1) {
													sdf += StringUtil.escapeSortName(srt.getSortName()) + " ";
												} else {
													// if this sort should be inserted to avoid the priority filter, then add it to the list
													sorts.add(srt);
													sdf += "InsertDz" + StringUtil.escapeSortName(srt.getSortName()) + " ";
												}
											}
										}
										sdf += "-> " + StringUtil.escapeSortName(p.getProdSort().getSortName());
										sdf += getSDFAttributes(p.getAttributes()) + "\n";
									}
									sdf += "} > ";
								}
								sdf = sdf.substring(0, sdf.length() - 3) + "\n\n";
							}
						}
					}
				}
			}

			sdf += "context-free start-symbols\n";
			sdf += "	Start\n";
			sdf += "context-free syntax\n";

			for (Production p : outsides) {
				if (p.isListDecl()) {
					UserList si = (UserList) p.getItems().get(0);
					sdf += "	{" + StringUtil.escapeSortName(si.getSort().getSortName()) + " \"" + si.getTerminal() + "\"}* -> " + StringUtil.escapeSortName(p.getProdSort().getSortName()) + " {cons(\"" + p.getAttributes().get("cons") + "\")}\n";
				} else {
					sdf += "	";
					List<Item> items = p.getItems();
					for (int i = 0; i < items.size(); i++) {
						Item itm = items.get(i);
						if (itm.getType() == ItemType.TERMINAL) {
							Terminal t = (Terminal) itm;
							sdf += "\"" + t.getTerminal() + "\" ";
						} else if (itm.getType() == ItemType.SORT) {
							Sort srt = (Sort) itm;
							sdf += StringUtil.escapeSortName(srt.getSortName()) + " ";
						}
					}
					sdf += "-> " + StringUtil.escapeSortName(p.getProdSort().getSortName());
					sdf += getSDFAttributes(p.getAttributes()) + "\n";
				}
			}
			for (Sort ss : sorts)
				sdf += "	" + StringUtil.escapeSortName(ss.getSortName()) + " -> InsertDz" + StringUtil.escapeSortName(ss.getSortName()) + "\n";

			sdf += "\n%% start symbols\n";
			if (startSorts.size() == 0) {
				for (Sort s : userSort) {
					if (!s.getSortName().equals("Start"))
						sdf += "	" + StringUtil.escapeSortName(s.getSortName()) + "		-> Start\n";
				}
			}

			sdf += "\n\n";
			sdf += "	DzDzInt		-> DzInt	{cons(\"DzInt1Const\")}\n";
			sdf += "	DzDzBool	-> DzBool	{cons(\"DzBool1Const\")}\n";
			sdf += "	DzDzId		-> DzId		{cons(\"DzId1Const\")}\n";
			sdf += "	DzDzString	-> DzString	{cons(\"DzString1Const\")}\n";

			sdf += "\n";
			sdf += "	DzDzINT		-> DzDzInt\n";
			sdf += "	DzDzID		-> DzDzId\n";
			sdf += "	DzDzBOOL	-> DzDzBool\n";
			sdf += "	DzDzSTRING	-> DzDzString\n";

			sdf += "\n";

			sdf += "lexical syntax\n";
			for (Production p : constants) {
				sdf += "	\"" + p.getItems().get(0) + "\" -> Dz" + StringUtil.escapeSortName(p.getProdSort().getSortName()) + "\n";
			}

			sdf += "\n\n";

			for (Terminal t : getTerminals(true)) {
				if (t.getTerminal().matches("[a-zA-Z][a-zA-Z0-9]*")) {
					sdf += "	\"" + t.getTerminal() + "\" -> DzDzID {reject}\n";
				}
			}

			sdf += "\n";
			sdf += getFollowRestrictionsForTerminals(true);

		}
		return sdf + "\n";
	}

	public Set<Terminal> getTerminals(boolean syntax) {
		Set<Terminal> termins = new HashSet<Terminal>();

		for (Module m : modules) {
			if (!m.getModuleName().endsWith("SYNTAX") && syntax)
				continue; // skip modules that don't end in SYNTAX
			for (Sentence s : m.getSentences()) {
				if (s.getType() == SentenceType.SYNTAX) {
					Syntax syn = (Syntax) s;
					List<Production> prods = syn.getProductions();

					for (Production p : prods) {
						if (!(p.getProdSort().getSortName().equals("#Id") && p.getItems().size() == 1 && p.getItems().get(0).getType() == ItemType.TERMINAL))
							// reject those terminals that are not declared as #Id
							for (Item i : p.getItems())
								if (i.getType() == ItemType.TERMINAL) {
									termins.add((Terminal) i);
								}
					}
				}
			}
		}

		return termins;
	}

	public String getFollowRestrictionsForTerminals(boolean syntax) {
		Set<Terminal> terminals = getTerminals(syntax);
		Set<Ttuple> mytuples = new HashSet<Definition.Ttuple>();
		String varid = "[A-Z][^:\\;\\(\\)\\<\\>\\~\\n\\r\\t\\,\\ \\[\\]\\=\\+\\-\\*\\/\\|\\{\\}\\.]*";

		for (Terminal t1 : terminals) {
			for (Terminal t2 : terminals) {
				if (t1 != t2) {
					String a = t1.getTerminal();
					String b = t2.getTerminal();
					if (a.startsWith(b)) {
						Ttuple tt = new Ttuple();
						tt.key = a;
						tt.value = b;
						String ending = tt.key.substring(tt.value.length());
						if (ending.matches(varid))
							mytuples.add(tt);
					}
				}
			}
		}

		String sdf = "lexical restrictions\n";
		sdf += "	%% follow restrictions\n";
		for (Ttuple tt : mytuples) {
			sdf += "	\"" + tt.value + "\" -/- ";
			String ending = tt.key.substring(tt.value.length());
			for (int i = 0; i < ending.length(); i++) {
				String ch = "" + ending.charAt(i);
				if (ch.matches("[a-zA-Z]"))
					sdf += "[" + ch + "].";
				else
					sdf += "[\\" + ch + "].";
			}
			sdf = sdf.substring(0, sdf.length() - 1) + "\n";
		}

		return sdf;
	}

	/**
	 * Using this class to collect the prefixes amongst terminals
	 * 
	 * @author RaduFmse
	 * 
	 */
	public class Ttuple {
		public String key;
		public String value;

		public boolean equals(Object o) {
			if (o.getClass() == Ttuple.class)
				return false;
			Ttuple tt = (Ttuple) o;
			if (key.equals(tt.key) && value.equals(tt.value))
				return true;
			return false;
		}

		public int hashCode() {
			return key.hashCode() + value.hashCode();
		}
	}

	public Map<Production, List<Production>> getProductionDittos() {
		Map<Production, List<Production>> prods2 = new HashMap<Production, List<Production>>();
		for (Module m : modules) {
			for (Sentence s : m.getSentences()) {
				if (s.getType() == SentenceType.SYNTAX) {
					Syntax syn = (Syntax) s;
					List<Production> prods = syn.getProductions();

					for (Production p : prods) {
						if (!p.isSubsort()) {
							Production p2 = p.clone();// (Production) Cloner.copy(p);
							p2.collapseSorts();
							if (prods2.containsKey(p2)) {
								List<Production> lprod = prods2.get(p2);
								lprod.add(p);
							} else {
								List<Production> lprod = new ArrayList<Production>();
								lprod.add(p);
								prods2.put(p2, lprod);
							}
						}
					}
				}
			}
		}

		return prods2;
	}

	public Set<Subsort> getSubsorts() {
		// collect the existing subsorting, and add the default ones
		Set<Subsort> sbs = Subsort.getDefaultSubsorts();
		for (Module m : modules) {
			for (Sentence s : m.getSentences()) {
				if (s.getType() == SentenceType.SYNTAX) {
					Syntax syn = (Syntax) s;
					if (!syn.getSort().isBaseSort())
						sbs.add(new Subsort(new Sort("K"), syn.getSort(), syn.getSort().getFilename(), syn.getSort().getLocation()));
					for (Production p : syn.getProductions()) {
						if (p.getItems().size() == 1 && p.getItems().get(0).getType() == ItemType.SORT) {
							// this is a subsort, add it to the list
							Sort s2 = (Sort) p.getItems().get(0);
							sbs.add(new Subsort(syn.getSort(), s2, s2.getFilename(), s2.getLocation()));
						}
					}
				}
			}
		}

		// closure for sorts
		boolean finished = false;
		while (!finished) {
			finished = true;
			Set<Subsort> ssTemp = new HashSet<Subsort>();
			for (Subsort s1 : sbs) {
				for (Subsort s2 : sbs) {
					if (s1.getBigSort().equals(s2.getSmallSort())) {
						Subsort sTemp = new Subsort(s2.getBigSort(), s1.getSmallSort(), "Transitive Closure", "(0,0,0,0)");
						if (!sbs.contains(sTemp)) {
							ssTemp.add(sTemp);
							finished = false;
						}
					}
				}
			}
			sbs.addAll(ssTemp);
		}

		return sbs;
	}

	public String getSubsortingAsStrategoTerms() {
		Set<Subsort> sbs = this.getSubsorts();
		String term = "[  ";
		for (Subsort ss : sbs) {
			term += "(\"" + ss.getBigSort() + "\", \"" + ss.getSmallSort() + "\")\n, ";
		}

		return term.substring(0, term.length() - 2) + "]";
	}

	public String getConsAsStrategoTerms() {
		String str = "[  ";
		for (Module m : modules) {
			for (Sentence s : m.getSentences()) {
				if (s.getType() == SentenceType.SYNTAX) {
					Syntax syn = (Syntax) s;
					for (Production p : syn.getProductions()) {
						if (p.getItems().size() > 1 || p.getItems().get(0).getType() == ItemType.TERMINAL || p.isListDecl()) {
							// if it contains at least one non-terminal - add it to the list
							boolean hasNonTerminal = false;
							String tempStr = "(\"" + p.getAttributes().get("cons") + "\",   \"" + syn.getSort() + "\", [";

							for (Item i : p.getItems()) {
								if (i.getType() == ItemType.SORT) {
									hasNonTerminal = true;
									tempStr += "\"" + i + "\", ";
								}
							}
							if (hasNonTerminal) {
								str += tempStr.substring(0, tempStr.length() - 2) + "])\n, ";
							} else
								str += tempStr + "])\n, ";
						}
					}
				}
			}
		}

		return str.substring(0, str.length() - 2) + "]";
	}

	private String getSDFAttributes(Map<String, String> attrs) {
		String str = " {";
		if (attrs.size() == 0)
			return "";

		if (attrs.containsKey("prefer"))
			str += "prefer, ";
		if (attrs.containsKey("avoid"))
			str += "avoid, ";
		if (attrs.containsKey("left"))
			str += "left, ";
		if (attrs.containsKey("right"))
			str += "right, ";
		if (attrs.containsKey("non-assoc"))
			str += "non-assoc, ";
		if (attrs.containsKey("bracket"))
			str += "bracket, ";
		if (attrs.containsKey("cons"))
			str += "cons(\"" + attrs.get("cons") + "\"), ";

		if (str.endsWith(", "))
			return str.substring(0, str.length() - 2) + "}";
		else
			return str + "}";
	}

	private String getSDFProdsInPriority(List<Item> items, Set<Sort> listSorts) {
		String str = "";
		for (int i = 0; i < items.size(); i++) {
			Item itm = items.get(i);
			if (itm.getType() == ItemType.TERMINAL) {
				Terminal t = (Terminal) itm;
				str += "\"" + t.getTerminal() + "\" ";
			} else if (itm.getType() == ItemType.SORT) {
				Sort s = (Sort) itm;
				if (s.isBaseSort()) {
					str += StringUtil.escapeSortName(s.getSortName()) + " ";
				} else if (listSorts.contains(s)) { // this is a list
					str += StringUtil.escapeSortName(s.getSortName()) + " ";
				} else if (i == 0 || i == items.size() - 1) {
					// apply the priority filter only to the outermost locations
					str += "K ";
				} else {
					// if inside the production create special sort
					str += "InsertDzK ";
				}
			}
		}

		return str;
	}

	private String getSDFProds(List<Item> items) {
		String str = "";
		for (Item i : items) {
			if (i.getType() == ItemType.TERMINAL) {
				Terminal t = (Terminal) i;
				str += "\"" + t.getTerminal() + "\" ";
			} else if (i.getType() == ItemType.SORT) {
				Sort s = (Sort) i;
				if (s.isBaseSort()) {
					str += StringUtil.escapeSortName(s.getSortName()) + " ";
				} else {
					str += "K ";
				}
			}
		}

		return str;
	}

	public File getMainFile() {
		return mainFile;
	}

	public void setMainFile(File mainFile) {
		this.mainFile = mainFile;
	}

	public String getLanguageModuleName() {
		return languageModuleName;
	}

	public void setLanguageModuleName(String languageModuleName) {
		this.languageModuleName = languageModuleName;
	}

	public List<Sentence> getAllSentences() {
		List<Sentence> sts = new ArrayList<Sentence>();
		for (Module m : modules) {
			sts.addAll(m.getSentences());
		}
		return sts;
	}

	public String getCellsFromConfigAsStrategoTerm() {
		List<Sentence> sts = this.getAllSentences();
		Map<String, Cell> cells = new HashMap<String, Cell>();
		for (Sentence s : sts) {
			if (s.getType() == SentenceType.CONFIGURATION) {
				Configuration c = (Configuration) s;
				c.parse();
				cells.putAll(c.getCellLabels());
			}
		}

		String term = "[  ";
		for (Map.Entry<String, Cell> c : cells.entrySet()) {
			term += "(\"" + c.getKey() + "\", \"" + c.getValue().getSort() + "\")\n, ";
		}

		return term.substring(0, term.length() - 2) + "]";
	}

	public void parseRules() {
		List<Sentence> sts = this.getAllSentences();
		for (Sentence s : sts) {
			if (s.getType() == SentenceType.RULE) {
				Rule r = (Rule) s;
				r.parse();
			} else if (s.getType() == SentenceType.CONTEXT) {
				Context c = (Context) s;
				c.parse();
			}
		}
	}

	public Document getDefAsXML() {
		try {
			DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
			DocumentBuilder db = dbf.newDocumentBuilder();
			Document doc = db.newDocument();

			Element el = doc.createElement("def");

			el.setAttribute("mainFile", this.mainFile.getCanonicalPath());
			el.setAttribute("mainModule", this.mainModule);

			for (Module m : modules) {
				el.appendChild(doc.importNode(m.xmlTerm, true));
			}

			doc.appendChild(el);

			return doc;
		} catch (ParserConfigurationException e) {
			e.printStackTrace();
		} catch (DOMException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}

		return null;
	}

	public void makeConsLists() throws Exception {
		for (Module m : modules) {
			for (Sentence s : m.getSentences()) {
				if (s.getType() == SentenceType.SYNTAX) {
					Syntax syn = (Syntax) s;
					for (Priority pry : syn.getPriorities()) {
						List<Production> prods = pry.getProductions();

						for (Production p : prods) {
							if (p.isListDecl()) {
								// this is the list decl
								UserList sl = (UserList) p.getItems().get(0);

								p.getItems().clear(); // clear the production
								p.getItems().add(p.getProdSort()); // and replace it with the cons list
								p.getItems().add(new Terminal(sl.getTerminal()));
								p.getItems().add(p.getProdSort());
								p.getAttributes().put("right", "");

								Production sbs = new Production(); // also add the element subsorted to the list sort
								sbs.setProdSort(p.getProdSort());
								sbs.getItems().add(sl.getSort());
								prods.add(sbs);

								Production idElem = new Production(); // also add the identity element
								idElem.setProdSort(p.getProdSort());
								idElem.getItems().add(new Terminal("." + p.getProdSort().getSortName()));
								String cons = p.getAttributes().get("cons");
								if (!cons.endsWith("ListSyn"))
									throw new Exception("Why isn't this cons ending in ListSyn: " + cons);
								cons = cons.substring(0, cons.length() - "ListSyn".length());
								idElem.getAttributes().put("cons", cons + "Empty");
								prods.add(idElem);
								break;
							}
						}
					}
				}
			}
		}
	}

	public void addConsToProductions() {
		// add cons to productions that don't have it already
		for (Module m : modules) {
			String termination;
			if (m.getType().equals(Tag.interfaceTag))
				termination = "Builtin";
			else
				termination = "Syn";
			for (Sentence s : m.getSentences()) {
				if (s.getType() == SentenceType.SYNTAX) {
					Syntax syn = (Syntax) s;
					for (Priority pry : syn.getPriorities()) {
						List<Production> prods = pry.getProductions();

						for (Production p : prods) {
							if (p.getAttributes().containsKey("bracket")) {
								// don't add cons to bracket production
								String cons = p.getAttributes().get("cons");
								if (cons != null)
									Error.report("'bracket' productions are not allowed to have cons: '" + cons + "'");
							} else if (p.getItems().size() == 1 && p.getItems().get(0).getType() == ItemType.TERMINAL && p.getProdSort().getSortName().startsWith("#")) {
								// don't add any cons, if it is a constant
								// a constant is a single terminal for a builtin sort
								String cons = p.getAttributes().get("cons");
								if (cons != null)
									Error.report("Constants are not allowed to have cons: '" + cons + "'");
							} else if (p.isSubsort()) {
								// cons are not allowed for subsortings
								String cons = p.getAttributes().get("cons");
								if (cons != null)
									Error.report("Subsortings are not allowed to have cons: '" + cons + "'");
							} else {
								if (!p.getAttributes().containsKey("cons")) {
									String cons;
									if (p.isListDecl())
										cons = StringUtil.escapeSortName(p.getProdSort().getSortName()) + "1" + "List" + termination;
									else
										cons = StringUtil.escapeSortName(p.getProdSort().getSortName()) + "1" + StringUtil.getUniqueId() + termination;
									p.getAttributes().put("cons", cons);
									Element el = p.xmlTerm.getOwnerDocument().createElement("tag");
									el.setAttribute("key", "cons");
									el.setAttribute("loc", "generated");
									el.setAttribute("value", "\"" + cons + "\"");

									Node attributes = p.xmlTerm.getLastChild().getPreviousSibling();

									// if the production doesn't have an attributes tag, add it manually
									if (!attributes.getNodeName().equals(Tag.attributes)) {
										Element attributes2 = p.xmlTerm.getOwnerDocument().createElement(Tag.attributes);
										p.xmlTerm.appendChild(attributes2);
										attributes = attributes2;
									}

									attributes.appendChild(el);
								} else {
									// check if the provided cons is correct
									String cons = p.getAttributes().get("cons");
									String escSort = StringUtil.escapeSortName(p.getProdSort().getSortName());
									if (m.getType().equals(Tag.interfaceTag)) {
										if (!cons.endsWith("Builtin"))
											Error.report("The cons attribute must end with 'Builtin' and not with " + cons);
										if (!cons.startsWith(escSort))
											Error.report("The cons attribute must start with '" + escSort + "' and not with " + cons);
									} else {
										if (!cons.startsWith(escSort))
											Error.report("The cons attribute must start with '" + escSort + "' and not with " + cons);
										if (!cons.endsWith("Syn")) // a normal cons must end with 'Syn'
											Error.report("The cons attribute must end with 'Syn' and not with " + cons);
										if (p.isListDecl() && !cons.endsWith("ListSyn")) // if this is a list, it must end with 'ListSyn'
											Error.report("The cons attribute must end with 'ListSyn' and not with " + cons);
									}
								}
							}
						}
					}
				}
			}
		}
	}

	public void replaceDittoCons() {
		Map<Production, List<Production>> prodSummary = getProductionDittos();

		for (Module m : modules) {
			for (Sentence s : m.getSentences()) {
				if (s.getType() == SentenceType.SYNTAX) {
					Syntax syn = (Syntax) s;
					List<Production> prods = syn.getProductions();

					for (Production p : prods) {
						if (!p.isSubsort()) {
							Production p2 = p.clone();// (Production) Cloner.copy(p);
							p2.collapseSorts();

							if (prodSummary.containsKey(p2)) {
								List<Production> listForProds = prodSummary.get(p2);

								if (listForProds.size() > 1) {
									p.getAttributes().put("cons", listForProds.get(0).getAttributes().get("cons"));
								}
							}
						}
					}
				}
			}
		}
	}

	public String getDittosAsStrategoTerm() {
		Map<Production, List<Production>> prodSummary = getProductionDittos();
		String term = "[  ";
		for (Map.Entry<Production, List<Production>> ss : prodSummary.entrySet()) {
			List<Production> listForProds = ss.getValue();

			if (listForProds.size() > 1) {
				term += "(\"" + listForProds.get(0).getAttributes().get("cons") + "\", [";
				for (Production p : listForProds) {
					term += "\"" + p.getAttributes().get("cons") + "\", ";
				}
				term = term.substring(0, term.length() - 2) + "])\n, ";
			}
		}

		return term.substring(0, term.length() - 2) + "]";
	}

	public void setMainModule(String mainModule) {
		this.mainModule = mainModule;
	}

	public String getMainModule() {
		return mainModule;
	}
}