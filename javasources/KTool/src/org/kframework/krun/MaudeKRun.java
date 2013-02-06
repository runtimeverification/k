package org.kframework.krun;

import org.kframework.backend.maude.MaudeFilter;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.krun.runner.KRunner;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitTypeCheckVisitor;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class MaudeKRun implements KRun {
	private PrettyPrintOutput p;

	private void executeKRun(String maudeCmd, boolean ioServer) throws Exception {
		FileUtil.createFile(K.maude_in, maudeCmd);
		File outFile = FileUtil.createFile(K.maude_out);
		File errFile = FileUtil.createFile(K.maude_err);

		if (K.log_io) {
			KRunner.main(new String[] { "--maudeFile", K.compiled_def + K.fileSeparator + "main.maude", "--moduleName", K.main_module, "--commandFile", K.maude_in, "--outputFile", outFile.getCanonicalPath(), "--errorFile", errFile.getCanonicalPath(), "--createLogs" });
		}
		if (!ioServer) {
			KRunner.main(new String[] { "--maudeFile", K.compiled_def + K.fileSeparator + "main.maude", "--moduleName", K.main_module, "--commandFile", K.maude_in, "--outputFile", outFile.getCanonicalPath(), "--errorFile", errFile.getCanonicalPath(), "--noServer" });
		} else {
			KRunner.main(new String[] { "--maudeFile", K.compiled_def + K.fileSeparator + "main.maude", "--moduleName", K.main_module, "--commandFile", K.maude_in, "--outputFile", outFile.getCanonicalPath(), "--errorFile", errFile.getCanonicalPath() });
		}

		if (errFile.exists()) {
			String content = FileUtil.getFileContent(K.maude_err);
			if (content.length() > 0) {
				throw new KRunExecutionException(content);
			}
		}

		p = new PrettyPrintOutput(K.color);
		p.preprocessDoc(K.maude_output, K.processed_maude_output);
	}

	public KRunResult run(Term cfg) throws Exception {
		MaudeFilter maudeFilter = new MaudeFilter();
		cfg.accept(maudeFilter);
		String cmd = "set show command off ." + K.lineSeparator + K.maude_cmd + " " + maudeFilter.getResult() + " .";
		if(K.trace) {
			cmd = "set trace on ." + K.lineSeparator + cmd;
		}
		if(K.profile) {
			cmd = "set profile on ." + K.lineSeparator + cmd + K.lineSeparator + "show profile .";
		}

		executeKRun(cmd, K.io);
		return parseRunResult();
	}

	public KRunResult step(Term cfg, int steps) throws Exception {
		String maude_cmd = K.maude_cmd;
		if (steps == 0) {
			K.maude_cmd = "red";
		} else {
			K.maude_cmd = "rew[" + Integer.toString(steps) + "]";
		}
		KRunResult result = run(cfg);
		K.maude_cmd = maude_cmd;
		return result;
	}

	private static class FlattenDisambiguationFilter extends BasicTransformer {
		public FlattenDisambiguationFilter() {
			super("Reflatten ambiguous syntax");
		}

		@Override
		public ASTNode transform(Ambiguity amb) throws TransformerException {
			if (amb.getContents().get(0) instanceof TermCons) {
				TermCons t1 = (TermCons)amb.getContents().get(0);
				if (MetaK.isComputationSort(t1.getSort())) {
					return new KApp(new Constant("KLabel", t1.getProduction().getKLabel()), (Term) new KList(t1.getContents()).accept(this));
				}
			} else if (amb.getContents().get(0) instanceof Empty) {
				Empty t1 = (Empty)amb.getContents().get(0);
				if (MetaK.isComputationSort(t1.getSort())) {
					return new KApp(new Constant("KLabel", MetaK.getListUnitLabel(((UserList)DefinitionHelper.listConses.get(t1.getSort()).getItems().get(0)).getSeparator())), new Empty(MetaK.Constants.KList));
				}
			}
			return amb;
		}
	}

	private KRunResult parseRunResult() throws Exception {
		File input = new File(K.maude_output);
		Document doc = XmlUtil.readXML(input);
		NodeList list = null;
		Node nod = null;
		list = doc.getElementsByTagName("result");
		nod = list.item(0);

		assertXML(nod != null && nod.getNodeType() == Node.ELEMENT_NODE);
		Element elem = (Element) nod;
		List<Element> child = XmlUtil.getChildElements(elem);
		assertXML(child.size() == 1);

		Term result = MaudeKRun.parseXML((Element) child.get(0));
		Term rawResult = MaudeKRun.parseXML((Element) child.get(0));
		result = (Term) result.accept(new ConcretizeSyntax());
		result = (Term) result.accept(new TypeInferenceSupremumFilter());
		result = (Term) result.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor()));
		//as a last resort, undo concretization
		result = (Term) result.accept(new FlattenDisambiguationFilter());
		if (result.getClass() == Cell.class) {
			Cell generatedTop = (Cell) result;
			if (generatedTop.getLabel().equals("generatedTop")) {
				result = generatedTop.getContents();
			}
		}

		KRunResult ret = new KRunResult(result, rawResult);
		String statistics = p.printStatistics(elem);
		ret.setStatistics(statistics);
		ret.setRawOutput(FileUtil.getFileContent(K.maude_out));
		return ret;
	}

	private static void assertXML(boolean assertion) {
		if (!assertion) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot parse result xml from maude. If you believe this to be in error, please file a bug and attach " + K.maude_output.replaceAll("/krun[0-9]*/", "/krun/")));
		}
	}

	private static void assertXMLTerm(boolean assertion) throws Exception {
		if (!assertion) {
			throw new Exception();
		}
	}

	public static Term parseXML(Element xml) {
		String op = xml.getAttribute("op");
		String sort = xml.getAttribute("sort");
		sort = sort.replaceAll("`([{}\\[\\](),])", "$1");
		List<Element> list = XmlUtil.getChildElements(xml);
		
		try {
			if (sort.equals("BagItem") && op.equals("<_>_</_>")) {
				Cell cell = new Cell();
				assertXMLTerm(list.size() == 3 && list.get(0).getAttribute("sort").equals("CellLabel") && list.get(2).getAttribute("sort").equals("CellLabel") && list.get(0).getAttribute("op").equals(list.get(2).getAttribute("op")));

				cell.setLabel(list.get(0).getAttribute("op"));
				cell.setContents(parseXML(list.get(1)));
				return cell;
			} else if (sort.equals("BagItem") && op.equals("BagItem")) {
				assertXMLTerm(list.size() == 1);
				return new BagItem(parseXML(list.get(0)));
			} else if (sort.equals("MapItem") && op.equals("_|->_")) {
				assertXMLTerm(list.size() == 2);
				return new MapItem(parseXML(list.get(0)), parseXML(list.get(1)));
			} else if (sort.equals("SetItem") && op.equals("SetItem")) {
				assertXMLTerm(list.size() == 1);
				return new SetItem(parseXML(list.get(0)));
			} else if (sort.equals("ListItem") && op.equals("ListItem")) {
				assertXMLTerm(list.size() == 1);
				return new ListItem(parseXML(list.get(0)));
			} else if (op.equals("_`,`,_") && sort.equals("NeKList")) {
				assertXMLTerm(list.size() >= 2);
				List<Term> l = new ArrayList<Term>();
				for (Element elem : list) {
					l.add(parseXML(elem));
				}
				return new KList(l);
			} else if (sort.equals("K") && op.equals("_~>_")) {
				assertXMLTerm(list.size() >= 2);
				List<Term> l = new ArrayList<Term>();
				for (Element elem : list) {
					l.add(parseXML(elem));
				}
				return new KSequence(l);
			} else if (op.equals("__") && (sort.equals("NeList") || sort.equals("List"))) {
				assertXMLTerm(list.size() >= 2);
				List<Term> l = new ArrayList<Term>();
				for (Element elem : list) {
					l.add(parseXML(elem));
				}
				return new org.kframework.kil.List(l);
			} else if (op.equals("__") && (sort.equals("NeBag") || sort.equals("Bag"))) {
				assertXMLTerm(list.size() >= 2);
				List<Term> l = new ArrayList<Term>();
				for (Element elem : list) {
					l.add(parseXML(elem));
				}
				return new Bag(l);
			} else if (op.equals("__") && (sort.equals("NeSet") || sort.equals("Set"))) {
				assertXMLTerm(list.size() >= 2);
				List<Term> l = new ArrayList<Term>();
				for (Element elem : list) {
					l.add(parseXML(elem));
				}
				return new org.kframework.kil.Set(l);
			} else if (op.equals("__") && (sort.equals("NeMap") || sort.equals("Map"))) {
				assertXMLTerm(list.size() >= 2);
				List<Term> l = new ArrayList<Term>();
				for (Element elem : list) {
					l.add(parseXML(elem));
				}
				return new org.kframework.kil.Map(l);
			} else if ((op.equals("#_") || op.equals("List2KLabel_") || op.equals("Map2KLabel_") || op.equals("Set2KLabel_") || op.equals("Bag2KLabel_") || op.equals("KList2KLabel_") || op.equals("KLabel2KLabel_")) && sort.equals("KLabel")) {
				assertXMLTerm(list.size() == 1);
				return new KInjectedLabel(parseXML(list.get(0)));
			} else if (sort.equals("#NzInt") && op.equals("--Int_")) {
				assertXMLTerm(list.size() == 1);
				return new Constant("#Int", "-" + ((Constant) parseXML(list.get(0))).getValue());
			} else if (sort.equals("#NzNat") && op.equals("sNat_")) {
				assertXMLTerm(list.size() == 1 && ((Constant) parseXML(list.get(0))).getValue().equals("0"));
				return new Constant("#Int", xml.getAttribute("number"));
			} else if (sort.equals("#Zero") && op.equals("0")) {
				assertXMLTerm(list.size() == 0);
				return new Constant("#Int", "0");
			} else if (sort.equals("#Bool") && (op.equals("true") || op.equals("false"))) {
				assertXMLTerm(list.size() == 0);
				return new Constant("#Bool", op);
			} else if (sort.equals("#Char") || sort.equals("#String")) {
				assertXMLTerm(list.size() == 0);
				return new Constant("#String", op);
			} else if (sort.equals("#FiniteFloat")) {
				assertXMLTerm(list.size() == 0);
				return new Constant("#Float", op);
			} else if (sort.equals("#Id") && op.equals("#id_")) {
				assertXMLTerm(list.size() == 1);
				String value = ((Constant) parseXML(list.get(0))).getValue();
				assertXMLTerm(value.startsWith("\"") && value.endsWith("\""));
				return new Constant("#Id", value.substring(1,value.length()-1));
			} else if (op.equals(".") && (sort.equals("Bag") || sort.equals("List") || sort.equals("Map") || sort.equals("Set") || sort.equals("K"))) {
				assertXMLTerm(list.size() == 0);
				return new Empty(sort);
			} else if (op.equals(".KList") && sort.equals(MetaK.Constants.KList)) {
				assertXMLTerm(list.size() == 0);
				return new Empty(MetaK.Constants.KList);
			} else if (op.equals("_`(_`)") && sort.equals("KItem")) {
				assertXMLTerm(list.size() == 2);
				if (list.get(0).getAttribute("sort").equals("KLabel") && list.get(0).getAttribute("op").equals("#freezer_")) {
					// TODO: Get rid of this code block when Traian fixes the Freezer class to be a KLabel again
					return parseXML(list.get(0));
				}
				return new KApp(parseXML(list.get(0)), parseXML(list.get(1)));
			} else if (sort.equals("KLabel") && list.size() == 0) {
				return new Constant("KLabel", op);
			} else if (sort.equals("KLabel") && op.equals("#freezer_")) {
				assertXMLTerm(list.size() == 1);
				return new Freezer(parseXML(list.get(0)));	
			} else if (op.equals("HOLE")) {
				assertXMLTerm(list.size() == 0);
				return new Hole(sort);
			} else {
				Set<String> conses = DefinitionHelper.labels.get(op);
				Set<String> validConses = new HashSet<String>();
				List<Term> possibleTerms = new ArrayList<Term>();
				assertXMLTerm(conses != null);
				for (String cons : conses) {
					Production p = DefinitionHelper.conses.get(cons);
					if (p.getSort().equals(sort) && p.getArity() == list.size()) {
						validConses.add(cons);
					}
				}
				assertXMLTerm(validConses.size() > 0);
				List<Term> contents = new ArrayList<Term>();
				for (Element elem : list) {
					contents.add(parseXML(elem));
				}
				for (String cons : validConses) {
					possibleTerms.add(new TermCons(sort, cons, contents));
				}
				if (possibleTerms.size() == 1) {
					return possibleTerms.get(0);
				} else {
					return new Ambiguity(sort, possibleTerms);
				}
			}
		} catch (Exception e) {
			return new BackendTerm(sort, flattenXML(xml));
		}
	}

	public static String flattenXML(Element xml) {
		List<Element> children = XmlUtil.getChildElements(xml);
		if (children.size() == 0) {
			return xml.getAttribute("op");
		} else {
			String result = xml.getAttribute("op");
			String conn = "(";
			for (Element child : children) {
				result += conn;
				conn = ",";
				result += flattenXML(child);
			}
			result += ")";
			return result;
		}
	}

	public KRunResult search(String bound, String depth, String searchType, Rule pattern, Term cfg, Set<String> varNames) throws Exception {
		String cmd = "set show command off ." + K.lineSeparator + "search ";
		if (bound != null && depth != null) {
			cmd += "[" + bound + "," + depth + "] ";
		} else if (bound != null) {
			cmd += "[" + bound + "] ";
		} else if (depth != null) {
			cmd += "[," + depth + "] ";
		}
		MaudeFilter maudeFilter = new MaudeFilter();
		cfg.accept(maudeFilter);
		cmd += maudeFilter.getResult() + " ";
		MaudeFilter patternBody = new MaudeFilter();
		pattern.getBody().accept(patternBody);
		String patternString = "=>" + searchType + " " + patternBody.getResult();
		if (pattern.getCondition() != null) {
			MaudeFilter patternCondition = new MaudeFilter();
			pattern.getCondition().accept(patternCondition);
			patternString += " such that " + patternCondition.getResult() + " = # true(.KList)";
		}
		cmd += patternString + " .";
		if (K.showSearchGraph) {
			cmd += K.lineSeparator + "show search graph .";
		}
		if (K.trace) {
			cmd = "set trace on ." + K.lineSeparator + cmd;
		}
		executeKRun(cmd, K.io);
		KRunResult result = new KRunResult(parseSearchResult(), parseRawSearchResult(), pattern, patternString.trim().matches("=>[!*1+] <_>_</_>\\(generatedTop, B:Bag, generatedTop\\)"), varNames);
		result.setRawOutput(FileUtil.getFileContent(K.maude_out));
		if (K.showSearchGraph) {
			result.setSearchGraph(p.printSearchGraph(K.processed_maude_output));
		}
		return result;
	}

	private List<Map<String, Term>> parseSearchResult() throws Exception {
		List<Map<String, Term>> results = new ArrayList<Map<String, Term>>();
		for (Map<String, Term> result : parseRawSearchResult()) {
			Map<String, Term> m = new HashMap<String, Term>();
			for (String key : result.keySet()) {
				Term searchResult = result.get(key);
				searchResult = (Term) searchResult.accept(new ConcretizeSyntax());
				searchResult = (Term) searchResult.accept(new TypeInferenceSupremumFilter());
				searchResult = (Term) searchResult.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor()));
				//as a last resort, undo concretization
				searchResult = (Term) searchResult.accept(new FlattenDisambiguationFilter());
				m.put(key, searchResult);
			}
			results.add(m);
		}
		return results;		
	}

	private List<Map<String, Term>> parseRawSearchResult() throws Exception {
		File input = new File(K.maude_output);
		Document doc = XmlUtil.readXML(input);
		NodeList list = null;
		Node nod = null;
		list = doc.getElementsByTagName("search-result");
		List<Map<String, Term>> searchResults = new ArrayList<Map<String, Term>>();
		for (int i = 0; i < list.getLength(); i++) {
			nod = list.item(i);
			assertXML(nod != null && nod.getNodeType() == Node.ELEMENT_NODE);
			Element elem = (Element) nod;
			if (elem.getAttribute("solution-number").equals("NONE")) {
				continue;
			}
			searchResults.add(new HashMap<String, Term>());
			NodeList assignments = elem.getElementsByTagName("assignment");
			for (int j = 0; j < assignments.getLength(); j++) {
				nod = assignments.item(j);
				assertXML(nod != null && nod.getNodeType() == Node.ELEMENT_NODE);
				elem = (Element) nod;
				List<Element> child = XmlUtil.getChildElements(elem);
				assertXML(child.size() == 2);
				Term result = parseXML(child.get(1));
			searchResults.get(i).put(child.get(0).getAttribute("op"), result);
			}
		}
		return searchResults;
	}

	public KRunResult modelCheck(Term formula, Term cfg) throws Exception {
		MaudeFilter formulaFilter = new MaudeFilter();
		formula.accept(formulaFilter);
		MaudeFilter cfgFilter = new MaudeFilter();
		cfg.accept(cfgFilter);

		String cmd = "mod MCK is" + K.lineSeparator + " including " + K.main_module + " ." + K.lineSeparator + K.lineSeparator + " op #initConfig : -> Bag ." + K.lineSeparator + K.lineSeparator + " eq #initConfig  =" + K.lineSeparator + cfgFilter.getResult() + " ." + K.lineSeparator + "endm" + K.lineSeparator + K.lineSeparator + "red" + K.lineSeparator + "_`(_`)(('modelCheck`(_`,_`)).KLabel,_`,`,_(_`(_`)(Bag2KLabel(#initConfig),.KList)," + K.lineSeparator + formulaFilter.getResult() + ")" + K.lineSeparator + ") .";
		executeKRun(cmd, false);
		KRunResult result = parseModelCheckResult();
		result.setRawOutput(FileUtil.getFileContent(K.maude_out));
		return result;
	}

	private KRunResult parseModelCheckResult() throws Exception {
		File input = new File(K.maude_output);
		Document doc = XmlUtil.readXML(input);
		NodeList list = null;
		Node nod = null;
		list = doc.getElementsByTagName("result");
		assertXML(list.getLength() == 1);
		nod = list.item(0);
		assertXML(nod != null && nod.getNodeType() == Node.ELEMENT_NODE);
		Element elem = (Element) nod;
		List<Element> child = XmlUtil.getChildElements(elem);
		assertXML(child.size() == 1);
		String sort = child.get(0).getAttribute("sort");
		String op = child.get(0).getAttribute("op");
		assertXML(op.equals("_`(_`)") && sort.equals("KItem"));
		child = XmlUtil.getChildElements(child.get(0));
		assertXML(child.size() == 2);
		sort = child.get(0).getAttribute("sort");
		op = child.get(0).getAttribute("op");
		assertXML(op.equals("#_") && sort.equals("KLabel"));
		sort = child.get(1).getAttribute("sort");
		op = child.get(1).getAttribute("op");
		assertXML(op.equals(".KList") && sort.equals("KList"));
		child = XmlUtil.getChildElements(child.get(0));
		assertXML(child.size() == 1);
		elem = child.get(0);
		if (elem.getAttribute("op").equals("true") && elem.getAttribute("sort").equals("#Bool")) {
			Term trueTerm = new Constant("Bool", "true");
			return new KRunResult(trueTerm, (Term)trueTerm.accept(new FlattenSyntax()));
		} else {
			sort = elem.getAttribute("sort");
			op = elem.getAttribute("op");
			assertXML(op.equals("LTLcounterexample") && sort.equals("#ModelCheckResult"));
			child = XmlUtil.getChildElements(elem);
			assertXML(child.size() == 2);
			List<Transition> initialPath = new ArrayList<Transition>();
			List<Transition> loop = new ArrayList<Transition>();
			parseCounterexample(child.get(0), initialPath);
			parseCounterexample(child.get(1), loop);
			return new KRunResult(initialPath, loop);
		}
	}

	private static void parseCounterexample(Element elem, List<Transition> list) throws Exception {
		String sort = elem.getAttribute("sort");
		String op = elem.getAttribute("op");
		List<Element> child = XmlUtil.getChildElements(elem);
		if (sort.equals("#TransitionList") && op.equals("_LTL_")) {
			assertXML(child.size() >= 2);
			for (Element e : child) {
				parseCounterexample(e, list);
			}
		} else if (sort.equals("#Transition") && op.equals("LTL`{_`,_`}")) {
			assertXML(child.size() == 2);
			Term t = parseXML(child.get(0));
		
			t = (Term) t.accept(new ConcretizeSyntax());
			t = (Term) t.accept(new TypeInferenceSupremumFilter());
			t = (Term) t.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor()));
			//as a last resort, undo concretization
			t = (Term) t.accept(new FlattenDisambiguationFilter());

			if (t.getClass() == Cell.class) {
				Cell generatedTop = (Cell) t;
				if (generatedTop.getLabel().equals("generatedTop")) {
					t = generatedTop.getContents();
				}
			}

			List<Element> child2 = XmlUtil.getChildElements(child.get(1));
			sort = child.get(1).getAttribute("sort");
			op = child.get(1).getAttribute("op");
			assertXML(child2.size() == 0 && (sort.equals("#Qid") || sort.equals("#RuleName")));
			String label = op;
			list.add(new Transition(t, label));
		} else if (sort.equals("#TransitionList") && op.equals("LTLnil")) {
			assertXML(child.size() == 0);
		} else {
			assertXML(false);
		}
	}
}
