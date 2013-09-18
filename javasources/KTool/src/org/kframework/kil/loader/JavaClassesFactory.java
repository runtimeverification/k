package org.kframework.kil.loader;

import java.util.ArrayList;
import java.util.HashMap;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.Bag;
import org.kframework.kil.BagItem;
import org.kframework.kil.Bracket;
import org.kframework.kil.Cast;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.kil.Empty;
import org.kframework.kil.FreezerHole;
import org.kframework.kil.Hole;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.KSorts;
import org.kframework.kil.Lexical;
import org.kframework.kil.List;
import org.kframework.kil.ListItem;
import org.kframework.kil.Map;
import org.kframework.kil.MapItem;
import org.kframework.kil.ParseError;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.Set;
import org.kframework.kil.SetItem;
import org.kframework.kil.Term;
import org.kframework.kil.TermComment;
import org.kframework.kil.TermCons;
import org.kframework.kil.Token;
import org.kframework.kil.Variable;
import org.kframework.utils.StringUtil;
import org.w3c.dom.Element;

import aterm.ATerm;
import aterm.ATermAppl;
import aterm.ATermList;

/**
 * Factory for creating KIL classes from XML nodes or ATerms. Must call startConstruction/endConstruction around calls to getTerm, to supply a Context.
 */
public class JavaClassesFactory {
	private static Context context = null;

	/** Set the context to use */
	public static synchronized void startConstruction(Context context) {
		assert JavaClassesFactory.context == null;
		JavaClassesFactory.context = context;
	}

	public static synchronized void endConstruction() {
		assert JavaClassesFactory.context != null;
		JavaClassesFactory.context = null;
	}

	public static ASTNode getTerm(Element element) {
		assert context != null;
		// used for a new feature - loading java classes at first step (Basic Parsing)
		if (Constants.RULE.equals(element.getNodeName()))
			return new Rule(element);
		if (Constants.SENTENCE.equals(element.getNodeName()))
			return new Sentence(element);
		if (Constants.REWRITE.equals(element.getNodeName()))
			return new Rewrite(element);
		if (Constants.TERM.equals(element.getNodeName())) {
			assert context != null;
			return new TermCons(element, context);
		}
		if (Constants.BRACKET.equals(element.getNodeName()))
			return new Bracket(element);
		if (Constants.CAST.equals(element.getNodeName()))
			return new Cast(element);
		if (Constants.VAR.equals(element.getNodeName()))
			return new Variable(element);
		if (Constants.CONST.equals(element.getNodeName())) {
			if (element.getAttribute(Constants.SORT_sort_ATTR).equals(KSorts.KLABEL)) {
				return new KLabelConstant(element);
			} else {
				// builtin token or lexical token
				return Token.kAppOf(element);
			}
		}
		if (Constants.KAPP.equals(element.getNodeName()))
			return new KApp(element, context);
		if (KSorts.KLIST.equals(element.getNodeName()))
			return new KList(element);
		if (Constants.EMPTY.equals(element.getNodeName())) {
			if (element.getAttribute(Constants.SORT_sort_ATTR).equals(KSorts.K)) {
				return KSequence.EMPTY;
			} else if (element.getAttribute(Constants.SORT_sort_ATTR).equals(KSorts.KLIST)) {
				return KList.EMPTY;
			} else if (element.getAttribute(Constants.SORT_sort_ATTR).equals(KSorts.BAG)) {
				return Bag.EMPTY;
			} else if (element.getAttribute(Constants.SORT_sort_ATTR).equals(KSorts.LIST)) {
				return List.EMPTY;
			} else if (element.getAttribute(Constants.SORT_sort_ATTR).equals(KSorts.MAP)) {
				return Map.EMPTY;
			} else if (element.getAttribute(Constants.SORT_sort_ATTR).equals(KSorts.SET)) {
				return Set.EMPTY;
			} else {
				// user defined empty list
				return new Empty(element);
			}
		}
		if (KSorts.SET.equals(element.getNodeName()))
			return new Set(element);
		if (KSorts.SET_ITEM.equals(element.getNodeName()))
			return new SetItem(element);
		if (Constants.CONFIG.equals(element.getNodeName()))
			return new Configuration(element);
		if (Constants.CELL.equals(element.getNodeName()))
			return new Cell(element);
		if (Constants.BREAK.equals(element.getNodeName()))
			return new TermComment(element);
		if (KSorts.BAG.equals(element.getNodeName()))
			return new Bag(element);
		if (KSorts.BAG_ITEM.equals(element.getNodeName()))
			return new BagItem(element);
		if (Constants.KSEQUENCE.equals(element.getNodeName()))
			return new KSequence(element);
		if (KSorts.MAP.equals(element.getNodeName()))
			return new Map(element);
		if (KSorts.MAP_ITEM.equals(element.getNodeName()))
			return new MapItem(element);
		if (Constants.CONTEXT.equals(element.getNodeName()))
			return new org.kframework.kil.Context(element);
		if (Constants.HOLE.equals(element.getNodeName()))
			return Hole.KITEM_HOLE;
		if (Constants.FREEZERHOLE.equals(element.getNodeName()))
			return new FreezerHole(element);
		if (KSorts.LIST.equals(element.getNodeName()))
			return new List(element);
		if (KSorts.LIST_ITEM.equals(element.getNodeName()))
			return new ListItem(element);
		if (Constants.DEFINITION.equals(element.getNodeName()))
			return new Definition(element);
		if (Constants.AMB.equals(element.getNodeName()))
			return new Ambiguity(element);
		if (Constants.TAG.equals(element.getNodeName()))
			return new Attribute(element);
		if (Constants.ATTRIBUTES.equals(element.getNodeName()))
			return new Attributes(element);

		System.out.println(">>> " + element.getNodeName() + " <<< - unimplemented yet: org.kframework.kil.loader.JavaClassesFactory");
		return null;
	}

	private static java.util.Map<Integer, ASTNode> cache = new HashMap<Integer, ASTNode>();

	public static void clearCache() {
		cache.clear();
	}

	private static ASTNode storeNode(Integer key, ASTNode node) {
		cache.put(key, node);
		return node;
	}

	public static ASTNode getTerm(ATerm atm) {
		assert context != null;

		if (cache.containsKey(atm.getUniqueIdentifier())) {
			ASTNode node = cache.get(atm.getUniqueIdentifier());
			// System.out.println(atm.getUniqueIdentifier() + " = " + node);
			return node;
		}

		if (atm.getType() == ATerm.APPL) {
			ATermAppl appl = (ATermAppl) atm;
			// used for a new feature - loading java classes at first step (Basic Parsing)

			// if (Constants.RULE.endsWith(appl.getNodeName()))
			// return new Rule(appl);
			// if (Constants.CONFIG.endsWith(appl.getNodeName()))
			// return new Configuration(appl);
			// if (Constants.DEFINITION.endsWith(appl.getNodeName()))
			// return new Definition(appl);
			// if (Constants.TAG.endsWith(appl.getNodeName()))
			// return new Attribute(appl);
			// if (Constants.ATTRIBUTES.endsWith(appl.getNodeName()))
			// return new Attributes(appl);
			// if (Constants.CONTEXT.endsWith(appl.getNodeName()))
			// return new Context(appl);

			if (appl.getName().endsWith("Ensures"))
				return storeNode(atm.getUniqueIdentifier(), new Sentence(appl));
			if (appl.getName().endsWith("Rewrite"))
				return storeNode(atm.getUniqueIdentifier(), new Rewrite(appl));
			if (appl.getName().endsWith("Syn")) {
				if (appl.getName().endsWith("ListSyn") && appl.getArgument(0) instanceof ATermList) {
					ATermList list = (ATermList) appl.getArgument(0);
					TermCons head = null;
					TermCons tc = null;
					while (!list.isEmpty()) {
						TermCons ntc = new TermCons(StringUtil.getSortNameFromCons(appl.getName()), appl.getName(), context);
						ntc.setLocation(appl.getAnnotations().getFirst().toString().substring(8));
						ntc.setContents(new ArrayList<Term>());
						ntc.getContents().add((Term) JavaClassesFactory.getTerm(list.getFirst()));
						if (tc == null) {
							head = ntc;
						} else {
							tc.getContents().add(ntc);
						}
						tc = ntc;
						list = list.getNext();
					}
					if (tc != null)
						tc.getContents().add(new Empty(StringUtil.getSortNameFromCons(appl.getName())));
					else
						return storeNode(atm.getUniqueIdentifier(), new Empty(StringUtil.getSortNameFromCons(appl.getName())));
					return storeNode(atm.getUniqueIdentifier(), head);
				} else
					return storeNode(atm.getUniqueIdentifier(), new TermCons(appl, context));
			}
			if (appl.getName().endsWith("Bracket"))
				return storeNode(atm.getUniqueIdentifier(), new Bracket(appl));
			if (appl.getName().endsWith("Cast"))
				return storeNode(atm.getUniqueIdentifier(), new Cast(appl));
			if (appl.getName().endsWith("Hole"))
				return Hole.KITEM_HOLE;
			if (appl.getName().endsWith("Var"))
				return new Variable(appl);
			if (appl.getName().endsWith("Const")) {
				String sort = StringUtil.getSortNameFromCons(appl.getName());
				if (sort.equals(KSorts.KLABEL)) {
					return storeNode(atm.getUniqueIdentifier(), new KLabelConstant(appl));
				} else {
					// builtin token or lexical token
					return storeNode(atm.getUniqueIdentifier(), Token.kAppOf(appl));
				}
			}
			if (appl.getName().equals("K1App"))
				return storeNode(atm.getUniqueIdentifier(), new KApp(appl));
			if (appl.getName().endsWith("Empty")) {
				String sort = StringUtil.getSortNameFromCons(appl.getName());
				if (sort.equals(KSorts.K)) {
					return KSequence.EMPTY;
				} else if (sort.equals(KSorts.KLIST)) {
					return KList.EMPTY;
				} else if (sort.equals(KSorts.BAG)) {
					return Bag.EMPTY;
				} else if (sort.equals(KSorts.LIST)) {
					return List.EMPTY;
				} else if (sort.equals(KSorts.MAP)) {
					return Map.EMPTY;
				} else if (sort.equals(KSorts.SET)) {
					return Set.EMPTY;
				} else {
					// user defined empty list
					return new Empty(appl);
				}
			}
			if (appl.getName().endsWith("Item")) {
				String sort = StringUtil.getSortNameFromCons(appl.getName());
				if (sort.equals("SetItem"))
					return storeNode(atm.getUniqueIdentifier(), new SetItem(appl));
				else if (sort.equals("BagItem"))
					return storeNode(atm.getUniqueIdentifier(), new BagItem(appl));
				else if (sort.equals("ListItem"))
					return storeNode(atm.getUniqueIdentifier(), new ListItem(appl));
				else if (sort.equals("MapItem"))
					return storeNode(atm.getUniqueIdentifier(), new MapItem(appl));
			}

			if (appl.getName().endsWith("List")) {
				String sort = StringUtil.getSortNameFromCons(appl.getName());
				if (sort.equals("Set"))
					return storeNode(atm.getUniqueIdentifier(), new Set(appl));
				else if (sort.equals("Bag"))
					return storeNode(atm.getUniqueIdentifier(), new Bag(appl));
				else if (sort.equals("List"))
					return storeNode(atm.getUniqueIdentifier(), new List(appl));
				else if (sort.equals("KList"))
					return storeNode(atm.getUniqueIdentifier(), new KList(appl));
				else if (sort.equals("Map"))
					return storeNode(atm.getUniqueIdentifier(), new Map(appl));
			}
			if (appl.getName().endsWith("K1Seq"))
				return storeNode(atm.getUniqueIdentifier(), new KSequence(appl));
			if (appl.getName().equals("Bag1ClosedCell"))
				return storeNode(atm.getUniqueIdentifier(), new Cell(appl));
			if (appl.getName().equals("BagItem1Break"))
				return storeNode(atm.getUniqueIdentifier(), new TermComment(appl));

			// if (Constants.FREEZERHOLE.endsWith(appl.getNodeName()))
			// return new FreezerHole(appl);
			if (Constants.AMB.equals(appl.getName()))
				return storeNode(atm.getUniqueIdentifier(), new Ambiguity(appl));
			if (Constants.ERROR.equals(appl.getName()))
				return storeNode(atm.getUniqueIdentifier(), new ParseError(appl));
		}
		System.out.println(">>> " + atm + " <<< - unimplemented yet: org.kframework.kil.loader.JavaClassesFactory");
		return null;
	}
}
