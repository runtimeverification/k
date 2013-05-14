package org.kframework.kil.loader;

import org.kframework.kil.*;
import org.spoofax.interpreter.terms.IStrategoAppl;
import org.w3c.dom.Element;

public class JavaClassesFactory {
	
	public static ASTNode getTerm(Element element) {
		// used for a new feature - loading java classes at first step (Basic Parsing)
		if (Constants.LEXICAL.equals(element.getNodeName()))
			return new Lexical(element);
		if (Constants.RESTRICTIONS.equals(element.getNodeName()))
			return new Restrictions(element);
		if (Constants.RULE.equals(element.getNodeName()) && element.hasAttribute(Constants.VALUE_value_ATTR))
			return new StringSentence(element);
		if (Constants.RULE.equals(element.getNodeName()) && element.hasAttribute(Constants.VALUE_value_ATTR))
			return new StringSentence(element);
		if (Constants.CONFIG.equals(element.getNodeName()) && element.hasAttribute(Constants.VALUE_value_ATTR))
			return new StringSentence(element);
		if (Constants.CONTEXT.equals(element.getNodeName()) && element.hasAttribute(Constants.VALUE_value_ATTR))
			return new StringSentence(element);

		if (Constants.REQUIRE.equals(element.getNodeName()))
			return new Require(element);
		if (Constants.MODULE.equals(element.getNodeName()))
			return new Module(element);
		if (Constants.IMPORT.equals(element.getNodeName()))
			return new Import(element);
		if (Constants.SYNTAX.equals(element.getNodeName()))
			return new Syntax(element);

		if (Constants.PRISENT.equals(element.getNodeName()))
			return new PriorityExtended(element);
		if (Constants.PRIASSOC.equals(element.getNodeName()))
			return new PriorityExtendedAssoc(element);
		if (Constants.PRIBLOCK.equals(element.getNodeName()))
			return new PriorityBlockExtended(element);

		if (Constants.SORT.equals(element.getNodeName()))
			return new Sort(element);
		if (Constants.PRIORITY.equals(element.getNodeName()))
			return new PriorityBlock(element);
		if (Constants.PRODUCTION.equals(element.getNodeName()))
			return new Production(element);
		if (Constants.RULE.equals(element.getNodeName()))
			return new Rule(element);
		if (Constants.REWRITE.equals(element.getNodeName()))
			return new Rewrite(element);
		if (Constants.TERM.equals(element.getNodeName()))
			return new TermCons(element);
		if (Constants.BRACKET.equals(element.getNodeName()))
			return new Bracket(element);
		if (Constants.CAST.equals(element.getNodeName()))
			return new Cast(element);
		if (Constants.VAR.equals(element.getNodeName()))
			return new Variable(element);
		if (Constants.TERMINAL.equals(element.getNodeName()))
			return new Terminal(element);
		if (Constants.CONST.equals(element.getNodeName())) {
            if (element.getAttribute(Constants.SORT_sort_ATTR).equals(KSorts.KLABEL)) {
                return new KLabelConstant(element);
            } else {
                // builtin token or lexical token
                return Token.kAppOf(element);
            }
        }
		if (Constants.KAPP.equals(element.getNodeName()))
			return new KApp(element, null);
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
		if (Constants.USERLIST.equals(element.getNodeName()))
			return new UserList(element);
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
			return new Context(element);
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
		if (Constants.MODULECOMMENT.equals(element.getNodeName()))
			return new LiterateModuleComment(element);
		if (Constants.DEFCOMMENT.equals(element.getNodeName()))
			return new LiterateDefinitionComment(element);
		if (Constants.TAG.equals(element.getNodeName()))
			return new Attribute(element);
		if (Constants.ATTRIBUTES.equals(element.getNodeName()))
			return new Attributes(element);

		System.out.println(">>> " + element.getNodeName() + " <<< - unimplemented yet: org.kframework.kil.loader.JavaClassesFactory");
		return null;
	}

	public static ASTNode getTerm(IStrategoAppl element) {
		// used for a new feature - loading java classes at first step (Basic Parsing)
		String nodeName = element.getConstructor().getName();

		if ("KSentenceList".equals(nodeName)) {
			return getTerm((IStrategoAppl) element.getSubterm(0).getSubterm(0));
		}
		if ("Config".equals(nodeName))
			return new Configuration(element);

		/*
		 * if (Constants.LEXICAL.equals(nodeName)) return new StringSentence(element); if (Constants.RESTRICTIONS.equals(nodeName)) return new StringSentence(element); if
		 * (Constants.RULE.equals(nodeName) && element.hasAttribute(Constants.VALUE_value_ATTR)) return new StringSentence(element); if (Constants.RULE.equals(nodeName) &&
		 * element.hasAttribute(Constants.VALUE_value_ATTR)) return new StringSentence(element); if (Constants.CONFIG.equals(nodeName) && element.hasAttribute(Constants.VALUE_value_ATTR)) return new
		 * StringSentence(element); if (Constants.CONTEXT.equals(nodeName) && element.hasAttribute(Constants.VALUE_value_ATTR)) return new StringSentence(element);
		 * 
		 * if (Constants.REQUIRE.equals(nodeName)) return new Require(element); if (Constants.MODULE.equals(nodeName)) return new Module(element); if (Constants.IMPORT.equals(nodeName)) return new
		 * Import(element); if (Constants.SYNTAX.equals(nodeName)) return new Syntax(element);
		 * 
		 * if (Constants.PRISENT.equals(nodeName)) return new PriorityExtended(element); if (Constants.PRIASSOC.equals(nodeName)) return new PriorityExtendedAssoc(element); if
		 * (Constants.PRIBLOCK.equals(nodeName)) return new PriorityBlockExtended(element);
		 * 
		 * if (Constants.SORT.equals(nodeName)) return new Sort(element); if (Constants.PRIORITY.equals(nodeName)) return new PriorityBlock(element); if (Constants.PRODUCTION.equals(nodeName)) return
		 * new Production(element); if (Constants.RULE.equals(nodeName)) return new Rule(element); if (Constants.REWRITE.equals(nodeName)) return new Rewrite(element); if
		 * (Constants.TERM.equals(nodeName)) return new TermCons(element); if (Constants.BRACKET.equals(nodeName)) return new Bracket(element); if (Constants.VAR.equals(nodeName)) return new
		 * Variable(element); if (Constants.TERMINAL.equals(nodeName)) return new Terminal(element); if (Constants.CONST.equals(nodeName)) return new Constant(element); if
		 * (Constants.KAPP.equals(nodeName)) return new KApp(element); if (Constants.LISTOFK.equals(nodeName)) return new KList(element); if (Constants.EMPTY.equals(nodeName)) return new
		 * Empty(element); if (Constants.SET.equals(nodeName)) return new Set(element); if (Constants.SETITEM.equals(nodeName)) return new SetItem(element); if (Constants.USERLIST.equals(nodeName))
		 * return new UserList(element); if (Constants.CELL.equals(nodeName)) return new Cell(element); if (Constants.BREAK.equals(nodeName)) return new TermComment(element); if
		 * (Constants.BAG.equals(nodeName)) return new Bag(element); if (Constants.BAGITEM.equals(nodeName)) return new BagItem(element); if (Constants.KSEQUENCE.equals(nodeName)) return new
		 * KSequence(element); if (Constants.MAPITEM.equals(nodeName)) return new MapItem(element); if (Constants.MAP.equals(nodeName)) return new Map(element); if (Constants.CONTEXT.equals(nodeName))
		 * return new Context(element); if (Constants.HOLE.equals(nodeName)) return new Hole(element); if (Constants.FREEZERHOLE.equals(nodeName)) return new FreezerHole(element); if
		 * (Constants.LISTITEM.equals(nodeName)) return new ListItem(element); if (Constants.LIST.equals(nodeName)) return new List(element); if (Constants.DEFINITION.equals(nodeName)) return new
		 * Definition(element); if (Constants.AMB.equals(nodeName)) return new Ambiguity(element); if (Constants.MODULECOMMENT.equals(nodeName)) return new LiterateModuleComment(element); if
		 * (Constants.DEFCOMMENT.equals(nodeName)) return new LiterateDefinitionComment(element); if (Constants.TAG.equals(nodeName)) return new Attribute(element); if
		 * (Constants.ATTRIBUTES.equals(nodeName)) return new Attributes(element);
		 */
		System.out.println(">>> " + nodeName + " <<< - unimplemented yet: org.kframework.kil.loader.JavaClassesFactory");
		return null;
	}
}
