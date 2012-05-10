package ro.uaic.info.fmse.loader;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.k.*;
import ro.uaic.info.fmse.parsing.ASTNode;

public class JavaClassesFactory {

	public static ASTNode getTerm(Element element) {
		if (Constants.MODULE.equals(element.getNodeName()))
			return new Module(element);
		if (Constants.IMPORT.equals(element.getNodeName()))
			return new Import(element);
		if (Constants.SYNTAX.equals(element.getNodeName()))
			return new Syntax(element);
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
			return new TermCons(element, false);
		if (Constants.VAR.equals(element.getNodeName()))
			return new Variable(element);
		if (Constants.TERMINAL.equals(element.getNodeName()))
			return new Terminal(element);
		if (Constants.CONST.equals(element.getNodeName()))
			return new Constant(element);
		if (Constants.KAPP.equals(element.getNodeName()))
			return new KApp(element);
		if (Constants.LISTOFK.equals(element.getNodeName()))
			return new ListOfK(element);
		if (Constants.EMPTY.equals(element.getNodeName()))
			return new Empty(element);
		if (Constants.SET.equals(element.getNodeName()))
			return new Set(element);
		if (Constants.SETITEM.equals(element.getNodeName()))
			return new SetItem(element);
		if (Constants.BUILTINOP.equals(element.getNodeName()))
			return new TermCons(element, true);
		if (Constants.USERLIST.equals(element.getNodeName()))
			return new UserList(element);
		if (Constants.CONFIG.equals(element.getNodeName()))
			return new Configuration(element);
		if (Constants.CELL.equals(element.getNodeName()))
			return new Cell(element);
		if (Constants.BAG.equals(element.getNodeName()))
			return new Bag(element);
		if (Constants.BAGITEM.equals(element.getNodeName()))
			return new BagItem(element);
		if (Constants.KSEQUENCE.equals(element.getNodeName()))
			return new KSequence(element);
		if (Constants.MAPITEM.equals(element.getNodeName()))
			return new MapItem(element);
		if (Constants.MAP.equals(element.getNodeName()))
			return new Map(element);
		if (Constants.CONTEXT.equals(element.getNodeName()))
			return new Context(element);
		if (Constants.HOLE.equals(element.getNodeName()))
			return new Hole(element);
		if (Constants.LISTITEM.equals(element.getNodeName()))
			return new ListItem(element);
		if (Constants.LIST.equals(element.getNodeName()))
			return new List(element);
		if (Constants.DEFINITION.equals(element.getNodeName()))
			return new Definition(element);

		System.out.println(">>> " + element.getNodeName() + " <<< - unimplemented yet: JavaClassesFactory");
		return null;
	}
}
