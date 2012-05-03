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
			return null;
		if (Constants.VAR.equals(element.getNodeName()))
			return new Variable(element);
		if (Constants.TERMINAL.equals(element.getNodeName()))
			return new Terminal(element);
		if (Constants.ATTRIBUTES.equals(element.getNodeName()))
			return null;
		if (Constants.TAG.equals(element.getNodeName()))
			return null;
		if (Constants.CONST.equals(element.getNodeName()))
			return new Constant(element);
		if (Constants.KAPP.equals(element.getNodeName()))
			return null;
		if (Constants.LABEL.equals(element.getNodeName()))
			return null;
		if (Constants.LISTOFK.equals(element.getNodeName()))
			return null;
		if (Constants.EMPTY.equals(element.getNodeName()))
			return new Empty(element);
		if (Constants.SET.equals(element.getNodeName()))
			return null;
		if (Constants.SETITEM.equals(element.getNodeName()))
			return null;
		if (Constants.BUILTINOP.equals(element.getNodeName()))
			return null;
		if (Constants.USERLIST.equals(element.getNodeName()))
			return new UserList(element);
		if (Constants.CONFIG.equals(element.getNodeName()))
			return new Configuration(element);
		if (Constants.CELL.equals(element.getNodeName()))
			return new Cell(element);
		if (Constants.BAG.equals(element.getNodeName()))
			return new Bag(element);
		if (Constants.KSEQUENCE.equals(element.getNodeName()))
			return new KSequence(element);
		if (Constants.MAPITEM.equals(element.getNodeName()))
			return null;
		if (Constants.KEY.equals(element.getNodeName()))
			return null;
		if (Constants.VALUE.equals(element.getNodeName()))
			return null;
		if (Constants.MAP.equals(element.getNodeName()))
			return null;
		if (Constants.CONTEXT.equals(element.getNodeName()))
			return new Context(element);
		if (Constants.HOLE.equals(element.getNodeName()))
			return null;
		if (Constants.LISTITEM.equals(element.getNodeName()))
			return null;
		if (Constants.DEFINITION.equals(element.getNodeName()))
			return new Definition(element);

		System.out.println(">>> " + element.getNodeName() + " <<< - unimplemented yet");
		return null;
	}
}
