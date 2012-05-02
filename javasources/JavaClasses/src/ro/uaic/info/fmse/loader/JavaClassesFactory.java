package ro.uaic.info.fmse.loader;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.k.Definition;
import ro.uaic.info.fmse.k.Import;
import ro.uaic.info.fmse.k.Module;
import ro.uaic.info.fmse.k.PriorityBlock;
import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.k.Sort;
import ro.uaic.info.fmse.k.Syntax;
import ro.uaic.info.fmse.k.Terminal;
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
			return null;
		if (Constants.BODY.equals(element.getNodeName()))
			return null;
		if (Constants.REWRITE.equals(element.getNodeName()))
			return null;
		if (Constants.LEFT.equals(element.getNodeName()))
			return null;
		if (Constants.TERM.equals(element.getNodeName()))
			return null;
		if (Constants.VAR.equals(element.getNodeName()))
			return null;
		if (Constants.RIGHT.equals(element.getNodeName()))
			return null;
		if (Constants.TERMINAL.equals(element.getNodeName()))
			return new Terminal(element);
		if (Constants.ATTRIBUTES.equals(element.getNodeName()))
			return null;
		if (Constants.TAG.equals(element.getNodeName()))
			return null;
		if (Constants.CONST.equals(element.getNodeName()))
			return null;
		if (Constants.KAPP.equals(element.getNodeName()))
			return null;
		if (Constants.LABEL.equals(element.getNodeName()))
			return null;
		if (Constants.LISTOFK.equals(element.getNodeName()))
			return null;
		if (Constants.EMPTY.equals(element.getNodeName()))
			return null;
		if (Constants.SET.equals(element.getNodeName()))
			return null;
		if (Constants.SETITEM.equals(element.getNodeName()))
			return null;
		if (Constants.COND.equals(element.getNodeName()))
			return null;
		if (Constants.BUILTINOP.equals(element.getNodeName()))
			return null;
		if (Constants.USERLIST.equals(element.getNodeName()))
			return null;
		if (Constants.CONFIG.equals(element.getNodeName()))
			return null;
		if (Constants.CELL.equals(element.getNodeName()))
			return null;
		if (Constants.BAG.equals(element.getNodeName()))
			return null;
		if (Constants.KSEQUENCE.equals(element.getNodeName()))
			return null;
		if (Constants.MAPITEM.equals(element.getNodeName()))
			return null;
		if (Constants.KEY.equals(element.getNodeName()))
			return null;
		if (Constants.VALUE.equals(element.getNodeName()))
			return null;
		if (Constants.MAP.equals(element.getNodeName()))
			return null;
		if (Constants.CONTEXT.equals(element.getNodeName()))
			return null;
		if (Constants.HOLE.equals(element.getNodeName()))
			return null;
		if (Constants.LISTITEM.equals(element.getNodeName()))
			return null;
		if (Constants.DEFINITION.equals(element.getNodeName()))
			return new Definition(element);

		return null;
	}
}
