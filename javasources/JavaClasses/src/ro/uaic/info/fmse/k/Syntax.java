package ro.uaic.info.fmse.k;

import java.util.LinkedList;
import java.util.List;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.transitions.maude.MaudeHelper;
import ro.uaic.info.fmse.utils.strings.StringUtil;
import ro.uaic.info.fmse.utils.xml.XML;

public class Syntax extends ModuleItem {
	Sort sort;
	java.util.List<PriorityBlock> priorityBlocks;

	public Syntax(Element element) {
		super(element);

		List<Element> sorts = XML.getChildrenElementsByTagName(element,
				Constants.SORT);

		// assumption: sorts contains only one element
		sort = (Sort) JavaClassesFactory.getTerm(sorts.get(0));

		this.priorityBlocks = new LinkedList<PriorityBlock>();
		List<Element> priorities = XML.getChildrenElementsByTagName(element,
				Constants.PRIORITY);
		for (Element priority : priorities)
			priorityBlocks.add((PriorityBlock) JavaClassesFactory
					.getTerm(priority));
	}

	@Override
	public String toString() {
		String blocks = "";

		for (PriorityBlock pb : priorityBlocks) {
			blocks += pb + "\n> ";
		}
		if (blocks.length() > 2)
			blocks = blocks.substring(0, blocks.length() - 3);

		return "  syntax " + sort + " ::= " + blocks + "\n";
	}

	@Override
	public String toMaude() {

		String contents = "";
		for (PriorityBlock pb : priorityBlocks) {
			for (Production p : pb.productions) {
				// subsort case
				if (p.items.size() == 1 && (p.items.get(0) instanceof Sort)) {
					ProductionItem item = p.items.get(0);
					if (item instanceof Sort)
						contents += "subsort " + p.items.get(0) + " < " + sort
								+ " .\n";
				} else if (p.items.size() == 1
						&& (p.items.get(0) instanceof UserList)) {
					// user declared lists case
					UserList list = (UserList) p.items.get(0);
					String metadata = (p.getMetadata() + " hybrid=()").trim();
					if (!MaudeHelper.separators.contains(list.separator)) {
						contents += "op _" + StringUtil.escape(list.separator)
								+ "_ : K K -> K [prec 120 metadata=\""
								+ metadata + "\"] .\n";
						contents += "op .List`{\"" + list.separator
								+ "\"`} : -> K .\n";
						contents += "eq 'isKResult(.List`{\""
								+ list.separator
								+ "\"`}) = true .\nop 'isKResult : -> KLabel [metadata \"generated-label=()\"] .\n";
						MaudeHelper.separators.add(list.separator);
					}
					
					contents += "subsort "+list.sort+" < K .\n";
					contents += "op 'is"+list.sort+" : -> KLabel .\n";
					contents += "eq 'is"+list.sort+"(.List`{\""+list.separator+"\"`}) = true .\n";
					contents += "eq 'is"+list.sort+"(_" + StringUtil.escape(list.separator) + "_( X:" + sort + ", L:" + list.sort + " )) = true .\n";
				} else {
					String metadata = p.getMetadata();
					
					if (metadata.equals(""))
						contents += "op " + p.getLabel() + " : " + p.toMaude()
							+ " -> " + sort + " .\n";
					else contents += "op " + p.getLabel() + " : " + p.toMaude()
							+ " -> " + sort + " [metadata \"" + metadata + "\"] .\n";
				}
			}
		}

		return contents;
	}
}
