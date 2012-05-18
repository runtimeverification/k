package ro.uaic.info.fmse.k;

import java.util.LinkedList;
import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.Modifier;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.transitions.maude.MaudeHelper;
import ro.uaic.info.fmse.utils.strings.StringUtil;
import ro.uaic.info.fmse.utils.xml.XML;

public class Syntax extends ModuleItem {
	Sort sort;
	java.util.List<PriorityBlock> priorityBlocks;

	public Sort getSort() {
		return sort;
	}

	public void setSort(Sort sort) {
		this.sort = sort;
	}

	public java.util.List<PriorityBlock> getPriorityBlocks() {
		return priorityBlocks;
	}

	public void setPriorityBlocks(java.util.List<PriorityBlock> priorityBlocks) {
		this.priorityBlocks = priorityBlocks;
	}

	public Syntax(Element element) {
		super(element);

		List<Element> sorts = XML.getChildrenElementsByTagName(element, Constants.SORT);

		// assumption: sorts contains only one element
		sort = (Sort) JavaClassesFactory.getTerm(sorts.get(0));

		this.priorityBlocks = new LinkedList<PriorityBlock>();
		List<Element> priorities = XML.getChildrenElementsByTagName(element, Constants.PRIORITY);
		for (Element priority : priorities)
			priorityBlocks.add((PriorityBlock) JavaClassesFactory.getTerm(priority));
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

				if (!MaudeHelper.declaredSorts.contains(sort.toString())) {
					// contents += "sort " + sort.toString() + " . ";
					MaudeHelper.declaredSorts.add(sort.toString());
				}

				// subsort case
				if (p.items.size() == 1 && (p.items.get(0) instanceof Sort)) {
					ProductionItem item = p.items.get(0);
					if (item instanceof Sort) {
						contents += "subsort " + p.items.get(0) + " < " + sort + " .\n";
					}
				} else if (p.items.size() == 1 && (p.items.get(0) instanceof Terminal) && MaudeHelper.constantSorts.contains(sort.sort)) {
					// ignore K constants declarations
				} else if (p.items.size() == 1 && (p.items.get(0) instanceof UserList)) {
					// user declared lists case
					UserList list = (UserList) p.items.get(0);
					String metadata = (p.getMetadata() + " hybrid=()").trim();
					if (!MaudeHelper.separators.contains(list.separator)) {
						contents += "op _" + StringUtil.escape(list.separator) + "_ : K K -> K [prec 120 metadata \"" + metadata + "\"] .\n";
						contents += "op .List`{\"" + list.separator + "\"`} : -> K .\n";
						contents += "eq 'isKResult(.List`{\"" + list.separator + "\"`}) = true .\nop 'isKResult : -> KLabel [metadata \"generated-label=()\"] .\n";
						MaudeHelper.separators.add(list.separator);
					}

					contents += "op ." + sort + " : -> " + sort + " .\n";
					contents += "subsort " + list.sort + " < K .\n";
					contents += "op 'is" + list.sort + " : -> KLabel .\n";
					contents += "op 'is" + sort + " : -> KLabel .\n";
					contents += "eq 'is" + sort + "(.List`{\"" + list.separator + "\"`}) = true .\n";
					contents += "eq 'is" + sort + "(_" + StringUtil.escape(list.separator) + "_( X:" + list.sort + ", L:" + sort + " )) = true .\n";
					contents += "eq ." + sort + " = .List`{\"" + list.separator + "\"`} .\n";
				} else {
					String metadata = p.getMetadata();

					if (!p.attributes.containsKey("bracket"))
						if (metadata.equals(""))
							contents += "op " + p.getLabel() + " : " + p.toMaude() + " -> " + sort + " .\n";
						else
							contents += "op " + p.getLabel() + " : " + p.toMaude() + " -> " + sort + " [metadata \"" + metadata + "\"] .\n";
				}
			}
		}

		return contents;
	}

	@Override
	public Element toXml(Document doc) {
		Element syntax = doc.createElement(Constants.SYNTAX);

		syntax.appendChild(sort.toXml(doc));
		for (PriorityBlock pb : priorityBlocks)
			syntax.appendChild(pb.toXml(doc));

		return syntax;
	}

	@Override
	public List<String> getAllSorts() {
		List<String> sorts = new LinkedList<String>();
		sorts.add(sort.toString());
		return sorts;
	}

	@Override
	public void applyToAll(Modifier visitor) {
		sort = (Sort) visitor.modify(sort);
		for (int i = 0; i < this.priorityBlocks.size(); i++) {
			PriorityBlock elem = (PriorityBlock) visitor.modify(this.priorityBlocks.get(i));
			this.priorityBlocks.set(i, elem);
		}
	}
	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}
}
