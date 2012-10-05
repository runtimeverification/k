package org.kframework.kil;

import java.util.LinkedList;
import java.util.List;

import org.kframework.compile.utils.MaudeHelper;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Modifier;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.utils.strings.StringUtil;
import org.kframework.utils.utils.xml.XML;
import org.w3c.dom.Element;

public class Syntax extends ModuleItem {
	Sort sort;
	java.util.List<PriorityBlock> priorityBlocks;

	public Syntax(Sort sort, java.util.List<PriorityBlock> priorities) {
		super();
		this.sort = sort;
		this.priorityBlocks = priorities;
	}

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

	public Syntax(Syntax node) {
		super(node);
		this.sort = node.sort;
		this.priorityBlocks = node.priorityBlocks;
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

				// if (!MaudeHelper.declaredSorts.contains(sort.toString())) {
				// MaudeHelper.declaredSorts.add(sort.toString());
				// }

				// subsort case
				if (p.items.size() == 1 && (p.items.get(0) instanceof Sort)) {
					ProductionItem item = p.items.get(0);
					if (item instanceof Sort) {
						if (!MaudeHelper.declaredSorts.contains(p.items.get(0).toString()) && !MaudeHelper.basicSorts.contains(p.items.get(0).toString())) {
							contents += "sort " + p.items.get(0) + " .\n";
							MaudeHelper.declaredSorts.add(p.items.get(0).toString());
						}
						contents += "subsort " + p.items.get(0) + " < " + sort + " .\n";
					}
				} else if (p.items.size() == 1 && (p.items.get(0) instanceof Terminal) && MaudeHelper.constantSorts.contains(sort.getName())) {

					String metadata = p.getAttributes().toMaude();
					String operation = p.toString().replaceAll("\"", "");

					if (operation.equals("")) {
						GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot declare empty terminal.", p.getFilename(), p.getLocation()));
						continue;
					}
					if (sort.toString().equals("KLabel") || sort.toString().equals("CellLabel"))
						if (!metadata.trim().equals(""))
							contents += "op " + operation + ": -> " + sort + " [metadata \"" + metadata + "\"] .\n";
						else
							contents += "op " + operation + ": -> " + sort + " .\n";
					// ignore K constants declarations
				} else if (p.items.size() == 1 && (p.items.get(0) instanceof UserList)) {
					// user declared lists case
					UserList list = (UserList) p.items.get(0);
					String metadata = (p.getAttributes().toMaude() + " hybrid=()").trim();
					metadata += " location=" + p.getMaudeLocation();
					if (!MaudeHelper.separators.contains(list.separator)) {
						contents += "op _" + StringUtil.escape(list.separator) + "_ : K K -> K [prec 120 metadata \"" + metadata + "\"] .\n";
						contents += "op .List`{\"" + list.separator + "\"`} : -> K .\n";
						contents += "eq isKResult(.List`{\"" + list.separator + "\"`}) = true .\n";
						MaudeHelper.separators.add(list.separator);
					}

					contents += "op ." + sort + " : -> " + sort + " .\n";
					contents += "subsort " + list.sort + " < K .\n";
					contents += "op is" + list.sort + " : -> KLabel .\n";
					contents += "op is" + sort + " : -> KLabel .\n";
					contents += "eq is" + sort + "(.List`{\"" + list.separator + "\"`}) = true .\n";
					contents += "eq is" + sort + "(_" + StringUtil.escape(StringUtil.equationSpaceElimination(list.separator)) + "_( X:" + list.sort + ", L:" + sort + " )) = true .\n";
					contents += "eq ." + sort + " = .List`{\"" + list.separator + "\"`} .\n";
				} else {
					String metadata = p.getAttributes().toMaude();
					metadata += " location=" + p.getMaudeLocation();

					String maudelabel = p.getLabel().replaceAll("` ", "`");

					if (maudelabel.equals("")) {
						GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.COMPILER, "Empty production. Please use `prefixlabel` attribute.", p.getFilename(), p.getLocation()));
						continue;
					}

					if (!p.attributes.containsKey("bracket"))
						if (metadata.equals(""))
							contents += "op " + maudelabel + " : " + p.toMaude() + " -> " + sort + " .\n";
						else
							contents += "op " + maudelabel + " : " + p.toMaude() + " -> " + sort + " [metadata \"" + metadata + "\"] .\n";
				}
			}
		}

		return contents;
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

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == null)
			return false;
		if (this == obj)
			return true;
		if (!(obj instanceof Syntax))
			return false;
		Syntax syn = (Syntax) obj;

		if (!syn.getSort().equals(this.sort))
			return false;

		if (syn.priorityBlocks.size() != priorityBlocks.size())
			return false;

		for (int i = 0; i < syn.priorityBlocks.size(); i++) {
			if (!syn.priorityBlocks.get(i).equals(priorityBlocks.get(i)))
				return false;
		}

		return true;
	}

	@Override
	public int hashCode() {
		int hash = sort.hashCode();

		for (PriorityBlock pb : priorityBlocks)
			hash += pb.hashCode();
		return hash;
	}

	@Override
	public Syntax shallowCopy() {
		return new Syntax(this);
	}
}
