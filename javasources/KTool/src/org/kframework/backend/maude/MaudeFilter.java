package org.kframework.backend.maude;

import org.kframework.compile.utils.MaudeHelper;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map.Entry;

public class MaudeFilter extends BasicVisitor {
	protected java.lang.StringBuilder result;
	private boolean firstAttribute;

	public MaudeFilter() {
		result = new java.lang.StringBuilder();
	}

	public String getResult() {
		return result.toString();
	}

	@Override
	public void visit(Definition def) {
		for (DefinitionItem di : def.getItems()) {
			di.accept(this);
			result.append(" \n");
		}
	}

	@Override
	public void visit(Import imp) {
		result.append("including ");
		result.append(imp.getName());
		result.append(" .");
	}

	@Override
	public void visit(Module mod) {
		if (!mod.getType().equals("interface")) {
			result.append("mod ");
			result.append(mod.getName());
			result.append(" is\n");
			for (ModuleItem mi : mod.getItems()) {
				mi.accept(this);
				result.append("\n");
			}
			result.append("\nendm");
		}
	}

	@Override
	public void visit(PriorityExtended syn) {
	}

	@Override
	public void visit(Syntax syn) {
		for (PriorityBlock pb : syn.getPriorityBlocks()) {
			for (Production p : pb.getProductions()) {
				if (p.getItems().size() == 1 && (p.getItems().get(0) instanceof Sort)) {
					// sub-sort case
					ProductionItem item = p.getItems().get(0);
					if (item instanceof Sort) {
						if (!MaudeHelper.declaredSorts.contains(p.getItems().get(0).toString()) && !MaudeHelper.basicSorts.contains(p.getItems().get(0).toString())) {
							result.append("sort ");
							result.append(p.getItems().get(0));
							result.append(" .\n");
							MaudeHelper.declaredSorts.add(p.getItems().get(0).toString());
						}
						result.append("subsort ");
						result.append(p.getItems().get(0));
						result.append(" < ");
						result.append(syn.getSort());
						result.append(" .\n");
					}
				} else if (p.getItems().size() == 1 && (p.getItems().get(0) instanceof Terminal)) {
					String operation = p.toString();
					if (operation.startsWith("\"")) {
						operation = operation.substring(1, operation.length() - 2);
					}
					if (operation.equals("") && !p.containsAttribute("onlyLabel")) {
						String msg = "Cannot declare empty terminals in the definition.\n";
						msg += "            Use attribute 'onlyLabel' paired with 'klabel(...)' to limit the use to programs.";
						GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, p.getFilename(), p.getLocation()));
					}
					if (!MaudeHelper.constantSorts.contains(syn.getSort()) || !syn.getSort().toString().equals("KLabel") || !syn.getSort().toString().equals("CellLabel")) {
						result.append("op ");
						result.append(operation);
						result.append(" : -> ");
						result.append(syn.getSort());
						if (!isEmptyAttributes(p.getAttributes())) {
							result.append(" [metadata \"");
							p.getAttributes().accept(this);
							result.append("\"]");
						}
						result.append(" .\n");
					}
					// ignore K constants declarations
				} else if (p.getItems().size() == 1 && (p.getItems().get(0) instanceof UserList)) {
					// user declared lists case
					UserList list = (UserList) p.getItems().get(0);
					if (!MaudeHelper.separators.contains(list.getSeparator())) {
						result.append("op _");
						result.append(StringUtil.escapeMaude(list.getSeparator()));
						result.append("_ : K K -> K [prec 120 metadata \"");
						p.getAttributes().accept(this);
						result.append(" hybrid=()");
						result.append(" location=");
						result.append(p.getMaudeLocation());
						result.append("\"] .\n");
						result.append("op .List`{\"");
						result.append(list.getSeparator());
						result.append("\"`} : -> K .\n");
						MaudeHelper.separators.add(list.getSeparator());
					}
				} else {
					String maudelabel = p.getLabel();
					if (maudelabel.equals("")) {
						String msg = "Empty production. Please use `prefixlabel` attribute.";
						GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.COMPILER, msg, p.getFilename(), p.getLocation()));
						continue;
					}

					if (!p.containsAttribute("bracket")) {
						result.append("op ");
						result.append(maudelabel);
						result.append(" : ");
						p.accept(this);
						result.append(" -> ");
						result.append(syn.getSort());
						// if (!isEmptyAttributes(p.getCellAttributes())) {
						result.append(" [metadata \"");
						p.getAttributes().accept(this);
						result.append(" location=");
						result.append(p.getMaudeLocation());
						result.append("\"]");
						// }
						result.append(" .\n");
					}
				}
			}
		}
	}

	@Override
	public void visit(PriorityExtendedAssoc priorityBlock) {
	}

	@Override
	public void visit(PriorityBlock priorityBlock) {
		result.append("production");
	}

	@Override
	public void visit(Production prod) {
		boolean first = true;
		for (ProductionItem pi : prod.getItems()) {
			if (!first) {
				result.append(" ");
			} else {
				first = false;
			}
			if (pi.getType().equals(ProductionType.SORT)) {
				pi.accept(this);
			}
		}
	}

	@Override
	public void visit(Sort sort) {
		result.append(sort.getName());
	}

	@Override
	public void visit(Terminal terminal) {
		// do nothing
	}

	@Override
	public void visit(StringSentence stringSentence) {
		result.append("StringSentence should not be maudifiable");
	}

	@Override
	public void visit(UserList userList) {
		// do nothing
	}

	@Override
	public void visit(ListOfK listOfK) {
		this.visit((Collection) listOfK);
		// throw new RuntimeException("don't know how to maudify ListOfK");
	}

	@Override
	public void visit(Attributes attributes) {
		firstAttribute = true;
		for (Attribute entry : attributes.getContents()) {
			// Andrei S: for some reason I do not understand, location and
			// filename are special attributes
			if (!entry.getKey().equals("klabel")) { // && !entry.getKey().equals("location") && !entry.getKey().equals("filename")) {
				entry.accept(this);
			}
		}
	}

	private boolean isEmptyAttributes(Attributes attributes) {
		for (Attribute entry : attributes.getContents()) {
			if (!entry.getKey().equals("klabel") && !entry.getKey().equals("location") && !entry.getKey().equals("filename")) {
				if (!isEmptyAttribute(entry)) {
					return false;
				}
			}
		}
		return true;
	}

	private boolean isEmptyAttribute(Attribute entry) {
		java.util.List<String> reject = new LinkedList<String>();
		reject.add("cons");
		reject.add("kgeneratedlabel");
		reject.add("latex");
		reject.add("prefixlabel");

		if (!reject.contains(entry.getKey())) {
			return false;
		}
		return true;
	}

	@Override
	public void visit(Attribute attribute) {
		java.util.List<String> reject = new LinkedList<String>();
		reject.add("cons");
		reject.add("kgeneratedlabel");
		reject.add("latex");
		reject.add("prefixlabel");

		if (!reject.contains(attribute.getKey())) {
			if (!firstAttribute) {
				result.append(" ");
			} else {
				firstAttribute = false;
			}
			result.append(attribute.getKey());
			result.append("=(");
			result.append(attribute.getValue());
			result.append(")");
		}
	}

	@Override
	public void visit(Configuration configuration) {
		// result.append("mb configuration ");
		// this.visit((Sentence)configuration);
	}

	@Override
	public void visit(Cell cell) {
		String cellLabel = "<_>_</_>";

		result.append(cellLabel);
		result.append("(");
		for (Entry<String, String> entry : cell.getCellAttributes().entrySet()) {
			if (!entry.getValue().equals("")) {
				result.append("__(");
			}
		}
		result.append(cell.getLabel());
		for (Entry<String, String> entry : cell.getCellAttributes().entrySet()) {
			if (!entry.getValue().equals("")) {
				result.append(",_=_(");
				result.append(entry.getKey());
				result.append(",\"");
				result.append(entry.getValue());
				result.append("\"))");
			}
		}
		result.append(", ");
		if (cell.getContents() != null) {
			cell.getContents().accept(this);
		} else {
			result.append("null");
		}
		result.append(", ");
		result.append(cell.getLabel());
		result.append(")");
	}

	@Override
	public void visit(Variable variable) {
		if (variable.getName().equals("_")) {
			result.append("?");
		} else {
			result.append(variable.getName());
		}
		result.append(":");
		result.append(variable.getSort());
	}

	@Override
	public void visit(Empty empty) {
		String sort = empty.getSort();
		if (MaudeHelper.basicSorts.contains(sort)) {
			if (!sort.equals("List{K}")) {
				result.append("(.).");
				result.append(sort);
			} else {
				result.append(".");
				result.append(sort);
			}
		} else {
			Production prd = DefinitionHelper.listConses.get(sort);
			UserList ul = (UserList) prd.getItems().get(0);
			result.append(".List`{\"");
			result.append(ul.getSeparator());
			result.append("\"`}");
		}
	}

	@Override
	public void visit(Rule rule) {
		result.append("mb rule ");
		this.visit((Sentence) rule);
	}

	@Override
	public void visit(KApp kapp) {
		result.append("_`(_`)(");
		kapp.getLabel().accept(this);
		result.append(", ");
		kapp.getChild().accept(this);
		result.append(") ");
	}

	@Override
	public void visit(KSequence ksequence) {
		this.visit((Collection) ksequence);
		// throw new RuntimeException("don't know how to maudify KSequence");
	}

	@Override
	public void visit(TermCons termCons) {
		Production pr = DefinitionHelper.conses.get(termCons.getCons());
		String cons = pr.getLabel();

		if (pr.containsAttribute("maudeop")) {
			cons = pr.getAttribute("maudeop").replaceAll("\"", "");
		}

		result.append(cons.replaceAll(" ", "`"));
		if (termCons.getContents().size() > 0) {
			result.append("(");
		}
		boolean first = true;
		for (Term term : termCons.getContents()) {
			if (!first) {
				result.append(",");
			} else {
				first = false;
			}
			if (term != null) {
				term.accept(this);
			} else {
				result.append("null");
			}
		}
		if (termCons.getContents().size() > 0) {
			result.append(")");
		}
	}

	@Override
	public void visit(Sentence sentence) {
		sentence.getBody().accept(this);
		result.append(" ");
		if (sentence.getCondition() != null) {
			result.append("when ");
			sentence.getCondition().accept(this);
		}

		result.append(" : KSentence [");
		if (sentence instanceof Rule) {
			Rule rule = (Rule) sentence;
			if (rule.getLabel() != null && !rule.getLabel().equals("")) {
				result.append("label " + rule.getLabel() + " metadata");
			} else {
				result.append("metadata");
			}
		} else {
			result.append("metadata");
		}
		result.append(" \"");
		sentence.getAttributes().accept(this);
		result.append(" location=");
		result.append(sentence.getMaudeLocation());
		result.append("\"] .");
	}

	@Override
	public void visit(Rewrite rewrite) {
		result.append("_=>_(");
		if (rewrite.getLeft() == null) {
			result.append("null");
		} else {
			rewrite.getLeft().accept(this);
		}
		result.append(",");
		if (rewrite.getRight() == null) {
			result.append("null");
		} else {
			rewrite.getRight().accept(this);
		}
		result.append(")");

	}

	@Override
	public void visit(Constant constant) {
		if (constant.getSort().equals("#Id")) {
			result.append("#id \"");
		}
		result.append(constant.getValue());
		if (constant.getSort().equals("#Id")) {
			result.append("\"");
		}
	}

	@Override
	public void visit(Collection collection) {
		if (collection.getContents().size() == 0) {
			new Empty(collection.getSort()).accept(this);
		} else if (collection.getContents().size() == 1) {
			collection.getContents().get(0).accept(this);
		} else {
			String constructor = getMaudeConstructor(collection.getSort());
			result.append(constructor);
			result.append("(");

			boolean first = true;
			for (Term term : collection.getContents()) {
				if (!first) {
					result.append(",");
				} else {
					first = false;
				}
				if (term == null) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "NULL Term encountered when MaudeFilter ran on collection " + collection.getContents()
							+ ".", collection.getFilename(), collection.getLocation()));
				}
				term.accept(this);
			}

			result.append(")");
		}
	}

	@Override
	public void visit(CollectionItem collectionItem) {
		throw new RuntimeException("don't know how to maudify CollectionItem");
	}

	@Override
	public void visit(BagItem bagItem) {
		result.append("BagItem(");
		bagItem.getItem().accept(this);
		result.append(")");
	}

	@Override
	public void visit(ListItem listItem) {
		result.append("ListItem(");
		listItem.getItem().accept(this);
		result.append(")");
	}

	@Override
	public void visit(SetItem setItem) {
		result.append("SetItem(");
		setItem.getItem().accept(this);
		result.append(")");
	}

	@Override
	public void visit(MapItem mapItem) {
		result.append("_|->_(");
		mapItem.getKey().accept(this);
		result.append(",");
		mapItem.getValue().accept(this);
		result.append(")");
	}

	@Override
	public void visit(Hole hole) {
		result.append("HOLE");
	}

	@Override
	public void visit(KInjectedLabel kInjectedLabel) {
		Term term = kInjectedLabel.getTerm();
		if (MetaK.isKSort(term.getSort())) {
			result.append(StringUtil.escapeMaude(kInjectedLabel.getInjectedSort(term.getSort())));
			result.append("2KLabel_(");
		} else {
			result.append("#_(");
		}
		term.accept(this);
		result.append(")");
	}

	@Override
	public void visit(KLabel kLabel) {
		throw new RuntimeException("don't know how to maudify KLabel");
	}

	@Override
	public void visit(TermComment termComment) {
		result.append(" (.).Bag ");
	}

	@Override
	public void visit(org.kframework.kil.List list) {
		this.visit((Collection) list);
		// throw new RuntimeException("don't know how to maudify List");
	}

	@Override
	public void visit(org.kframework.kil.Map map) {
		this.visit((Collection) map);
		// throw new RuntimeException("don't know how to maudify Map");
	}

	@Override
	public void visit(Bag bag) {
		this.visit((Collection) bag);
		// throw new RuntimeException("don't know how to maudify Bag");
	}

	@Override
	public void visit(org.kframework.kil.Set set) {
		this.visit((Collection) set);
		// throw new RuntimeException("don't know how to maudify Set");
	}

	@Override
	public void visit(org.kframework.kil.Ambiguity ambiguity) {
		result.append("amb(");
		boolean first = true;
		for (Term term : ambiguity.getContents()) {
			if (!first) {
				result.append(",");
			} else {
				first = false;
			}
			if (term != null) {
				term.accept(this);
			} else {
				result.append("null");
			}
		}
		result.append(")");
	}

	@Override
	public void visit(org.kframework.kil.Context context) {
		result.append("mb context ");
		this.visit((Sentence) context);
	}

	@Override
	public void visit(LiterateDefinitionComment literateDefinitionComment) {
		// do nothing
	}

	@Override
	public void visit(LiterateModuleComment literateModuleComment) {
		// do nothing
	}

	@Override
	public void visit(org.kframework.kil.Require require) {
		// do nothing
	}

	private static java.util.Map<KSort, String> maudeCollectionConstructors = new HashMap<KSort, String>();
	static {
		maudeCollectionConstructors.put(KSort.Bag, "__");
		maudeCollectionConstructors.put(KSort.Map, "__");
		maudeCollectionConstructors.put(KSort.Set, "__");
		maudeCollectionConstructors.put(KSort.List, "__");
		maudeCollectionConstructors.put(KSort.K, "_~>_");
		maudeCollectionConstructors.put(KSort.ListOfK, "_`,`,_");
	}

	public static String getMaudeConstructor(String sort) {
		return maudeCollectionConstructors.get(KSort.getKSort(sort));
	}
}
