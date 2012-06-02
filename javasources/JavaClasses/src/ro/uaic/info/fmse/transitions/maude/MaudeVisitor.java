package ro.uaic.info.fmse.transitions.maude;

import java.util.HashSet;
import java.util.Set;

import ro.uaic.info.fmse.k.Definition;
import ro.uaic.info.fmse.k.DefinitionItem;
import ro.uaic.info.fmse.k.Import;
import ro.uaic.info.fmse.k.Module;
import ro.uaic.info.fmse.k.ModuleItem;
import ro.uaic.info.fmse.k.PriorityBlock;
import ro.uaic.info.fmse.k.Syntax;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.visitors.BasicVisitor;

public class MaudeVisitor extends BasicVisitor {

	private String maudified = "";
	private String contents = "";
	private Set<String> declaredSorts = new HashSet<String>();
	
	
	public void visit(Definition node) {
		String uris = "";
		for (DefinitionItem di : node.getItems()) {
			// if (di instanceof Module && ((Module)di).name.equals("URIS"))
			// uris = di.toMaude();
			// else
			di.accept(this);
			// content += di.toMaude() + " \n";
		}

		// klabels
		String klabels = "";
		KLabelsVisitor labelsVisitor = new KLabelsVisitor();
		labelsVisitor.visit(node);
		for (String kl : labelsVisitor.kLabels) {
			klabels += kl + " ";
		}
		klabels = klabels.trim();
		if (!klabels.equals(""))
			klabels = "  ops " + klabels + " : -> KLabel .\n";

		// cellLabels visitor
		String cellLabels = "";
		CellLabelsVisitor cellLabelsVisitor = new CellLabelsVisitor();
		cellLabelsVisitor.visit(node);
		for (String cellLabel : cellLabelsVisitor.cellLabels) {
			cellLabels += cellLabel + " ";
		}
		cellLabels = cellLabels.trim();
		if (!cellLabels.equals(""))
			cellLabels = "  ops " + cellLabels + " : -> CellLabel .\n";

		// sorts & automatic subsortation to K
		String sorts = "";
		for (String s : declaredSorts) {
			if (!MaudeHelper.basicSorts.contains(s))
				sorts += s + " ";
		}
		sorts = sorts.trim();
		if (!sorts.equals(""))
			sorts = "  sorts " + sorts + " .\n  subsorts " + sorts + " < K .\n";

		String shared = "mod " + Constants.SHARED + " is\n  including K .\n"
				+ klabels + sorts + cellLabels + "\nendm";

		setMaudified(uris + "\n" + shared + "\n" + contents);
	}

	@Override
	public void visit(Module node) {
		if (!node.getType().equals("interface")) {

			node.getItems().add(0, new Import(Constants.SHARED));
			if (!node.isPredefined())
				node.getItems().add(0, new Import("URIS"));

			contents += "mod " + node.getName() + " is\n";
			for (ModuleItem mi : node.getItems()) {
				// content += mi.toMaude() + "\n";
				mi.accept(this);
			}

			contents += "\nendm\n";
		}
	}

	
	@Override
	public void visit(Syntax node) {
		for (PriorityBlock pb : node.getPriorityBlocks()) {
			pb.accept(this);
		}
	}
	
	
	public String getMaudified() {
		return maudified;
	}

	public void setMaudified(String maudified) {
		this.maudified = maudified;
	};
}
