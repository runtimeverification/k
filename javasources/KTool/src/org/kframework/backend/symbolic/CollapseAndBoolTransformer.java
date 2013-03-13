package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Constant;
import org.kframework.kil.KApp;
import org.kframework.kil.KList;
import org.kframework.kil.Term;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class CollapseAndBoolTransformer extends CopyOnWriteTransformer {

	public CollapseAndBoolTransformer() {
		super("Collapse nested conjunctions.");
	}

	@Override
	public ASTNode transform(KApp node) throws TransformerException {

		Term label = node.getLabel();
//		System.out.println("STEP: " + node);
		Term newContent = node.getChild().shallowCopy();
		if (label instanceof Constant) {
			String labelName = ((Constant) label).getValue();
			// System.out.println("LABEL: \"" + labelName + "\" == \"" +
			// Constant.ANDBOOL_KLABEL + "\" ? " +
			// labelName.trim().equals(Constant.ANDBOOL_KLABEL.getValue().trim()));

			if (labelName
					.equals(Constant.BOOL_ANDBOOL_KLABEL.getValue().trim())) {
				node = node.shallowCopy();
				node.setLabel(Constant.ANDBOOL_KLABEL);
//				System.out.println("Changed: " + node);
				return transform(node);
			}

			if (labelName.equals(Constant.ANDBOOL_KLABEL.getValue().trim())) {
				// System.out.println("DEBUG1:" + node);
				Term content = node.getChild();
				if (content instanceof KList) {
					List<Term> list = ((KList) content).getContents();
					List<Term> newList = new ArrayList<Term>();

					boolean collapsed;
					if (list != null) {
						for (Term t : list) {
							collapsed = false;
							if (t instanceof KApp) {
								KApp tapp = (KApp) t;
								Term tlabel = tapp.getLabel();
								if (tlabel instanceof Constant) {
									Constant ct = (Constant) tlabel;
									if (ct.getValue().equals(
											Constant.ANDBOOL_KLABEL.getValue()
													.trim())
											|| ct.getValue()
													.equals(Constant.BOOL_ANDBOOL_KLABEL
															.getValue().trim())) {
										// System.out.println("HERE: " + tapp);
										newList.add(tapp.getChild()
												.shallowCopy());
										collapsed = true;
									}
								}
							}
							if (!collapsed)
								newList.add(t);
						}
						newContent = new KList(newList);
					}
				} else if (content instanceof KApp) {
					// System.out.println("DEBUG2:" + node);
					Term aLabel = ((KApp) content).getLabel();
					if (aLabel instanceof Constant) {
//						System.out.println("DEBUG2:" + content);
						if (((Constant) aLabel).getValue().equals(
								Constant.ANDBOOL_KLABEL.getValue().trim())
								|| ((Constant) aLabel).getValue().equals(
										Constant.BOOL_ANDBOOL_KLABEL.getValue()
												.trim()))
//							System.out.println("HERE2: " + content);
						newContent = ((KApp) content).getChild().shallowCopy();
					}
				}
			} else {
				// System.out.println("DEBUG3:" + node);
			}
			node = node.shallowCopy();
			node.setChild(newContent);
			return node;
		}

//		System.out.println("AFTER: " + node);
		return super.transform(node);
	}
}
