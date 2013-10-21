package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.*;
import java.util.List;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/19/12
 * Time: 10:24 PM
 */
public class AddSupercoolDefinition extends CopyOnWriteTransformer {
	private List<Rule> superCools = new ArrayList<Rule>();

	public AddSupercoolDefinition(Context context) {
		super("AddSupercoolDefinition", context);
	}

	@Override
	public ASTNode transform(Module node) throws TransformerException {
		superCools.clear();
		node = (Module) super.transform(node);
		if (!superCools.isEmpty()) {
			node = node.shallowCopy();
			node.setItems(new ArrayList<ModuleItem>(node.getItems()));
			node.getItems().addAll(superCools);
		}
		return node;
	}

	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(org.kframework.kil.Context node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		if (!node.containsAttribute(MetaK.Constants.coolingTag)) {
			return node;
		}
		if (!(node.getBody() instanceof  Rewrite)) {
			GlobalSettings.kem.register(
					new KException(KException.ExceptionType.ERROR,
							KException.KExceptionGroup.CRITICAL,
							"Cooling rules should have rewrite at the top.",
							getName(),
							node.getFilename(),
							node.getLocation())
			);
		}
		KSequence kSequence;
		Rewrite rewrite = (Rewrite) node.getBody();
		if (!(rewrite.getLeft() instanceof KSequence)) {
			GlobalSettings.kem.register(
					new KException(KException.ExceptionType.ERROR,
							KException.KExceptionGroup.CRITICAL,
							"Cooling rules should have a K sequence in the lhs.",
							getName(),
							node.getFilename(),
							node.getLocation())
			);
		}
		kSequence = (KSequence) rewrite.getLeft();
		java.util.List<Term> kSequenceContents = kSequence.getContents();
		if (kSequenceContents.size() != 2 ) {
			GlobalSettings.kem.register(
					new KException(KException.ExceptionType.ERROR,
							KException.KExceptionGroup.CRITICAL,
							"Heating/Cooling rules should have exactly 2 items in their K Sequence.",
								getName(),
								node.getFilename(),
								node.getLocation())
				);
		}
		final Term cool = kSequenceContents.get(0);
		kSequenceContents = new ArrayList<Term>(kSequenceContents);
		kSequenceContents.set(0, KApp.of(KLabelConstant.COOL_KLABEL, cool));
		kSequence = kSequence.shallowCopy();
		kSequence.setContents(kSequenceContents);
		rewrite = rewrite.shallowCopy();
		rewrite.replaceChildren(
				kSequence,
				KApp.of(KLabelConstant.COOL_KLABEL, rewrite.getRight()),
                context);
		Rule superCoolNode = node.shallowCopy();
		final Attributes attrs = new Attributes();
		attrs.getContents().addAll(node.getAttributes().getContents());
		attrs.remove("cool");
		superCoolNode.setAttributes(attrs);

		superCoolNode.setBody(rewrite);
		superCools.add(superCoolNode);
		return node;
	}

	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		return node;
	}
}
