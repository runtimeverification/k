package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/19/12
 * Time: 3:02 PM
 */
public class AddHeatingConditions extends CopyOnWriteTransformer {
	public AddHeatingConditions(org.kframework.kil.loader.Context context) {
		super("Generate Heating Conditions", context);
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

		final boolean heating = node.containsAttribute(MetaK.Constants.heatingTag);
		final boolean cooling = node.containsAttribute(MetaK.Constants.coolingTag);
		if (!(heating || cooling))
			return node;
		Term kresultCnd = null;
		if (!(node.getBody() instanceof  Rewrite)) {
			GlobalSettings.kem.register(
					new KException(KException.ExceptionType.ERROR,
							KException.KExceptionGroup.CRITICAL,
							"Heating/Cooling rules should have rewrite at the top.",
							getName(),
							node.getFilename(),
							node.getLocation())
			);
		}
		KSequence kSequence;
		Rewrite rewrite = (Rewrite) node.getBody();
		if (heating) {
			if (!(rewrite.getRight() instanceof KSequence)) {
				GlobalSettings.kem.register(
						new KException(KException.ExceptionType.ERROR,
								KException.KExceptionGroup.CRITICAL,
								"Heating rules should have a K sequence in the rhs.",
								getName(),
								node.getFilename(),
								node.getLocation())
				);
			}
			kSequence = (KSequence) rewrite.getRight();
		} else {
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
		}
		if (kSequence.getContents().size() != 2 ) {
			GlobalSettings.kem.register(
					new KException(KException.ExceptionType.ERROR,
							KException.KExceptionGroup.CRITICAL,
							"Heating/Cooling rules should have exactly 2 items in their K Sequence.",
								getName(),
								node.getFilename(),
								node.getLocation())
				);
		}
		java.util.Set<Variable> vars = kSequence.getContents().get(0).variables();
		if (vars.size() != 1) {
			GlobalSettings.kem.register(
					new KException(KException.ExceptionType.ERROR,
							KException.KExceptionGroup.CRITICAL,
							"Heating/Cooling rules should heat/cool at most one variable.",
							getName(),
							node.getFilename(),
							node.getLocation())
			);
		}
		Variable variable = vars.iterator().next();
		final KApp isKResult = KApp.of(KLabelConstant.KRESULT_PREDICATE, variable);
		if (heating) {
			kresultCnd = KApp.of(KLabelConstant.KNEQ_KLABEL, isKResult, BoolBuiltin.TRUE);
		} else {
			kresultCnd = isKResult;
		}
		node = node.shallowCopy();
		Term condition = MetaK.incrementCondition(node.getCondition(), kresultCnd, context);

		node.setCondition(condition);
		return node;
	}

	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		return node;
	}
}
