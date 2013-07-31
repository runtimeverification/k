package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.Substitution;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;


public class FreshCondToFreshVar extends CopyOnWriteTransformer {

	private Set<Variable> vars = new HashSet<Variable>();

	public FreshCondToFreshVar(Context context) {
		super("Transform fresh conditions into fresh variables.", context);
	}

	@Override
	public ASTNode transform(Sentence node) throws TransformerException {
		//TODO:  maybe now fresh belongs in the ensures?  update this accordingly if so.
		if (null == node.getRequires())
			return node;

		vars.clear();
		ASTNode condNode = node.getRequires().accept(this);
		if (vars.isEmpty())
			return node;

		node = node.shallowCopy();
		node.setRequires((Term) condNode);

		ASTNode bodyNode = node.getBody().accept(freshSubstitution(vars));
		assert(bodyNode instanceof Term);
		node.setBody((Term)bodyNode);
		
		return node;
	}
	
	@Override
	public ASTNode transform(TermCons node) throws TransformerException {
		if (MetaK.Constants.freshCons.equals(node.getCons())) {
			if (node.getContents().size() != 1) {
				GlobalSettings.kem.register(new KException(KException.ExceptionType.WARNING,
						KException.KExceptionGroup.COMPILER,
						"Fresh has more than one argument:" + node,
						getName(), node.getFilename(), node.getLocation()));
			}
			if (!(node.getContents().get(0) instanceof Variable)) {
				GlobalSettings.kem.register(new KException(KException.ExceptionType.WARNING,
						KException.KExceptionGroup.COMPILER,
						"Fresh must take a variable as argument:" + node,
						getName(), node.getFilename(), node.getLocation()));
			}
			Variable var = (Variable) node.getContents().get(0);
			this.vars.add(var);
			return BoolBuiltin.TRUE;
		}

		return super.transform(node);
	}

	private Substitution freshSubstitution(
            Set<Variable> vars) {
		Map<Term, Term> symMap = new HashMap<Term, Term>();
		for (Variable var : vars) {
			Variable freshVar = var.shallowCopy();
			freshVar.setFresh(true);
            symMap.put(var, freshVar);
		}

		return new Substitution(symMap, context);
	}

}

