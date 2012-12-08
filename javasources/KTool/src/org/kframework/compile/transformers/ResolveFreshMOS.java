package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.Substitution;
import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;


public class ResolveFreshMOS extends CopyOnWriteTransformer {

	private boolean isFresh;
	private Set<Variable> vars = new HashSet<Variable>();

	public ResolveFreshMOS() {
		super("Resolve fresh variables condition (MOS version).");
	}

	@Override
	public ASTNode transform(Sentence node) throws TransformerException {
		if (null == node.getCondition())
			return node;

		vars.clear();
		ASTNode condNode = node.getCondition().accept(this);
		if (vars.isEmpty())
			return node;

		node = node.shallowCopy();
		node.setCondition((Term) condNode);

		Variable freshVar = MetaK.getFreshVar("Int"); 
		ASTNode bodyNode = node.getBody().accept(freshSubstitution(vars, freshVar));
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
			this.isFresh = true;
			return Constant.TRUE;
		}

		return super.transform(node);
	}

	private static Substitution freshSubstitution(
            Set<Variable> vars,
            Variable idxVar) {
		Map<Term, Term> symMap = new HashMap<Term, Term>();
		int idx = 0;
		for (Variable var : vars) {
			Term symTerm = AddSymbolicK.freshSymSortN(var.getSort(),idx);
            symMap.put(var, symTerm);
		}

		return new Substitution(symMap);
	}

}

