package org.kframework.compile.transformers;

import org.kframework.compile.utils.Substitution;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Sentence;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;


public class ResolveFreshVarMOS extends CopyOnWriteTransformer {

	private Set<Variable> vars = new HashSet<Variable>();

	public ResolveFreshVarMOS(DefinitionHelper definitionHelper) {
		super("Resolve fresh variables (MOS version).", definitionHelper);
	}

	@Override
	public ASTNode transform(Sentence node) throws TransformerException {
		vars.clear();
		super.transform(node);
		if (vars.isEmpty())
			return node;

		ASTNode bodyNode = node.accept(freshSubstitution(vars));
		assert(bodyNode instanceof Sentence);

		return bodyNode;
	}
	
	@Override
	public ASTNode transform(Variable node) throws TransformerException {
		if (node.isFresh()) {
			this.vars.add(node);
			return node;
		}
		return super.transform(node);
	}

	private Substitution freshSubstitution(Set<Variable> vars) {
		Map<Term, Term> symMap = new HashMap<Term, Term>();
		int idx = 0;
		for (Variable var : vars) {
			Term symTerm = new AddSymbolicK(definitionHelper).freshSymSortN(var.getSort(definitionHelper),idx);
			idx++;
            symMap.put(var, symTerm);
		}

		return new Substitution(symMap, definitionHelper);
	}

}

