package org.kframework.krun.api;

import org.kframework.backend.unparser.AddBracketsFilter;
import org.kframework.backend.unparser.AddBracketsFilter2;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.krun.ConcretizeSyntax;
import org.kframework.krun.FlattenDisambiguationFilter;
import org.kframework.krun.K;
import org.kframework.krun.SubstitutionFilter;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;

import java.io.Serializable;

public class KRunState implements Serializable{

	private Term result;
	private Term rawResult;
	private Integer stateId;
	
	protected DefinitionHelper definitionHelper;

	public KRunState(Term rawResult, DefinitionHelper definitionHelper) {
		this.definitionHelper = definitionHelper;
		this.rawResult = rawResult;
		this.result = concretize(rawResult, definitionHelper);
	}

	public static Term concretize(Term result, DefinitionHelper definitionHelper) {
		Term rawResult = result;
		try {
			result = (Term) result.accept(new ConcretizeSyntax(definitionHelper));
			result = (Term) result.accept(new TypeInferenceSupremumFilter(definitionHelper));
			result = (Term) result.accept(new FlattenDisambiguationFilter(definitionHelper));
			if (!K.parens) {
				result = (Term) result.accept(new AddBracketsFilter(definitionHelper));
				AddBracketsFilter2 filter = new AddBracketsFilter2(definitionHelper);
				result = (Term) result.accept(filter);
				while (true) {
					Term newResult = (Term) result.accept(new SubstitutionFilter(filter.substitution, definitionHelper));
					if (newResult.equals(result)) {
						break;
					}
					result = newResult;
				}
			}
		} catch (Exception e) {
			// if concretization fails, return the raw result directly.
			//return rawResult;s
			throw new RuntimeException(e);
		}
		if (result.getClass() == Cell.class) {
			Cell generatedTop = (Cell) result;
			if (generatedTop.getLabel().equals("generatedTop")) {
				result = generatedTop.getContents();
			}
		}

		return result;
	}
	
	public KRunState(Term rawResult, int stateId, DefinitionHelper definitionHelper) {
		this(rawResult, definitionHelper);
		this.stateId = stateId;
	}

	@Override
	public String toString() {
		if (stateId == null) {
			UnparserFilter unparser = new UnparserFilter(true, K.color, K.parens, definitionHelper);
			result.accept(unparser);
			return unparser.getResult();
		} else {
			return "Node " + stateId;
		}
	}

	public Term getResult() {
		return result;
	}

	public Term getRawResult() {
		return rawResult;
	}

	public Integer getStateId() {
		return stateId;
	}

	public void setStateId(Integer stateId) {	
		this.stateId = stateId;
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof KRunState)) return false;
		KRunState s = (KRunState)o;
		return rawResult.equals(s.rawResult);
	}

	@Override
	public int hashCode() {
		return rawResult.hashCode();
	}
}
