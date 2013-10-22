package org.kframework.krun.api;

import org.kframework.backend.unparser.AddBracketsFilter;
import org.kframework.backend.unparser.AddBracketsFilter2;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.ConcretizeSyntax;
import org.kframework.krun.FlattenDisambiguationFilter;
import org.kframework.krun.K;
import org.kframework.krun.SubstitutionFilter;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.io.Serializable;
import java.io.IOException;

public class KRunState implements Serializable{

	/**
	The pretty-printed term associated with this state, as suitable for display
	*/
	private Term result;

	/**
	The raw term associated with this state, as suitable for further rewriting
	*/
	private Term rawResult;
	private Integer stateId;
	
	protected Context context;

	public KRunState(Term rawResult, Context context) {
		this.context = context;
		this.rawResult = rawResult;
	}

	public static Term concretize(Term result, Context context) {
		Term rawResult = result;
		try {
			result = (Term) result.accept(new ConcretizeSyntax(context));
			result = (Term) result.accept(new TypeInferenceSupremumFilter(context));
			result = (Term) result.accept(new FlattenDisambiguationFilter(context));
			if (!K.parens) {
				result = (Term) result.accept(new AddBracketsFilter(context));
				try {
					AddBracketsFilter2 filter = new AddBracketsFilter2(context);
					result = (Term) result.accept(filter);
					while (true) {
						Term newResult = (Term) result.accept(new SubstitutionFilter(filter.substitution, context));
						if (newResult.equals(result)) {
							break;
						}
						result = newResult;
					}
				} catch (IOException e) {
					GlobalSettings.kem.register(new KException(
						ExceptionType.WARNING,
						KExceptionGroup.INTERNAL,
						"Could not load parser: brackets may be unsound"));
				}
			}
		} catch (TransformerException e) {
			assert false : "Concretization threw a TransformerException";
		}
		if (result.getClass() == Cell.class) {
			Cell generatedTop = (Cell) result;
			if (generatedTop.getLabel().equals("generatedTop")) {
				result = generatedTop.getContents();
			}
		}

		return result;
	}
	
	public KRunState(Term rawResult, int stateId, Context context) {
		this(rawResult, context);
		this.stateId = stateId;
	}

	@Override
	public String toString() {
		if (stateId == null) {
			UnparserFilter unparser = new UnparserFilter(true, K.color, K.parens, context);
			getResult().accept(unparser);
			return unparser.getResult();
		} else {
			return "Node " + stateId;
		}
	}

	public Term getResult() {
		if (result == null) {
			result = concretize(rawResult, context);
		}
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
