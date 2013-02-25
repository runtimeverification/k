package org.kframework.krun.api;

import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.*;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitTypeCheckVisitor;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;

public class KRunState {

	private Term result;
	private Term rawResult;
	private Integer stateId;

	public KRunState(Term rawResult) {
		this.rawResult = rawResult;
		this.result = concretize(rawResult);
	}

	public static Term concretize(Term result) {
		Term rawResult = result;
		try {
			result = (Term) result.accept(new ConcretizeSyntax());
			result = (Term) result.accept(new TypeInferenceSupremumFilter());
			result = (Term) result.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor()));
			//as a last resort, undo concretization
			result = (Term) result.accept(new FlattenDisambiguationFilter());
		} catch (Exception e) {
			// if concretization fails, return the raw result directly.
			return rawResult;
		}
		if (result.getClass() == Cell.class) {
			Cell generatedTop = (Cell) result;
			if (generatedTop.getLabel().equals("generatedTop")) {
				result = generatedTop.getContents();
			}
		}

		return result;
	}	

	private static class FlattenDisambiguationFilter extends CopyOnWriteTransformer {
		public FlattenDisambiguationFilter() {
			super("Reflatten ambiguous syntax");
		}

		@Override
		public ASTNode transform(Ambiguity amb) throws TransformerException {
			if (amb.getContents().get(0) instanceof TermCons) {
				TermCons t1 = (TermCons)amb.getContents().get(0);
				if (MetaK.isComputationSort(t1.getSort())) {
					return new KApp(new Constant("KLabel", t1.getProduction().getKLabel()), (Term) new KList(t1.getContents()).accept(this));
				}
			} else if (amb.getContents().get(0) instanceof Empty) {
				Empty t1 = (Empty)amb.getContents().get(0);
				if (MetaK.isComputationSort(t1.getSort())) {
					return new KApp(new Constant("KLabel", MetaK.getListUnitLabel(((UserList)DefinitionHelper.listConses.get(t1.getSort()).getItems().get(0)).getSeparator())), new Empty(MetaK.Constants.KList));
				}
			}
			return amb;
		}
	}

	public KRunState(Term rawResult, int stateId) {
		this(rawResult);
		this.stateId = stateId;
	}

	@Override
	public String toString() {
		if (stateId == null) {
			UnparserFilter unparser = new UnparserFilter(true, K.color);
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
