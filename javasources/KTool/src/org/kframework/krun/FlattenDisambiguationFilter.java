package org.kframework.krun;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.List;

public class FlattenDisambiguationFilter extends CopyOnWriteTransformer {
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
