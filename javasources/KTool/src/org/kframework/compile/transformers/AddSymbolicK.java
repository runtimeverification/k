package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;


public class AddSymbolicK extends CopyOnWriteTransformer {

	private static final String SymbolicConstructorPrefix = "#sym";

	public AddSymbolicK() {
		super("Add symbolic constructors");
	}

	public static final boolean allowSymbolic(String sort) {
		return sort.equals("List") || sort.equals("Set") ||
                sort.equals("Bag") || sort.equals("Map") ||
                allowKSymbolic(sort);
	}

    public static final boolean allowKSymbolic(String sort) {
        return MetaK.isComputationSort(sort) && !MetaK.isBuiltinSort(sort);
    }

    public static final String symbolicConstructor(String sort) {
		assert allowSymbolic(sort);

		if (allowKSymbolic(sort))
            return "'" + SymbolicConstructorPrefix + sort;
        else
            return SymbolicConstructorPrefix + sort;
	}

    public static final Production getSymbolicProduction(String sort) {
        assert allowSymbolic(sort);

        return Production.makeFunction(sort, symbolicConstructor(sort), "K");
    }

    public static final Term makeSymbolicTerm(String sort, Term term) {
        assert allowSymbolic(sort);

        String ctor = symbolicConstructor(sort);
        Term symTerm;
        if (!allowKSymbolic(sort)) {
            symTerm = new TermCons(sort, ctor);
            ((TermCons) symTerm).getContents().add(term);
        } else {
            Constant klbl = new Constant("KLabel", ctor);
            symTerm = new KApp(klbl, term);
        }

        return symTerm;
    }

	@Override
	public ASTNode transform(Module node) throws TransformerException {
		Module retNode = node.shallowCopy();
		retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

		for (String sort : node.getAllSorts()) {
            if (allowKSymbolic(sort)) {
                //retNode.addProduction(sort, getSymbolicProduction(sort));
                retNode.addConstant("KLabel", symbolicConstructor(sort));
            }
		}

		if (retNode.getItems().size() != node.getItems().size())
			return retNode;
		else
			return node;
	}

}

