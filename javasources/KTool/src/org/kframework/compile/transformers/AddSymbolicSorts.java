package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Production;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;


public class AddSymbolicSorts extends CopyOnWriteTransformer {

	private static final String SymbolicSortPrefix = "Symbolic";
	private static final String SymbolicConstructorPrefix = "sym";
    private static final String SymbolicConstructorArgumentSort = "Int";

	public AddSymbolicSorts() {
		super("Add symbolic sorts and default symbolic constructors");
	}

	public static final boolean hasSymbolicSubsort(String sort) {
		// just for Bool and Int
		//return sort.equals("Bool") || sort.equals("Int");
		return MetaK.isComputationSort(sort) &&
                !sort.startsWith(SymbolicSortPrefix);
	}

	public static final String getSymbolicSubsort(String sort) {
		assert hasSymbolicSubsort(sort);

		return SymbolicSortPrefix + sort;
	}

	public static final String getDefaultSymbolicConstructor(String sort) {
		assert hasSymbolicSubsort(sort);

		return SymbolicConstructorPrefix + sort;
	}

    public static final Production getDefaultSymbolicProduction(String sort) {
        assert hasSymbolicSubsort(sort);

        return Production.makeFunction(
                getSymbolicSubsort(sort),
                getDefaultSymbolicConstructor(sort),
                SymbolicConstructorArgumentSort);
    }

	@Override
	public ASTNode transform(Module node) throws TransformerException {
		Module retNode = node.shallowCopy();
		retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

		for (String sort : node.getAllSorts()) {
			if (hasSymbolicSubsort(sort)) {
				String symSort = getSymbolicSubsort(sort);
				retNode.addSubsort(sort, symSort);
                Production symProd = getDefaultSymbolicProduction(sort);
				retNode.addProduction(symSort, symProd);
			}
		}

		if (retNode.getItems().size() != node.getItems().size())
			return retNode;
		else
			return node;
	}

}

