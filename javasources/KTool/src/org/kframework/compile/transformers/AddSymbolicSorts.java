package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Module;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;


public class AddSymbolicSorts extends CopyOnWriteTransformer {

    private static final String SymbolicSortPrefix = "Symbolic";
    private static final String symbolicConstructorPrefix = "sym";

    public AddSymbolicSorts() {
        super("Add symbolic sorts and default symbolic constructors");
    }

    public final static boolean hasSymbolicSubsort(String sort) {
        // just for Bool and Int
        //return sort.equals("Bool") || sort.equals("Int");
        return !sort.startsWith(SymbolicSortPrefix);
    }

    public final static String getSymbolicSubsort(String sort) {
        assert hasSymbolicSubsort(sort);

        return SymbolicSortPrefix + sort;
    }

    public final static String getDefaultSymbolicConstructor(String sort) {
        assert hasSymbolicSubsort(sort);

        return symbolicConstructorPrefix + sort;
    }

    @Override
    public ASTNode transform(Module node) throws TransformerException {
        for (String sort : node.getAllSorts()) {
            if (hasSymbolicSubsort(sort)) {
                node.addSubsort(sort, getSymbolicSubsort(sort));
                node.addConstant("KLabel", getDefaultSymbolicConstructor(sort));
            }
        }
        return node;
    }

}

