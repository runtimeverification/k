package org.kframework.backend.symbolic;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;

/**
 * Created with IntelliJ IDEA.
 * User: andrei.arusoaie
 * Date: 12/2/13
 * Time: 11:32 AM
 * To change this template use File | Settings | File Templates.
 */
public class AddPCToBagVariable extends CopyOnWriteTransformer {

    private Cell pc;
    private String B;

    public AddPCToBagVariable(Context context, Cell pc, String B) {
        super("Concatenate path condition cell to given Bag (variable)", context);
        this.pc = pc;
        this.B = B;
    }

    public ASTNode transform(Variable node) throws TransformerException {
        if (node.getName().equals(B)) {
            Bag bag = new Bag();
            java.util.List<Term> contents = new ArrayList<Term>();
            contents.add(node.shallowCopy());
            contents.add(pc);
            bag.setContents(contents);
            return bag;
        }

        return super.transform(node);    //To change body of overridden methods use File | Settings | File Templates.
    }
}
