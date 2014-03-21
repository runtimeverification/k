package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Bracket;
import org.kframework.kil.GenericToken;
import org.kframework.kil.Production;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Delete Bracket nodes
 */
public class RemoveBrackets extends CopyOnWriteTransformer {

    public RemoveBrackets(Context context) {
        super("Remove brackets", context);
    }

    @Override
    public ASTNode transform(Bracket node) throws TransformerException {
        // System.out.println("Remove: " + node.getFilename() + ":" + node.getLocation());
        return node.getContent().accept(this);
    }
}
