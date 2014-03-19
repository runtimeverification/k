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

    /**
     * Fixing an issue where syntax like Id ::= "Main" should be automatically be transformed
     * into constants (#token). I'm letting it parse as klabel at first so I don't modify the SDF parser
     * which is unstable on modifications. After it parses I use the RemoveBrackets filter to do the post
     * processing that transforms the TermCons element into a constant. Putting it here ensures me that
     * the filter will be applied in every parser call.
     */
    @Override
    public ASTNode transform(TermCons tc) throws TransformerException {
        if (context.getTokenSorts().contains(tc.getSort())) {
            Production p = (Production) tc.getProduction();
            if (p.getItems().size() == 1 && p.getItems().get(0) instanceof Terminal) {
                Terminal t = (Terminal) p.getItems().get(0);
                Term trm = GenericToken.kAppOf(p.getSort(), t.getTerminal());
                trm.setFilename(tc.getFilename());
                trm.setLocation(tc.getLocation());
                return trm;
            }
        }
        return super.transform(tc);
    }

    @Override
    public ASTNode transform(Bracket node) throws TransformerException {
        // System.out.println("Remove: " + node.getFilename() + ":" + node.getLocation());
        return node.getContent().accept(this);
    }
}
