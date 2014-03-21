package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.GenericToken;
import org.kframework.kil.Production;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;

public class CorrectConstantsTransformer extends BasicTransformer {
    public CorrectConstantsTransformer(Context context) {
        super(CorrectConstantsTransformer.class.getName(), context);
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
}
