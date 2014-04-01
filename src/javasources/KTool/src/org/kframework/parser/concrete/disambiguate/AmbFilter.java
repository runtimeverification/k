package org.kframework.parser.concrete.disambiguate;

import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class AmbFilter extends BasicTransformer {
    public AmbFilter(Context context) {
        super("Ambiguity filter", context);
    }

    public ASTNode transform(Ambiguity amb) throws TransformerException {
        String msg = "Parsing ambiguity. Arbitrarily choosing the first.";

        for (int i = 0; i < amb.getContents().size(); i++) {
            msg += "\n" + (i + 1) + ": ";
            if (amb.getContents().get(i) instanceof TermCons) {
                TermCons tc = (TermCons) amb.getContents().get(i);
                msg += tc.getProduction().getSort() + " ::= ";
                msg += tc.getProduction().toString();
            }
            UnparserFilter unparserFilter = new UnparserFilter(context);
            amb.getContents().get(i).accept(unparserFilter);
            msg += "\n   " + unparserFilter.getResult().replace("\n", "\n   ");
        }
        GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.INNER_PARSER, msg, getName(), amb.getFilename(), amb.getLocation()));

        return amb.getContents().get(0).accept(this);
    }
}
