// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.GenericToken;
import org.kframework.kil.KApp;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.Production;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class NormalizeASTTransformer extends ParseForestTransformer {

    private final KExceptionManager kem;

    public NormalizeASTTransformer(Context context, KExceptionManager kem) {
        super(NormalizeASTTransformer.class.getName(), context);
        this.kem = kem;
    }

    /**
     * A rule like P:Ptr => . when isKResult(P)
     * would create an AST where the variable P from the side condition wouldn't be wrapped
     * by a KList object. Adding a separate step which checks for exactly this case.
     */
    @Override
    public ASTNode visit(KApp kapp, Void _void) throws ParseFailedException {
        if (!kapp.getChild().getSort().equals(Sort.KLIST)) {
            kapp.setChild(new KList(kapp.getChild()));
        }
        return super.visit(kapp, _void);
    }

    /**
     * Fixing an issue where syntax like Id ::= "Main" should be automatically be transformed
     * into constants (#token). I'm letting it parse as klabel at first so I don't modify the SDF parser
     * which is unstable on modifications. After it parses I use the RemoveBrackets filter to do the post
     * processing that transforms the TermCons element into a constant. Putting it here ensures me that
     * the filter will be applied in every parser call.
     */
    @Override
    public ASTNode visit(TermCons tc, Void _void) throws ParseFailedException {
        if (context.getTokenSorts().contains(tc.getSort())) {
            Production p = tc.getProduction();
            if (p.getItems().size() == 1 && p.getItems().get(0) instanceof Terminal) {
                Terminal t = (Terminal) p.getItems().get(0);
                Term trm = GenericToken.kAppOf(p.getSort(), t.getTerminal());
                return trm;
            }
        }
        return super.visit(tc, _void);
    }

    /**
     * The rest of kompile works with these classes. The front end though needs an unified way
     * of looking at the "." productions to make it easier to disambiguate.
     */
    public ASTNode visit(ListTerminator lt, Void _void) throws ParseFailedException {
        ASTNode result = null;
        if (lt.getSort().equals(Sort.K)) {
            result = KSequence.EMPTY;
        } else if (lt.getSort().equals(Sort.KLIST)) {
            result = KList.EMPTY;
        } else if (lt.getSort().equals(Sort.BAG)) {
            result = Bag.EMPTY;
        // TODO(Radu): unfortunately, these 3 are kind of a hack. Normally should be declared directly in K
        // but at the moment because we are using SDF, I have to declare the dots directly in
        // SDF in order to avoid certain types of ambiguities.
        // with the new parser I should be able to
        } else if (lt.getSort().equals(Sort.LIST)) {
            result = KApp.of("'.List");
        } else if (lt.getSort().equals(Sort.MAP)) {
            result = KApp.of("'.Map");
        } else if (lt.getSort().equals(Sort.SET)) {
            result = KApp.of("'.Set");
        }
        if (result != null) {
            if (!lt.isUserTyped()) {
                String msg = "Inferring the sort of . as being " + lt.getSort();
                kem.register(new KException(ExceptionType.HIDDENWARNING,
                        KExceptionGroup.LISTS, msg,
                        lt.getSource(), lt.getLocation()));
            }
            return result;
        }
        // user defined empty list
        return lt;
    }
}
