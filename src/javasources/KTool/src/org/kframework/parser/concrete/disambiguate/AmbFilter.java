// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.FloatBuiltin;
import org.kframework.kil.GenericToken;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.Sort;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class AmbFilter extends ParseForestTransformer {
    public AmbFilter(Context context) {
        super("Ambiguity filter", context);
    }

    @Override
    public ASTNode visit(Ambiguity amb, Void _) throws ParseFailedException {
        String msg = "Parsing ambiguity. Arbitrarily choosing the first.";

        for (int i = 0; i < amb.getContents().size(); i++) {
            msg += "\n" + (i + 1) + ": ";
            if (amb.getContents().get(i) instanceof TermCons) {
                TermCons tc = (TermCons) amb.getContents().get(i);
                msg += tc.getProduction().getSort() + " ::= ";
                msg += tc.getProduction().toString();
            } else if (amb.getContents().get(i) instanceof KApp) {
                // TODO: RaduM. For the new parser this will be a class called Constant which
                // points exactly to the production that generates the constant
                KApp kApp = (KApp) amb.getContents().get(i);
                if (kApp.getLabel() instanceof GenericToken) {
                    GenericToken gt = (GenericToken) kApp.getLabel();
                    msg += "Constant of type " + gt.tokenSort();
                } else if (kApp.getLabel() instanceof StringBuiltin) {
                    msg += "Constant of type " + Sort.BUILTIN_STRING;
                } else if (kApp.getLabel() instanceof BoolBuiltin) {
                    msg += "Constant of type " + Sort.BUILTIN_BOOL;
                } else if (kApp.getLabel() instanceof FloatBuiltin) {
                    msg += "Constant of type " + Sort.BUILTIN_FLOAT;
                } else if (kApp.getLabel() instanceof IntBuiltin) {
                    msg += "Constant of type " + Sort.BUILTIN_INT;
                }
            }
            UnparserFilter unparserFilter = new UnparserFilter(context);
            unparserFilter.visitNode(amb.getContents().get(i));
            msg += "\n   " + unparserFilter.getResult().replace("\n", "\n   ");
        }
        GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.INNER_PARSER, msg, getName(), amb.getSource(), amb.getLocation()));

        return this.visitNode(amb.getContents().get(0));
    }
}
