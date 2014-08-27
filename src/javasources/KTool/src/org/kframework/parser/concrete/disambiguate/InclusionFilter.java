// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Source;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.kil.visitors.exceptions.PriorityException;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class InclusionFilter extends ParseForestTransformer {
    public InclusionFilter(String localModule, Context context) {
        super("Inclusion filter", context);
        this.localModule = localModule;
    }

    String localModule = null;

    @Override
    public ASTNode visit(TermCons tc, Void _) throws ParseFailedException {
        Source consFile = tc.getProduction().getSource();
        String consModule = tc.getProduction().getOwnerModuleName();
//        Trying to fix issue 651, by removing file inclusion check
//        String localFile = tc.getFilename();
//        if (!context.isRequiredEq(consFile, localFile)) {
//            String msg = "Production " + tc.getProduction().toString() + " has not been imported in this file.\n";
//            msg += "    Defined in module: " + consModule + " file: " + consFile;
//            KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, tc.getFilename(), tc.getLocation());
//            throw new PriorityException(kex);
//        }

        if (!context.isModuleIncludedEq(localModule, consModule)) {
            String msg = "Production " + tc.getProduction().toString() + " has not been imported in this module.\n";
            msg += "    Defined in module: " + consModule + " file: " + consFile;
            KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, tc.getSource(), tc.getLocation());
            throw new PriorityException(kex);
        }

        return super.visit(tc, _);
    }
}
