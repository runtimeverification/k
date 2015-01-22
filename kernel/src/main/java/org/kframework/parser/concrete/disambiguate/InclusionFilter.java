// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.Source;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.utils.errorsystem.PriorityException;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class InclusionFilter extends ParseForestTransformer {
    public InclusionFilter(Context context, Definition currentDefinition, Module currentModule) {
        super("Inclusion filter", context, currentDefinition, currentModule);
    }

    @Override
    public ASTNode visit(TermCons tc, Void _void) throws ParseFailedException {
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

        if (!getCurrentDefinition().getDefinitionContext().isModuleIncludedEq(getCurrentModule().getName(), consModule)) {
            String msg = "Production " + tc.getProduction().toString() + " has not been imported in this module.\n";
            msg += "    Defined in module: " + consModule + " file: " + consFile;
            KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, tc.getSource(), tc.getLocation());
            throw new PriorityException(kex);
        }

        return super.visit(tc, _void);
    }
}
