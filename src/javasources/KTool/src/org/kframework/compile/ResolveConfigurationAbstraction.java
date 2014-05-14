// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.compile.transformers.ResolveContextAbstraction;
import org.kframework.compile.transformers.ResolveDefaultTerms;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.compile.utils.ConfigurationStructureVisitor;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/6/12
 * Time: 12:27 PM
 */
public class ResolveConfigurationAbstraction extends CompilerSteps<Definition> {

    public ResolveConfigurationAbstraction(Context context) {
        super(context);
    }

    @Override
    public Definition compile(Definition def, String stepName) throws CompilerStepDone {
        add(new ResolveContextAbstraction(context));
        add(new ResolveDefaultTerms(context));
        return super.compile(def, stepName);
    }
}
