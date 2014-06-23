// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.compile.transformers.AddKCell;
import org.kframework.compile.transformers.AddTopCellRules;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.transformers.RemoveBrackets;
import org.kframework.compile.transformers.RemoveSyntacticCasts;
import org.kframework.compile.transformers.ResolveAnonymousVariables;
import org.kframework.compile.transformers.ResolveContextAbstraction;
import org.kframework.compile.transformers.ResolveListOfK;
import org.kframework.compile.transformers.ResolveOpenCells;
import org.kframework.compile.transformers.ResolveRewrite;
import org.kframework.compile.utils.CompileDataStructures;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.kil.Module;
import org.kframework.kil.loader.Context;


/**
 * @author: AndreiS
 */
public class SpecificationCompilerSteps extends CompilerSteps<Module> {

    public SpecificationCompilerSteps(Context context) {
        super(context);

        //add(new CheckVisitorStep<Definition>(new CheckConfigurationCells(context), context));
        add(new RemoveBrackets(context));
        add(new AddEmptyLists(context));
        add(new RemoveSyntacticCasts(context));
        //add(new CheckVisitorStep<Definition>(new CheckVariables(context), context));
        //add(new CheckVisitorStep<Definition>(new CheckRewrite(context), context));

        add(new AddKCell(context));
        add(new AddTopCellRules(context));
        add(new ResolveAnonymousVariables(context));
        add(new ResolveListOfK(context));
        add(new FlattenSyntax(context));
        add(new ResolveContextAbstraction(context));
        add(new ResolveOpenCells(context));
        add(new ResolveRewrite(context));
        add(new CompileDataStructures(context));
        //add(new DataStructureToLookupUpdate(context));
    }

}
