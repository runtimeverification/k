// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.compile.checks.CheckVariables;
import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.compile.transformers.AddInjections;
import org.kframework.compile.transformers.AddKCell;
import org.kframework.compile.transformers.AddTopCellRules;
import org.kframework.compile.transformers.Cell2DataStructure;
import org.kframework.compile.transformers.FlattenTerms;
import org.kframework.compile.transformers.RemoveBrackets;
import org.kframework.compile.transformers.RemoveSyntacticCasts;
import org.kframework.compile.transformers.ResolveAnonymousVariables;
import org.kframework.compile.transformers.ResolveContextAbstraction;
import org.kframework.compile.transformers.ResolveListOfK;
import org.kframework.compile.transformers.ResolveOpenCells;
import org.kframework.compile.transformers.ResolveRewrite;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.compile.utils.CompileDataStructures;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.kil.Module;
import org.kframework.kil.loader.Context;
import org.kframework.utils.errorsystem.KExceptionManager;


/**
 * @author: AndreiS
 */
public class SpecificationCompilerSteps extends CompilerSteps<Module> {

    private final KExceptionManager kem;

    public SpecificationCompilerSteps(Context context, KExceptionManager kem) {
        super(context);
        this.kem = kem;

        //add(new CheckVisitorStep<Definition>(new CheckConfigurationCells(context), context));
        add(new RemoveBrackets(context));
        add(new AddEmptyLists(context, kem));
        add(new RemoveSyntacticCasts(context));
        add(new CheckVisitorStep<Module>(new CheckVariables(context, kem), context));
        //add(new CheckVisitorStep<Definition>(new CheckRewrite(context), context));

        add(new AddKCell(context));
        add(new AddTopCellRules(context));
        add(new ResolveAnonymousVariables(context));
        add(new ResolveListOfK(context));
        add(new AddInjections(context));
        add(new FlattenTerms(context));
        add(new ResolveContextAbstraction(context, kem));
        add(new ResolveOpenCells(context));
        add(new ResolveRewrite(context));
        add(new Cell2DataStructure(context));
        add(new CompileDataStructures(context, kem));
        //add(new DataStructureToLookupUpdate(context));
    }

}
