// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.AbstractTransformer;

/**
 * Created with IntelliJ IDEA.
 * User: TraianSF
 * Date: 24.05.2013
 * Time: 23:01
 *
 * Compilation Step class to initialize the configurationStructureMap and the maxLevel fields of the given Context.
 */
public class InitializeConfigurationStructure extends BasicCompilerStep<Definition> {
    public InitializeConfigurationStructure(Context context) {
        super(context);
    }

    @Override
    public Definition compile(Definition def, String stepName) throws CompilerStepDone {
        ConfigurationStructureVisitor cfgStrVisitor =
                new ConfigurationStructureVisitor(context);
        cfgStrVisitor.visitNode(def);
        context.setMaxConfigurationLevel(cfgStrVisitor.getMaxLevel());
        return def;
    }

    @Override
    public String getName() {
        return "Initiallize Configuration Structure Map";
    }
}
