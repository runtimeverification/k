// Copyright (c) 2010-2014 K Team. All Rights Reserved.
package org.kframework.krun;

import java.util.List;

import org.kframework.kil.Attributes;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.transformation.AmbiguousTransformationException;
import org.kframework.transformation.Transformation;
import org.kframework.transformation.TransformationNotSatisfiedException;
import org.kframework.transformation.TransformationProvider;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.DefinitionLoadingModule;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.Main;

import com.google.common.collect.ImmutableList;
import com.google.inject.Inject;
import com.google.inject.Module;

public class KRunFrontEnd extends FrontEnd {

    public static List<Module> getDefinitionSpecificModules(String[] argv) {
        return ImmutableList.<Module>of(
                new KRunModule.CommonModule(),
                new DefinitionLoadingModule()
        );
    }

    public static List<Module> getModules(String[] args, List<Module> definitionSpecificModules) {
        KRunOptions options = new KRunOptions();

        return ImmutableList.<Module>of(
                new KRunModule(options),
                new CommonModule(),
                new JCommanderModule(args),
                new KRunModule.MainExecutionContextModule(options, definitionSpecificModules));
    }


    private final TransformationProvider<Transformation<Void, Void>> toolProvider;
    private final KExceptionManager kem;

    @Inject
    KRunFrontEnd(
            GlobalOptions options,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            TransformationProvider<Transformation<Void, Void>> toolProvider,
            KExceptionManager kem,
            BinaryLoader loader,
            JarInfo jarInfo,
            @Main FileUtil files) {
        super(kem, options, usage, experimentalUsage, jarInfo, files);
        this.toolProvider = toolProvider;
        this.kem = kem;
    }

    /**
     * @param cmds represents the arguments/options given to krun command..
     * @return true if the application completed normally; false otherwise
     */
    public boolean run() {
        try {
            Transformation<Void, Void> tool = toolProvider.get();
            tool.run(null, new Attributes());
            return true;
        } catch (TransformationNotSatisfiedException
                | AmbiguousTransformationException e) {
            throw KExceptionManager.criticalError(e.getMessage(), e);
        }
    }
}
