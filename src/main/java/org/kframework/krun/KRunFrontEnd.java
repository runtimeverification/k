// Copyright (c) 2010-2014 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.backend.java.symbolic.JavaSymbolicKRunModule;
import org.kframework.kil.Attributes;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.transformation.AmbiguousTransformationException;
import org.kframework.transformation.Transformation;
import org.kframework.transformation.TransformationNotSatisfiedException;
import org.kframework.transformation.TransformationProvider;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.DefinitionLoadingModule;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;
import org.kframework.utils.inject.CommonModule;
import com.google.inject.Inject;
import com.google.inject.Module;

public class KRunFrontEnd extends FrontEnd {

    public static Module[] getModules(String[] args, Module... definitionSpecificModules) {
        KRunOptions options = new KRunOptions();
        JavaExecutionOptions javaOptions = new JavaExecutionOptions();

        return new com.google.inject.Module[] {
                new KRunModule(options),
                new CommonModule(),
                new JCommanderModule(args),
                new JavaSymbolicKRunModule(javaOptions),
                new KRunModule.MainExecutionContextModule(options, definitionSpecificModules),
                new JavaSymbolicKRunModule.SimulationModule(definitionSpecificModules)
        };
    }

    public static Module[] getDefinitionSpecificModules(String[] argv) {
        return new com.google.inject.Module[] {
                new KRunModule.CommonModule(),
                new DefinitionLoadingModule(),
                new JavaSymbolicKRunModule.CommonModule()
        };
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
            JarInfo jarInfo) {
        super(kem, options, usage, experimentalUsage, jarInfo);
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
            kem.registerCriticalError(e.getMessage(), e);
            throw new AssertionError("unreachable");
        }
    }
}
