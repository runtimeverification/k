package org.kframework.backend.java.symbolic;

import com.google.inject.Inject;
import org.kframework.Rewriter;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kil.Attribute;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kore.K;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.util.List;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;

/**
 * Created by dwightguth on 8/26/15.
 */
public class ProofExecutionMode implements ExecutionMode<List<K>> {

    private final KExceptionManager kem;
    private final KRunOptions options;
    private final Stopwatch sw;
    private final FileUtil files;
    private final GlobalOptions globalOptions;

    @Inject
    public ProofExecutionMode(KExceptionManager kem, KRunOptions options, Stopwatch sw, FileUtil files, GlobalOptions globalOptions) {
        this.kem = kem;
        this.options = options;
        this.sw = sw;
        this.files = files;
        this.globalOptions = globalOptions;
    }

    @Override
    public List<K> execute(K k, Rewriter rewriter, CompiledDefinition compiledDefinition) {
        String proofFile = options.experimental.prove;
        String content = files.loadFromWorkingDirectory(proofFile);
        Kompile kompile = new Kompile(compiledDefinition.kompileOptions, globalOptions, files, kem, sw, false);
        Module mod = kompile.parseModule(compiledDefinition, files.resolveWorkingDirectory(proofFile), true);
        List<Rule> rules = stream(mod.rules())
                .map(r -> /* TODO(andreistefanescu): perform preprocessing) */ r)
                .map(r -> kompile.compileRule(compiledDefinition, r))
                .collect(Collectors.toList());
        return rules.stream().filter(r -> !r.att().contains(Attribute.TRUSTED_KEY)).flatMap(r -> rewriter.proveRule(r, rules).stream()).collect(Collectors.toList());
    }
}
