package org.kframework.backend.maude;

import java.util.Collections;
import java.util.List;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.Backend;
import org.kframework.backend.maude.krun.MaudeExecutor;
import org.kframework.backend.maude.krun.MaudeModelChecker;
import org.kframework.krun.tools.Executor;
import org.kframework.krun.tools.LtlModelChecker;
import org.kframework.main.AbstractKModule;

public class MaudeBackendKModule extends AbstractKModule {

    @Override
    public List<Pair<String, Class<? extends Backend>>> backends() {
        return Collections.singletonList(Pair.<String, Class<? extends Backend>>of("maude", KompileBackend.class));
    }

    @Override
    public List<Pair<String, Class<? extends Executor>>> executors() {
        return Collections.singletonList(Pair.<String, Class<? extends Executor>>of("maude", MaudeExecutor.class));
    }

    @Override
    public List<Pair<String, Class<? extends LtlModelChecker>>> ltlModelCheckers() {
        return Collections.singletonList(Pair.<String, Class<? extends LtlModelChecker>>of("maude", MaudeModelChecker.class));
    }

    @Override
    public List<Pair<Object, Boolean>> krunOptions() {
        return Collections.singletonList(Pair.<Object, Boolean>of(new MaudeKRunOptions(), true));
    }
}
