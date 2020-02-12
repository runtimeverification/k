package org.kframework.compile.checks;

import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.utils.errorsystem.KExceptionManager;

import static org.kframework.Collections.*;
import static org.kframework.compile.checks.CheckKLabels.*;
import static org.kframework.kil.Import.*;

public class CheckImports {
    private final KExceptionManager kem;
    private final Module mainModule;

    public CheckImports(Module mainModule, KExceptionManager kem) {
        this.mainModule = mainModule;
        this.kem = kem;
    }

    public void check(Module m) {
        if (m.localRules().isEmpty()) {
            return;
        }
        for (Module _import : iterable(m.imports())) {
            Module importSyntax;
            if (!_import.name().endsWith(IMPORTS_SYNTAX_SUFFIX)) {
                importSyntax = stream(_import.imports()).filter(mod -> mod.name().equals(_import.name() + IMPORTS_SYNTAX_SUFFIX)).findAny().get();
            } else {
                continue;
            }
            if (importSyntax.localProductions().isEmpty()) {
                continue;
            }
            if ((m.name() + "$SYNTAX").equals(_import.name())) {
                continue;
            }
            long numImports = stream(mainModule.importedModules()).filter(mod -> mod.imports().apply(_import)).count();
            if (mainModule.imports().apply(_import)) {
                numImports++;
            }
            if (numImports == 1 && _import.rules().nonEmpty()) {
                continue;
            }
            boolean used = false;
            boolean hasAny = false;
            for (Production prod : iterable(importSyntax.localProductions())) {
                if (prod.klabel().isEmpty()) {
                    continue;
                }
                hasAny = true;
                if (m.klabelsDefinedInRules().contains(prod.klabel().get().head()) || prod.att().contains("initializer")) {
                    used = true;
                }
            }
            if (hasAny && !used && !m.att().get(Source.class).source().equals(KAST_K.getAbsolutePath()) && !m.att().get(Source.class).source().equals(DOMAINS_K.getAbsolutePath()))  {
                kem.registerCompilerWarning("Module " + m.name() + " might not need to import module " + _import.name());
            }
        }
    }
}
