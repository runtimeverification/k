package org.kframework.compile.checks;

import com.google.common.collect.ImmutableSet;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Sentence;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;

public class CheckTokens {
    private final Set<KEMException> errors;
    private final Module m;
    private static final ImmutableSet<String> ignoredSortNames = ImmutableSet.of("Bag", "IOFile", "IOInt", "IOString", "K", "KBott", "KItem", "KLabel", "KList", "Sort");

    public CheckTokens(Set<KEMException> errors, Module m) {
        this.errors = errors;
        this.m = m;
    }

    // This check ensures that sorts containing token declarations only contain syntax declarations that are also tokens (or macros).
    public void check(Sentence sentence) {
        if (!(sentence instanceof Production)) {
            return;
        }

        Production p = (Production) sentence;
        // ignoredSortNames include special sorts defined in domains.md or kast.md that are special variables that
        // contain subsorts and tokens. The codebase relies on the definitions kast.md and domains.md to be unmodified
        // so ignore these names.
        if (p.att().contains("function") || p.att().contains("token") || p.sort().name().startsWith("#")
                || ignoredSortNames.contains(p.sort().name())) {
            return;
        }

        if (!m.tokenProductionsFor().contains(p.sort()) // We only care about sorts that have been declared as tokens.
                || p.klabel().isDefined() && m.macroKLables().contains(p.klabel().get())) {
            return;
        }

        errors.add(KEMException.compilerError("Sort " + p.sort().name() + " was declared as a token. Productions of this sort can only contain [function] or [token] labels.", p));
    }
}
