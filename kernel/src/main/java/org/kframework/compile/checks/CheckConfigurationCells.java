// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.compile.GenerateSentencesFromConfigDecl;
import org.kframework.definition.Configuration;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;
import org.kframework.utils.errorsystem.KEMException;

import java.util.HashSet;
import java.util.Set;

import static org.kframework.Collections.*;

/**
 * Checks that no two cells with the same name are declared in the configuration.
 */
public class CheckConfigurationCells {
    private final Set<KEMException> errors;

    private final Module module;

    private final boolean isSymbolicKast;

    public CheckConfigurationCells(Set<KEMException> errors, Module module, boolean isSymbolicKast) {
        this.errors = errors;
        this.module = module;
        this.isSymbolicKast = isSymbolicKast;
    }

    public void check(Sentence s) {
        if (s instanceof Production) {
            check((Production) s);
        }
        else if (s instanceof Rule && s.att().contains("initializer")) {
            check((Rule) s);
        }
    }

    private Set<Sort> cells = new HashSet<>();

    private void check(Production p) {
        if (p.att().contains(Att.CELL())) {
            for (ProductionItem i : mutable(p.items())) {
                if (i instanceof NonTerminal) {
                    Sort sort = ((NonTerminal) i).sort();
                    if (sort.name().endsWith("Cell")) {
                        if (cells.contains(sort)) {
                            Production cell = new ConfigurationInfoFromModule(module).cellProductionsFor().get(sort).get().head();
                            errors.add(KEMException.compilerError("Cell " + cell.klabel().get() + " found twice in configuration.", p));
                        }
                        cells.add(sort);
                    }
                }
            }
            if (p.att().getOptional("multiplicity").orElse("").equals("*") && p.att().getOptional("type").orElse("Bag").equals("Bag")) {
                if (!isSymbolicKast) {
                    errors.add(KEMException.compilerError("Cell bags are only supported on the Java backend. If you want "
                          + "this feature, comment on https://github.com/runtimeverification/k/issues/1419 . As a workaround, you can add the attribute "
                          + "type=\"Set\" and add a unique identifier to each element in the set.", p));
                }
            }
        }
    }
    private void check(Rule r) {
        KLabel kLabel = module.matchKLabel(r);
        if (module.rulesFor().get(kLabel).getOrElse(()-> Collections.Set()).size() > 1) {
            errors.add(KEMException.compilerError(
                    "Duplicate initialization of " + kLabel.name().replaceFirst("Cell", "").replaceFirst("init","") +
                            " cell found. Only one initialization is allowed.", r));
        }
    }
}
