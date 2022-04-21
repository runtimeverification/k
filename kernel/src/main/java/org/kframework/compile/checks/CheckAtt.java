// Copyright (c) 2016-2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.attributes.Att;
import org.kframework.attributes.HasLocation;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.KLabel;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.Set;

import static org.kframework.Collections.*;

/**
 * Created by dwightguth on 1/25/16.
 */
public class CheckAtt {
    private final scala.collection.Set<KLabel> macros;
    private final Set<KEMException> errors;
    private final KExceptionManager kem;
    private final Module m;
    private final boolean isSymbolicKast;

    public CheckAtt(Set<KEMException> errors, KExceptionManager kem, Module m, boolean isSymbolicKast) {
        this.errors = errors;
        this.kem = kem;
        this.m = m;
        this.isSymbolicKast = isSymbolicKast;
        this.macros = m.macroKLabels();
    }

    public void check(Sentence sentence) {
        if (sentence instanceof Rule) {
            check(((Rule) sentence).att(), sentence);
            check((Rule) sentence);
        } else if (sentence instanceof Production) {
            check((Production) sentence);
        }
    }

    private void check(Production prod) {
        if (!prod.sort().equals(Sorts.KItem())) {
            Att sortAtt =  m.sortAttributesFor().getOrElse(prod.sort().head(), () -> Att.empty());
            if (sortAtt.contains(Att.HOOK()) && !sortAtt.get(Att.HOOK()).equals("ARRAY.Array") && !(sortAtt.get(Att.HOOK()).equals("KVAR.KVar") && isSymbolicKast)) {
                if (!prod.att().contains(Att.FUNCTION()) && !prod.att().contains(Att.BRACKET()) &&
                    !prod.att().contains("token") && !prod.att().contains("macro") && !(prod.klabel().isDefined() && macros.contains(prod.klabel().get()))) {
                    if (!(prod.sort().equals(Sorts.K()) && ((prod.klabel().isDefined() && (prod.klabel().get().name().equals("#EmptyK") || prod.klabel().get().name().equals("#KSequence"))) || prod.isSubsort()))) {
                        if (!(sortAtt.contains("cellCollection") && prod.isSubsort())) {
                            errors.add(KEMException.compilerError("Cannot add new constructors to hooked sort " + prod.sort(), prod));
                        }
                    }
                }
            }
        }
        if (prod.att().contains("binder") && !isSymbolicKast) {
            if (!prod.att().get("binder").equals("")) {
                errors.add(KEMException.compilerError("Attribute value for 'binder' attribute is not supported.", prod));
            }
            if (prod.nonterminals().size() < 2) {
                errors.add(KEMException.compilerError("Binder productions must have at least two nonterminals.", prod));
            } else if (!m.sortAttributesFor().get(prod.nonterminals().apply(0).sort().head()).getOrElse(() -> Att.empty()).getOptional(Att.HOOK()).orElse("").equals("KVAR.KVar")) {
                errors.add(KEMException.compilerError("First child of binder must have a sort with the 'KVAR.KVar' hook attribute.", prod));
            }
        }
        boolean hasColors = false;
        int ncolors = 0;
        if (prod.att().contains("colors")) {
          hasColors = true;
          ncolors = prod.att().get("colors").split(",").length;
        }
        int nterminals = prod.items().size() - prod.nonterminals().size();
        int nescapes = 0;
        if (prod.att().contains("format")) {
            String format = prod.att().get("format");
            for (int i = 0; i < format.length(); i++) {
                char c = format.charAt(i);
                if (c == '%') {
                    if (i == format.length() - 1) {
                        errors.add(KEMException.compilerError("Invalid format attribute: unfinished escape sequence.", prod));
                        break;
                    }
                    char c2 = format.charAt(i + 1);
                    i++;
                    switch(c2) {
                      case 'n':
                      case 'i':
                      case 'd':
                      case 'r':
                        break;
                      case 'c':
                        nescapes++;
                        break;
                      case '0':
                      case '1':
                      case '2':
                      case '3':
                      case '4':
                      case '5':
                      case '6':
                      case '7':
                      case '8':
                      case '9':
                        StringBuilder sb = new StringBuilder();
                        for (; i < format.length() && format.charAt(i) >= '0' && format.charAt(i) <= '9'; i++) {
                            sb.append(format.charAt(i));
                        }
                        i--;
                        int idx = Integer.parseInt(sb.toString());
                        if (idx == 0 || idx > prod.items().size()) {
                            errors.add(KEMException.compilerError("Invalid format escape sequence '%" + sb.toString() + "'. Expected a number between 1 and " + prod.items().size(), prod));
                        } else {
                            ProductionItem pi = prod.items().apply(idx-1);
                            if (pi instanceof RegexTerminal) {
                                errors.add(KEMException.compilerError("Invalid format escape sequence referring to regular expression terminal '" + pi + "'.", prod));
                            }
                        }
                        break;
                    }
                }
            }
        } else if (!prod.att().contains("token") && !prod.sort().equals(Sorts.Layout()) && !prod.sort().equals(Sorts.LineMarker())) {
            for (ProductionItem pi : iterable(prod.items())) {
                if (pi instanceof RegexTerminal) {
                    if (prod.items().size() == 1)  {
                        errors.add(KEMException.compilerError(
                              "Expected format attribute on production with regular expression terminal. Did you forget the 'token' attribute?", prod));
                    } else {
                        errors.add(KEMException.compilerError(
                              "Expected format attribute on production with regular expression terminal.", prod));
                    }
                }
            }
        }
        if (hasColors && nescapes + nterminals != ncolors) {
            errors.add(KEMException.compilerError("Invalid colors attribute: expected " + (nescapes + nterminals) + " colors, found " + ncolors + " colors instead.", prod));
        }
    }

    private void check(Rule rule) {
        if (rule.isMacro()) {
            kem.registerCompilerWarning(ExceptionType.RULE_HAS_MACRO_ATT, errors,
                    "The attribute [" + rule.att().getMacro().get() + "] has been deprecated on rules. Use this label on syntax declarations instead.", rule);
        }

        checkNonExecutable(rule);
    }

    private void checkNonExecutable(Rule rule) {
        boolean isNonExecutable = rule.att().contains(Att.NON_EXECUTABLE());
        boolean isFunction = m.attributesFor()
                                .getOrElse(m.matchKLabel(rule), Att::empty)
                                .contains(Att.FUNCTION());

        if(isNonExecutable && !isFunction) {
            errors.add(
                    KEMException.compilerError(
                            "non-executable attribute is only supported on function rules.",
                            rule));
        }
    }

    private void check(Att att, HasLocation loc) {
        if (att.contains(Att.OWISE()) && att.contains(Att.SIMPLIFICATION())) {
          errors.add(KEMException.compilerError("owise attribute is not supported on simplification rules.", loc));
        }
        if (att.contains(Att.PRIORITY()) && att.contains(Att.SIMPLIFICATION())) {
          errors.add(KEMException.compilerError("priority attribute is not supported on simplification rules.", loc));
        }
    }
}
