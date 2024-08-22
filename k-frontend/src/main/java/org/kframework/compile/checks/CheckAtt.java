// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile.checks;

import static org.kframework.Collections.*;

import java.util.List;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import org.kframework.attributes.Att;
import org.kframework.attributes.Att.Key;
import org.kframework.attributes.HasLocation;
import org.kframework.builtin.Sorts;
import org.kframework.definition.HasAtt;
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
import scala.Tuple2;

/** Check that attributes are well-formed and placed on the correct syntactic elements. */
public class CheckAtt {
  private final scala.collection.Set<KLabel> macros;
  private final Set<KEMException> errors;
  private final KExceptionManager kem;
  private final Module m;

  public CheckAtt(Set<KEMException> errors, KExceptionManager kem, Module m) {
    this.errors = errors;
    this.kem = kem;
    this.m = m;
    this.macros = m.macroKLabels();
  }

  public void check() {
    checkUnrecognizedAtts(m);
    checkRestrictedAtts(m);
    stream(m.localSentences()).forEach(this::checkSentence);
  }

  private void checkSentence(Sentence sentence) {
    checkUnrecognizedAtts(sentence);
    checkRestrictedAtts(sentence);
    checkLabel(sentence);

    if (sentence instanceof Rule rule) {
      checkRule(rule);
    } else if (sentence instanceof Production prod) {
      checkProduction(prod);
    }
  }

  private void checkRule(Rule rule) {
    checkNonExecutable(rule);
    checkSimplification(rule);
    checkSymbolic(rule);
    checkSyntactic(rule);
  }

  private void checkProduction(Production prod) {
    checkHookedSortConstructors(prod);
    checkBinder(prod);
    checkFormat(prod);
    checkFunctional(prod);
    checkTotal(prod);
    checkTerminatorKLabel(prod);
    checkLatex(prod);
    checkSymbolKLabel(prod);
    checkKLabelOverload(prod);
    checkNullarySymbol(prod);
    checkNoSymbolOverload(prod);
  }

  private <T extends HasAtt & HasLocation> void checkUnrecognizedAtts(T term) {
    if (!term.att().unrecognizedKeys().isEmpty()) {
      errors.add(
          KEMException.compilerError(
              "Unrecognized attributes: "
                  + stream(term.att().unrecognizedKeys()).map(Key::toString).sorted().toList(),
              term));
    }
  }

  private <T extends HasAtt & HasLocation> void checkRestrictedAtts(T term) {
    Class<?> cls = term.getClass();
    Att att = term.att();
    Set<Key> keys = stream(att.att().keySet()).map(Tuple2::_1).collect(Collectors.toSet());
    keys.removeIf(k -> k.allowedSentences().exists(c -> c.isAssignableFrom(cls)));
    if (!keys.isEmpty()) {
      List<String> sortedKeys = keys.stream().map(Key::toString).sorted().toList();
      errors.add(
          KEMException.compilerError(
              cls.getSimpleName() + " cannot have the following attributes: " + sortedKeys, term));
    }
  }

  private static final Pattern whitespace = Pattern.compile("\\s");

  private void checkLabel(Sentence sentence) {
    if (sentence.att().contains(Att.LABEL())) {
      String label = sentence.att().get(Att.LABEL());
      if (label.contains("`") || whitespace.matcher(label).find()) {
        errors.add(
            KEMException.compilerError(
                "Label '" + label + "' cannot contain whitespace or backticks.", sentence));
      }
    }
  }

  private void checkNonExecutable(Rule rule) {
    boolean isNonExecutable = rule.att().contains(Att.NON_EXECUTABLE());
    boolean isFunction =
        m.attributesFor().getOrElse(m.matchKLabel(rule), Att::empty).contains(Att.FUNCTION());

    if (isNonExecutable && !isFunction) {
      errors.add(
          KEMException.compilerError(
              "non-executable attribute is only supported on function rules.", rule));
    }
  }

  private void checkSimplification(Rule rule) {
    Att att = rule.att();
    if (att.contains(Att.OWISE()) && att.contains(Att.SIMPLIFICATION())) {
      errors.add(
          KEMException.compilerError(
              "owise attribute is not supported on simplification rules.", rule));
    }
    if (att.contains(Att.PRIORITY()) && att.contains(Att.SIMPLIFICATION())) {
      errors.add(
          KEMException.compilerError(
              "priority attribute is not supported on simplification rules.", rule));
    }
    if (att.contains(Att.ANYWHERE()) && att.contains(Att.SIMPLIFICATION())) {
      errors.add(
          KEMException.compilerError(
              "anywhere attribute is not supported on simplification rules.", rule));
    }
  }

  private void checkSymbolic(Rule rule) {
    if (rule.att().contains(Att.ANYWHERE()) && rule.att().contains(Att.SYMBOLIC())) {
      errors.add(
          KEMException.compilerError(
              "anywhere attribute is not supported on symbolic rules.", rule));
    }
  }

  private void checkSyntactic(Rule rule) {
    if (rule.att().contains(Att.SYNTACTIC()) && !rule.att().contains(Att.SIMPLIFICATION())) {
      errors.add(
          KEMException.compilerError(
              "syntactic attribute is only supported on simplification rules."));
    }
  }

  private void checkHookedSortConstructors(Production prod) {
    if (prod.sort().equals(Sorts.KItem())) {
      return;
    }
    Att sortAtt = m.sortAttributesFor().getOrElse(prod.sort().head(), Att::empty);
    if (sortAtt.contains(Att.HOOK())) {
      if (!prod.att().contains(Att.FUNCTION())
          && !prod.att().contains(Att.BRACKET())
          && !prod.att().contains(Att.TOKEN())
          && !prod.att().contains(Att.MACRO())
          && !(prod.klabel().isDefined() && macros.contains(prod.klabel().get()))) {
        if (!(prod.sort().equals(Sorts.K())
            && ((prod.klabel().isDefined()
                    && (prod.klabel().get().name().equals("#EmptyK")
                        || prod.klabel().get().name().equals("#KSequence")))
                || prod.isSubsort()))) {
          if (!(sortAtt.contains(Att.CELL_COLLECTION()) && prod.isSubsort())) {
            errors.add(
                KEMException.compilerError(
                    "Cannot add new constructors to hooked sort " + prod.sort(), prod));
          }
        }
      }
    }
  }

  private void checkBinder(Production prod) {
    if (!prod.att().contains(Att.BINDER())) {
      return;
    }
    if (prod.nonterminals().size() < 2) {
      errors.add(
          KEMException.compilerError(
              "Binder productions must have at least two nonterminals.", prod));
    } else if (!m.sortAttributesFor()
        .get(prod.nonterminals().apply(0).sort().head())
        .getOrElse(Att::empty)
        .getOptional(Att.HOOK())
        .orElse("")
        .equals("KVAR.KVar")) {
      errors.add(
          KEMException.compilerError(
              "First child of binder must have a sort with the 'KVAR.KVar' hook attribute.", prod));
    }
  }

  private void checkFormat(Production prod) {
    boolean hasColors = false;
    int ncolors = 0;
    if (prod.att().contains(Att.COLORS())) {
      hasColors = true;
      ncolors = prod.att().get(Att.COLORS()).split(",").length;
    }
    int nterminals = prod.items().size() - prod.nonterminals().size();
    int nescapes = 0;
    if (prod.att().contains(Att.FORMAT())) {
      String format = prod.att().get(Att.FORMAT());
      for (int i = 0; i < format.length(); i++) {
        char c = format.charAt(i);
        if (c == '%') {
          if (i == format.length() - 1) {
            errors.add(
                KEMException.compilerError(
                    "Invalid format attribute: unfinished escape sequence.", prod));
            break;
          }
          char c2 = format.charAt(i + 1);
          i++;
          switch (c2) {
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
              for (;
                  i < format.length() && format.charAt(i) >= '0' && format.charAt(i) <= '9';
                  i++) {
                sb.append(format.charAt(i));
              }
              i--;
              int idx = Integer.parseInt(sb.toString());
              if (idx == 0 || idx > prod.items().size()) {
                errors.add(
                    KEMException.compilerError(
                        "Invalid format escape sequence '%"
                            + sb
                            + "'. Expected a number between 1 and "
                            + prod.items().size(),
                        prod));
              } else {
                ProductionItem pi = prod.items().apply(idx - 1);
                if (pi instanceof RegexTerminal) {
                  errors.add(
                      KEMException.compilerError(
                          "Invalid format escape sequence referring to regular expression terminal"
                              + " '"
                              + pi
                              + "'.",
                          prod));
                }
              }
              break;
          }
        }
      }
    } else if (!prod.att().contains(Att.TOKEN())
        && !prod.sort().equals(Sorts.Layout())
        && !prod.sort().equals(Sorts.LineMarker())) {
      for (ProductionItem pi : iterable(prod.items())) {
        if (pi instanceof RegexTerminal) {
          if (prod.items().size() == 1) {
            errors.add(
                KEMException.compilerError(
                    "Expected format attribute on production with regular expression terminal. Did"
                        + " you forget the 'token' attribute?",
                    prod));
          } else {
            errors.add(
                KEMException.compilerError(
                    "Expected format attribute on production with regular expression terminal.",
                    prod));
          }
        }
      }
    }
    if (hasColors && nescapes + nterminals != ncolors) {
      errors.add(
          KEMException.compilerError(
              "Invalid colors attribute: expected "
                  + (nescapes + nterminals)
                  + " colors, found "
                  + ncolors
                  + " colors instead.",
              prod));
    }
  }

  private void checkFunctional(Production prod) {
    if (prod.att().contains(Att.FUNCTIONAL())) {
      kem.registerCompilerWarning(
          ExceptionType.FUTURE_ERROR,
          errors,
          "The attribute 'functional' has been deprecated on symbols. Use the combination of"
              + " attributes 'function' and 'total' instead.",
          prod);
    }
  }

  private void checkTotal(Production prod) {
    if (prod.att().contains(Att.TOTAL()) && !prod.att().contains(Att.FUNCTION())) {
      errors.add(
          KEMException.compilerError(
              "The attribute 'total' cannot be applied to a production which does not have the"
                  + " 'function' attribute.",
              prod));
    }
  }

  private void checkTerminatorKLabel(Production prod) {
    if (!prod.att().contains(Att.USER_LIST()) && prod.att().contains(Att.TERMINATOR_SYMBOL())) {
      errors.add(
          KEMException.compilerError(
              "The attribute 'terminator-symbol' cannot be applied to a production that does not declare a syntactic list.",
              prod));
    }
  }

  private void checkLatex(Production prod) {
    if (prod.att().contains(Att.LATEX())) {
      kem.registerCompilerWarning(
          ExceptionType.FUTURE_ERROR,
          errors,
          "The attribute 'latex' has been deprecated and all of its functionality has been removed. Using it will be an error in the future.",
          prod);
    }
  }

  private void checkSymbolKLabel(Production prod) {
    if (!prod.att().contains(Att.KLABEL())) {
      return;
    }

    var kLabelValue = prod.att().get(Att.KLABEL());

    if (prod.att().contains(Att.SYMBOL())) {
      if (prod.att().get(Att.SYMBOL()).isEmpty()) {
        var message =
            "The zero-argument form of `symbol` is deprecated. Replace `klabel("
                + kLabelValue
                + "), symbol` by `symbol("
                + kLabelValue
                + ")`.";

        kem.registerCompilerWarning(ExceptionType.FUTURE_ERROR, errors, message, prod);
      } else {
        errors.add(
            KEMException.compilerError(
                "The 1-argument form of the `symbol(_)` attribute cannot be combined with `klabel(_)`.",
                prod));
      }
    } else {
      var overloadProds = m.overloads().elements();

      if (overloadProds.contains(prod)) {
        var message =
            "Attribute `klabel("
                + kLabelValue
                + ") is deprecated, but marks an overload. Add `overload("
                + kLabelValue
                + ")`.";

        kem.registerCompilerWarning(ExceptionType.FUTURE_ERROR, errors, message, prod);
      } else {
        var message =
            "Attribute `klabel(_)` is deprecated. Either remove `klabel("
                + kLabelValue
                + ")`, or replace it by `symbol("
                + kLabelValue
                + ")`.";

        kem.registerCompilerWarning(ExceptionType.FUTURE_ERROR, errors, message, prod);
      }
    }
  }

  private void checkKLabelOverload(Production prod) {
    if (prod.att().contains(Att.KLABEL()) && prod.att().contains(Att.OVERLOAD())) {
      var klabelKey = prod.att().get(Att.KLABEL());
      var msg =
          "The attributes `klabel` and `overload` may not occur together. Either remove `klabel("
              + klabelKey
              + ")`, or replace it by `symbol("
              + klabelKey
              + ")`";

      errors.add(KEMException.compilerError(msg, prod));
    }
  }

  private void checkNoSymbolOverload(Production prod) {
    if (prod.klabel().isEmpty() && prod.att().contains(Att.OVERLOAD())) {
      errors.add(
          KEMException.compilerError(
              "Production would not be a KORE symbol and therefore cannot be overloaded. Add a `symbol(_)` attribute to the production.",
              prod));
    }
  }

  private void checkNullarySymbol(Production prod) {
    if (prod.att().contains(Att.SYMBOL()) && !prod.att().contains(Att.KLABEL())) {
      if (prod.att().get(Att.SYMBOL()).isEmpty()) {
        kem.registerCompilerWarning(
            ExceptionType.FUTURE_ERROR,
            errors,
            "Zero-argument `symbol` attribute used without a corresponding `klabel(_)`. Either remove `symbol`, or supply an argument.",
            prod);
      }
    }
  }
}
