// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile.checks;

import static org.kframework.Collections.*;

import com.google.common.collect.Comparators;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.kframework.DirectedGraph;
import org.kframework.attributes.HasLocation;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.Sentence;
import org.kframework.definition.SyntaxLexical;
import org.kframework.definition.regex.Regex;
import org.kframework.definition.regex.RegexBody;
import org.kframework.definition.regex.RegexSyntax;
import org.kframework.definition.regex.RegexVisitor;
import org.kframework.utils.errorsystem.KEMException;

/**
 * Check that regular expressions are semantically valid:
 *
 * <ul>
 *   <li>Every referenced identifier has a corresponding declaration
 *   <li>`syntax lexical` declarations are non-circular
 *   <li>`syntax lexical` declarations do not contain line anchors
 *   <li>Non-ASCII characters do not occur in character ranges nor negated character classes
 *   <li>Character class ranges `[c1-c2]` have codepoint(c1) <= codepoint(c2)
 *   <li>Numeric ranges `r{n,m}` have n <= m
 * </ul>
 */
public class CheckRegex {
  public static void check(Set<KEMException> errors, Module m) {
    checkNames(errors, m);
    stream(m.sortedLocalSentences())
        .forEach(
            s -> {
              checkLineAnchors(errors, s);
              checkUnicode(errors, s);
              checkCharClassRanges(errors, s);
              checkNumericRanges(errors, s);
            });
  }

  private static Stream<Regex> regexTerminals(Production prod) {
    return stream(prod.items())
        .flatMap(i -> i instanceof RegexTerminal term ? Stream.of(term.regex()) : Stream.of());
  }

  private static void checkNames(Set<KEMException> errors, Module m) {
    Map<String, SyntaxLexical> definedNames =
        stream(m.lexicalIdentifiers())
            .map(syn -> Map.entry(syn.name(), syn))
            .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
    // LinkedHashMap/LinkedHashSet to stabilize the error message / iteration order
    Map<SyntaxLexical, Set<SyntaxLexical>> synDeps = new LinkedHashMap<>();
    for (Sentence s : iterable(m.sortedLocalSentences())) {
      Set<String> badNames = new LinkedHashSet<>();
      if (s instanceof SyntaxLexical syn) {
        Set<SyntaxLexical> deps = new LinkedHashSet<>();
        CollectLexicalIdentifiers.collect(syn.regex())
            .forEach(
                n -> {
                  if (definedNames.containsKey(n)) {
                    deps.add(definedNames.get(n));
                  } else {
                    badNames.add(n);
                  }
                });
        synDeps.put(syn, deps);
      } else if (s instanceof Production prod) {
        badNames.addAll(
            regexTerminals(prod)
                .flatMap(r -> CollectLexicalIdentifiers.collect(r).stream())
                .filter(n -> !definedNames.containsKey(n))
                .collect(Collectors.toSet()));
      }
      if (!badNames.isEmpty()) {
        errors.add(
            KEMException.outerParserError(
                "Unrecognized lexical identifiers in regular expression: " + badNames, s));
      }
    }

    Comparator<SyntaxLexical> sourceComp =
        (a, b) -> {
          int compSource =
              Comparators.emptiesLast(Comparator.<Source>naturalOrder())
                  .compare(a.source(), b.source());
          if (compSource != 0) {
            return compSource;
          }
          return Comparators.emptiesLast(Comparator.<Location>naturalOrder())
              .compare(a.location(), b.location());
        };
    DirectedGraph.findDisjointCycles(synDeps)
        .forEach(
            (cycle) ->
                errors.add(
                    KEMException.outerParserError(
                        "Circular dependency between lexical identifiers: ["
                            + DirectedGraph.sortCycle(cycle, sourceComp).stream()
                                .map(SyntaxLexical::name)
                                .collect(Collectors.joining(", "))
                            + "]",
                        cycle.get(0))));
  }

  // Find all lexical identifiers {Name} in the regex
  private static class CollectLexicalIdentifiers extends RegexVisitor {
    private final Set<String> identifiers;

    private CollectLexicalIdentifiers() {
      this.identifiers = new LinkedHashSet<>();
    }

    public static Set<String> collect(Regex reg) {
      CollectLexicalIdentifiers collect = new CollectLexicalIdentifiers();
      collect.apply(reg);
      return collect.identifiers;
    }

    @Override
    public void apply(RegexBody.Named named) {
      identifiers.add(named.name());
    }
  }

  private static void checkLineAnchors(Set<KEMException> errors, Sentence s) {
    if (s instanceof SyntaxLexical syn && (syn.regex().startLine() || syn.regex().endLine())) {
      errors.add(
          KEMException.outerParserError("Named lexical syntax cannot contain line anchors.", s));
    }
  }

  private static void checkUnicode(Set<KEMException> errors, Sentence s) {
    CollectBadUnicodeRegex collect = new CollectBadUnicodeRegex();
    if (s instanceof SyntaxLexical syn) {
      collect.apply(syn.regex());
    } else if (s instanceof Production prod) {
      regexTerminals(prod).forEach(collect::apply);
    }
    if (!collect.unicodeInNegatedCharClass().isEmpty()) {
      errors.add(
          KEMException.outerParserError(
              "Unsupported non-ASCII characters found in negated character class: "
                  + collect.unicodeInNegatedCharClass().stream().map(Character::toString).toList(),
              s));
    }
    if (!collect.unicodeInCharClassRange().isEmpty()) {
      errors.add(
          KEMException.outerParserError(
              "Unsupported non-ASCII characters found in character class range: "
                  + collect.unicodeInCharClassRange().stream().map(Character::toString).toList(),
              s));
    }
  }

  private static class CollectBadUnicodeRegex extends RegexVisitor {
    private final Set<Integer> badNegated;
    private final Set<Integer> badRange;

    public CollectBadUnicodeRegex() {
      this.badNegated = new LinkedHashSet<>();
      this.badRange = new LinkedHashSet<>();
    }

    public Set<Integer> unicodeInNegatedCharClass() {
      return badNegated;
    }

    public Set<Integer> unicodeInCharClassRange() {
      return badRange;
    }

    @Override
    public void apply(RegexBody.CharClassExp clsExp) {
      if (!clsExp.negated()) {
        super.apply(clsExp);
        return;
      }
      badNegated.addAll(
          clsExp.charClasses().stream()
              .flatMap(
                  cls -> {
                    if (cls instanceof RegexBody.CharClass.Char chr) {
                      return Stream.of(chr.codePoint());
                    }
                    if (cls instanceof RegexBody.CharClass.Range range) {
                      return Stream.of(range.start(), range.end());
                    }
                    throw new AssertionError("Unhandled class: " + cls.getClass());
                  })
              .filter(c -> c > 127)
              .distinct()
              .toList());
      super.apply(clsExp);
    }

    @Override
    public void apply(RegexBody.CharClass.Range range) {
      if (range.start() > 127) {
        badRange.add(range.start());
      }
      if (range.end() > 127) {
        badRange.add(range.end());
      }
    }
  }

  private static void checkCharClassRanges(Set<KEMException> errors, Sentence s) {
    if (s instanceof SyntaxLexical syn) {
      CheckCharClassRanges.check(errors, s, syn.regex());
    } else if (s instanceof Production prod) {
      regexTerminals(prod).forEach(r -> CheckCharClassRanges.check(errors, s, r));
    }
  }

  private static class CheckCharClassRanges extends RegexVisitor {
    private final Set<KEMException> errors;
    private final HasLocation loc;

    private CheckCharClassRanges(Set<KEMException> errors, HasLocation loc) {
      this.errors = errors;
      this.loc = loc;
    }

    public static void check(Set<KEMException> errors, HasLocation loc, Regex reg) {
      new CheckCharClassRanges(errors, loc).apply(reg);
    }

    @Override
    public void apply(RegexBody.CharClass.Range range) {
      if (range.start() > range.end()) {
        errors.add(
            KEMException.outerParserError(
                "Invalid character range '"
                    + RegexSyntax.K.print(range)
                    + "'. Start of range U+"
                    + String.format("%04X", range.start())
                    + " is greater than end of range U+"
                    + String.format("%04X", range.end())
                    + ".",
                loc));
      }
    }
  }

  private static void checkNumericRanges(Set<KEMException> errors, Sentence s) {
    if (s instanceof SyntaxLexical syn) {
      CheckNumericRanges.check(errors, s, syn.regex());
    } else if (s instanceof Production prod) {
      regexTerminals(prod).forEach(r -> CheckNumericRanges.check(errors, s, r));
    }
  }

  private static class CheckNumericRanges extends RegexVisitor {
    private final Set<KEMException> errors;
    private final HasLocation loc;

    private CheckNumericRanges(Set<KEMException> errors, HasLocation loc) {
      this.errors = errors;
      this.loc = loc;
    }

    public static void check(Set<KEMException> errors, HasLocation loc, Regex reg) {
      new CheckNumericRanges(errors, loc).apply(reg);
    }

    @Override
    public void apply(RegexBody.RangeOfTimes range) {
      if (range.atLeast() > range.atMost()) {
        errors.add(
            KEMException.outerParserError(
                "Invalid numeric range '"
                    + RegexSyntax.K.print(range)
                    + "'. Start of range "
                    + range.atLeast()
                    + " is greater than end of range "
                    + range.atMost()
                    + ".",
                loc));
      }
    }
  }
}
