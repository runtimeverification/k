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
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.Sentence;
import org.kframework.definition.SyntaxLexical;
import org.kframework.definition.regex.RegexBody;
import org.kframework.utils.errorsystem.KEMException;

/**
 * Check that all lexical identifiers exist, have no circular dependencies, and do not contain line
 * anchors.
 */
public class CheckLexicalIdentifiers {
  public static void check(Set<KEMException> errors, Module m) {
    checkNames(errors, m);
    stream(m.sortedLocalSentences()).forEach(s -> checkLineAnchors(errors, s));
  }

  public static void checkNames(Set<KEMException> errors, Module m) {
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
        collectNames(syn.regex().reg())
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
            stream(prod.items())
                .flatMap(
                    i ->
                        i instanceof RegexTerminal
                            ? collectNames(((RegexTerminal) i).regex().reg())
                            : Stream.empty())
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
  private static Stream<String> collectNames(RegexBody reg) {
    if (reg instanceof RegexBody.Char
        || reg instanceof RegexBody.AnyChar
        || reg instanceof RegexBody.CharClassExp) {
      return Stream.empty();
    }
    if (reg instanceof RegexBody.Named named) {
      return Stream.of(named.name());
    }
    if (reg instanceof RegexBody.Union un) {
      return Stream.concat(collectNames(un.left()), collectNames(un.right()));
    }
    if (reg instanceof RegexBody.Concat con) {
      return con.members().stream().flatMap(CheckLexicalIdentifiers::collectNames);
    }
    if (reg instanceof RegexBody.ZeroOrMoreTimes star) {
      return collectNames(star.reg());
    }
    if (reg instanceof RegexBody.ZeroOrOneTimes question) {
      return collectNames(question.reg());
    }
    if (reg instanceof RegexBody.OneOrMoreTimes plus) {
      return collectNames(plus.reg());
    }
    if (reg instanceof RegexBody.ExactlyTimes exact) {
      return collectNames(exact.reg());
    }
    if (reg instanceof RegexBody.AtLeastTimes atLeast) {
      return collectNames(atLeast.reg());
    }
    if (reg instanceof RegexBody.RangeOfTimes range) {
      return collectNames(range.reg());
    }
    throw new AssertionError("Unhandled class: " + reg.getClass());
  }

  private static void checkLineAnchors(Set<KEMException> errors, Sentence s) {
    if (s instanceof SyntaxLexical syn && (syn.regex().startLine() || syn.regex().endLine())) {
      errors.add(
          KEMException.outerParserError("Named lexical syntax cannot contain line anchors.", s));
    }
  }
}
