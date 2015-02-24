package org.kframework.parser.concrete2kore.generator;

import org.kframework.kore.Attributes;
import org.kframework.kore.Sort;
import org.kframework.kore.outer.Module;
import org.kframework.kore.outer.Sentence;
import org.kframework.parser.concrete2kore.ParseInModule;

import java.util.HashSet;
import java.util.Set;

import static org.kframework.Collections.*;
import static org.kframework.kore.Constructors.*;
import static org.kframework.kore.outer.Constructors.*;

/**
 * Generator for rule and ground parsers.
 * Takes as input a reference to a definition containing all the base syntax of K
 * and uses it to generate a grammar by connecting all users sorts in a lattice with
 * the top sort KItem#Top and the bottom sort KItem#Bottom.
 *
 * The instances of the non-terminal KItem is renamed in KItem#Top if found in the right
 * hand side of a production, and into KItem#Bottom if found in the left hand side.
 */
public class RuleGrammarGenerator {

    private final Module baseK;
    private static final Sort KBott = Sort("KBott");
    private static final Sort KTop = Sort("K");
    private static final Set<Sort> kSorts = new HashSet<>();;

    public RuleGrammarGenerator(Module baseK) {
        this.baseK = renameKItem2Bottom(baseK);
        kSorts.add(KBott);
        kSorts.add(KTop);
        kSorts.add(Sort("KLabel"));
        kSorts.add(Sort("KList"));
        kSorts.add(Sort("KItem"));
    }

    private Module renameKItem2Bottom(Module def) {
        // TODO: do renaming of KItem and K in the LHS to KBott
        return def;
    }

    public ParseInModule getRuleGrammar(Module mod) {
        Set<Sentence> prods = new HashSet<>();

        // create the diamond
        for (Sort srt : iterable(mod.definedSorts())) {
            if (!kSorts.contains(srt)) {
                // Sort ::= KBott
                prods.add(SyntaxProduction(srt, Seq(NonTerminal(KBott)), Attributes()));
                // K ::= Sort
                prods.add(SyntaxProduction(KTop, Seq(NonTerminal(srt)), Attributes()));
                // K ::= K "::Sort" | K ":Sort" | K "<:Sort" | K ":>Sort"
                Attributes attrs1 = Attributes().add("klabel", "#SyntacticCast").add("sort", srt.name());
                prods.add(SyntaxProduction(KBott, Seq(NonTerminal(KTop), RegexTerminal("::" + srt.name() + "(?![a-zA-Z0-9])")), attrs1));
                Attributes attrs2 = Attributes().add("klabel", "#SemanticCast").add("sort", srt.name());
                prods.add(SyntaxProduction(KBott, Seq(NonTerminal(KTop), RegexTerminal(":" + srt.name() + "(?![a-zA-Z0-9])")), attrs2));
                Attributes attrs3 = Attributes().add("klabel", "#InnerCast").add("sort", srt.name());
                prods.add(SyntaxProduction(KBott, Seq(NonTerminal(KTop), RegexTerminal("<:" + srt.name() + "(?![a-zA-Z0-9])")), attrs3));
                Attributes attrs4 = Attributes().add("klabel", "#OuterCast").add("sort", srt.name());
                prods.add(SyntaxProduction(KBott, Seq(NonTerminal(KTop), RegexTerminal(":>" + srt.name() + "(?![a-zA-Z0-9])")), attrs4));
            }
        }

        Module newM = new Module(mod.name() + "-RULES", Set(mod, baseK), immutable(prods), null);
        return new ParseInModule(newM);
    }
}
