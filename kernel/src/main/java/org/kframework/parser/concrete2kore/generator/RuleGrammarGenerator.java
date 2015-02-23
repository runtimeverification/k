package org.kframework.parser.concrete2kore.generator;

import org.kframework.kore.outer.Definition;
import org.kframework.kore.outer.Module;
import org.kframework.parser.concrete2kore.ParseInModule;

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

    private final Definition baseK;

    public RuleGrammarGenerator(Definition baseK) {
        this.baseK = renameKItem2TopBottom(baseK);
    }

    private Definition renameKItem2TopBottom(Definition def) {
        // TODO: do renaming of KItem and K in the LHS to #Bottom
        return def;
    }

    public ParseInModule getRuleGrammar(Module mod) {
        // TODO: do some changes to the module
        return new ParseInModule(mod);
    }
}
