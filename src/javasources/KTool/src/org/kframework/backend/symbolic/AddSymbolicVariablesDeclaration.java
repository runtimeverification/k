// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.symbolic;

import org.kframework.backend.Backends;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import java.util.*;

/**
 * Created with IntelliJ IDEA.
 * User: andrei.arusoaie
 * Date: 11/28/13
 * Time: 8:46 AM
 * Generate syntax for symbolic variables.
 * This works only for the maude symbolic backend.
 */
public class AddSymbolicVariablesDeclaration extends BasicVisitor {
    private final String syntaxModule;

    private String terminal  = "[\\$][A-Z][a-zA-Z0-9]*[\\:][a-zA-Z]+";
    private String follow = "[a-zA-Z]";
    private final String symVariable = "SymVariable";

    public AddSymbolicVariablesDeclaration(Context context, String syntaxModule) {
        super(context);
        this.syntaxModule = syntaxModule;
    }

    @Override
    public Void visit(Module module, Void _) {

        //TODO(dwightguth): remove for modularization
        if (module.getName().equals(syntaxModule) && context.kompileOptions.backend.equals(Backends.SYMBOLIC)) {

            // adding lexical construct
            Lexical lexical = new Lexical(terminal, follow);
            org.kframework.kil.Attributes attributes = new Attributes();
//            attributes.set("onlyLabel", "");
            attributes.add(Attribute.NOT_IN_RULES);
            attributes.add(Attribute.VARIABLE);

            // adding default Int ::= SymVar
            java.util.List<ModuleItem> itemsS = module.getItems();
            itemsS.add(getSyntaxDeclaration(symVariable, lexical, attributes));
            itemsS.add(getSyntaxDeclaration("Int", new NonTerminal(Sort.of(symVariable)), new Attributes()));
            module.setItems(itemsS);
        }

        return super.visit(module, _);    //To change body of overridden methods use File | Settings | File Templates.
    }

    private Syntax getSyntaxDeclaration(String sortName, ProductionItem pi, Attributes attributes) {
        java.util.List<ProductionItem> items = new ArrayList<ProductionItem>();
        items.add(pi);

        NonTerminal sort = new NonTerminal(Sort.of(sortName));
        Production production = new Production(sort, items);
        production.setAttributes(attributes);
        java.util.List<Production> productions = new ArrayList<Production>();
        productions.add(production);
        java.util.List<PriorityBlock> priorities = new ArrayList<PriorityBlock>();
        priorities.add(new PriorityBlock("", productions));

        return new Syntax(sort, priorities);
    }
}
