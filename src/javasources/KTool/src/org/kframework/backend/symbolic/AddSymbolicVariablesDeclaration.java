package org.kframework.backend.symbolic;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kompile.KompileOptions;

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
    public void visit(Module module) {

        if (module.getName().equals(syntaxModule) && context.kompileOptions.backend == KompileOptions.Backend.symbolic) {

            // adding lexical construct
            Lexical lexical = new Lexical(terminal, follow);
            org.kframework.kil.Attributes attributes = new Attributes();
//            attributes.set("onlyLabel", "");
            attributes.set("notInRules", "");
            attributes.set("variable", "");

            // adding default Int ::= SymVar
            java.util.List<ModuleItem> itemsS = module.getItems();
            itemsS.add(getSyntaxDeclaration(symVariable, lexical, attributes));
            itemsS.add(getSyntaxDeclaration("Int", new Sort(symVariable), new Attributes()));
            module.setItems(itemsS);
        }

        super.visit(module);    //To change body of overridden methods use File | Settings | File Templates.
    }

    private Syntax getSyntaxDeclaration(String sortName, ProductionItem pi, Attributes attributes) {
        java.util.List<ProductionItem> items = new ArrayList<ProductionItem>();
        items.add(pi);

        Sort sort = new Sort(sortName);
        Production production = new Production(sort, items);
        production.setAttributes(attributes);
        java.util.List<Production> productions = new ArrayList<Production>();
        productions.add(production);
        java.util.List<PriorityBlock> priorities = new ArrayList<PriorityBlock>();
        priorities.add(new PriorityBlock("", productions));

        return new Syntax(sort, priorities);
    }
}
