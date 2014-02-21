package org.kframework.kil.loader;

import org.kframework.backend.java.util.KSorts;
import org.kframework.backend.symbolic.AddConditionToConfig;
import org.kframework.backend.symbolic.ResolveInputStreamCell;
import org.kframework.kil.KSort;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.general.GlobalSettings;

/**
 * Collect the $PGM sort from the final configuration it encounters
 * 
 * @author Radu
 * 
 */
public class CollectStartSymbolPgmVisitor extends BasicVisitor {

	public CollectStartSymbolPgmVisitor(Context context) {
		super(context);
        {
            /*
                Here we add $PC and $IN manually because they are added during the compilation process
                after the configuration is serialized. Probably, the compiler should serialize the
                configuration right before sending it to various backends.
                The symbolic backend adds by default these two variables because users may want to
                be able to send symbolic inputs to their programs ($IN) and set the initial
                path condition ($PC).
             */
            context.configVarSorts.put(AddConditionToConfig.PC_VAR.substring(1), "Bool");
            context.configVarSorts.put(ResolveInputStreamCell.IN.substring(1), org.kframework.kil.KSorts.LIST);
        }
	}

	@Override
	public void visit(Rule node) {
	}

	@Override
	public void visit(org.kframework.kil.Context node) {
	}

	@Override
	public void visit(Syntax node) {
	}

	@Override
	public void visit(Variable node) {
		if (node.getName().equals("$PGM")) {
			context.startSymbolPgm = node.getSort();
		}
		assert node.getName().startsWith("$") : "Configuration variables must start with $ symbol.";
		context.configVarSorts.put(node.getName().substring(1), node.getSort());
	}
}
