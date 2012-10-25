package org.kframework.parser.generator.loader;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.kframework.kil.Definition;
import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class CollectTerminalsVisitor extends BasicVisitor {
	public Set<String> defterminals = new HashSet<String>();
	public Set<String> synterminals = new HashSet<String>();
	private boolean isSyntax = false;
	private Set<String> synModNames = new HashSet<String>();

	public void visit(Definition def) {
		List<String> synQue = new LinkedList<String>();
		synQue.add(def.getMainSyntaxModule());
		synQue.add("AUTO-INCLUDED-MODULE-SYNTAX");

		while (!synQue.isEmpty()) {
			String mname = synQue.remove(0);
			if (!synModNames.contains(mname)) {
				synModNames.add(mname);

				Module m = def.getModulesMap().get(mname);
				for (ModuleItem s : m.getItems())
					if (s instanceof Import) {
						Import imp = ((Import) s);
						String mname2 = imp.getName();
						Module mm = def.getModulesMap().get(mname2);
						// if the module starts with # it means it is predefined in maude
						if (!mname2.startsWith("#"))
							if (mm != null)
								synQue.add(mm.getName());
							else // if (!MetaK.isKModule(mname2))
							{
								String msg = "Could not find module: " + mname2 + " imported from: " + m.getName();
								GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.PARSER, msg, imp.getFilename(), imp.getLocation()));
							}
					}
			}
		}

		super.visit(def);
	}

	public void visit(Module m) {
		if (synModNames.contains(m.getName()))
			isSyntax = true;
		super.visit(m);
		isSyntax = false;
	}

	private void addTerminal(String terminal) {
		if (terminal.equals(""))
			return;
		if (isSyntax)
			synterminals.add(terminal);
		defterminals.add(terminal);
	}

	public void visit(Terminal t) {
		addTerminal(t.getTerminal());
	}

	public void visit(UserList ul) {
		addTerminal(ul.getSeparator());
	}
}
