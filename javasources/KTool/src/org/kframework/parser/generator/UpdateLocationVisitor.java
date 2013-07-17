package org.kframework.parser.generator;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class UpdateLocationVisitor extends BasicVisitor {
	int startLine, startCol;

	public UpdateLocationVisitor(Context context, int startLine, int startCollumn) {
		super(context);
		this.startLine = startLine;
		this.startCol = startCollumn;
	}

	public void visit(ASTNode a) {
		super.visit(a);
		if (a.getLocation().startsWith("(")) {
			String[] str = a.getLocation().split("[\\(,\\)]");
			int loc0 = Integer.parseInt(str[0 + 1]);
			int loc1 = Integer.parseInt(str[1 + 1]);
			int loc2 = Integer.parseInt(str[2 + 1]);
			int loc3 = Integer.parseInt(str[3 + 1]);

			if (loc0 + loc1 + loc2 + loc3 == 0) {
				loc0 = startLine;
				loc1 = startCol;
				loc2 = startLine;
				loc3 = startCol;
			} else {
				if (loc0 == 1)
					loc1 += startCol - 1;
				if (loc2 == 1)
					loc3 += startCol - 1;
				loc0 += startLine - 1;
				loc2 += startLine - 1;
			}
			String newLoc = "(" + loc0 + "," + loc1 + "," + loc2 + "," + loc3 + ")";
			a.setLocation(newLoc);
		}
	}
}
