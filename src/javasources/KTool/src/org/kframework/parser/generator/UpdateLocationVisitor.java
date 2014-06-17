// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Sentence;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class UpdateLocationVisitor extends BasicVisitor {
    private int currentStartLine;
    private int currentStartColumn;
    private int cachedStartLine;
    private int cachedStartColumn;

    public UpdateLocationVisitor(Context context, int currentStartLine, int currentStartColumn,
                                                  int  cachedStartLine, int  cachedStartColumn) {
        super(context);
        this.currentStartLine   = currentStartLine;
        this.currentStartColumn = currentStartColumn;
        this.cachedStartColumn  = cachedStartColumn;
        this.cachedStartLine    = cachedStartLine;
    }

    public Void visit(ASTNode node, Void _) {
        String[] str = node.getLocation().split("[\\(,\\)]");
        if (str.length != 5)
            return null;
        int startLine   = Integer.parseInt(str[0 + 1]);
        int startColumn = Integer.parseInt(str[1 + 1]);
        int endLine     = Integer.parseInt(str[2 + 1]);
        int endColumn   = Integer.parseInt(str[3 + 1]);

        int columnOffset = currentStartColumn - cachedStartColumn;
        int lineOffset = currentStartLine - cachedStartLine;
        // offset the column only if on the first line
        if (startLine == cachedStartLine) {
            startColumn += columnOffset;
            if (endLine == cachedStartLine)
                endColumn += columnOffset;
        }

        startLine += lineOffset;
        endLine   += lineOffset;

        String newLoc = "(" + startLine + "," + startColumn + "," + endLine + "," + endColumn + ")";
        node.setLocation(newLoc);
        return null;
    }

    @Override
    public boolean cache() {
        return true;
    }
}
