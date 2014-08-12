// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Location;
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
        Location loc = node.getLocation();
        if (loc == null) {
            return null;
        }
        int startLine   = loc.lineStart;
        int startColumn = loc.columnStart;
        int endLine     = loc.lineEnd;
        int endColumn   = loc.columnEnd;

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

        node.setLocation(new Location(startLine, startColumn, endLine, endColumn));
        return null;
    }

    @Override
    public boolean cache() {
        return true;
    }
}
