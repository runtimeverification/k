// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.symbolic;

import java.util.Map;

import org.kframework.kil.Variable;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

/**
 * Add variable $IN if the current cell is marked as being 
 * connected to the input stream.
 * @author andreiarusoaie
 *
 */
public class ResolveInputStreamCell extends CopyOnWriteTransformer {

    private boolean notSet = true;
    public static String IN = "$IN";
    public ResolveInputStreamCell(Context context) {
        super("Resolve InputStream cell", context);
    }
    
    @Override
    public ASTNode visit(Cell node, Void _)  {
        
        Map<String, String> attributes = node.getCellAttributes();
        if (!attributes.containsKey("stream"))
            return super.visit(node, _);
        
        if (node.getCellAttributes().get("stream").equals(Constants.STDIN) && notSet){

            Variable in = new Variable(IN, "List");
            
            node.shallowCopy();
            node.setContents(in);
            notSet = true;

            context.configVarSorts.put(in.getName(), in.getSort());
        }
        
        
        return super.visit(node, _);
    }
}
