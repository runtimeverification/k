package org.kframework.compile.tags;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.kompile.KompileOptions;

public class AddOptionalTags extends BasicTransformer {

    private KompileOptions options;
    
    public AddOptionalTags(Context context) {
        super("AddOptionalTags", context);
        this.options = context.kompileOptions;
    }

    @Override
    public ASTNode transform(Attributes node) throws TransformerException {

        for (String tag : options.transition)
            if (node.containsKey(tag))
                node.set("transition", "");
        for (String tag : options.supercool)
            if (node.containsKey(tag))
                node.set("supercool", "");
        for (String tag : options.superheat)
            if (node.containsKey(tag))
                node.set("superheat", "");

        return node;
    }
}
