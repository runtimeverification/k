// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.latex;

import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Rule;
import org.kframework.utils.StringUtil;

public class DocumentationFilter extends LatexFilter {

    public DocumentationFilter(org.kframework.kil.loader.Context context) {
        super(context);
    }

    @Override
    public Void visit(Module mod, Void _) {
        result.append("\\begin{module}{\\moduleName{" + StringUtil.latexify(mod.getName()) + "}}" + endl);
        //insert section and label tags for link
        result.append("\\section{" + mod.getName() + "}" + endl);
        result.append("\\label{sec:" + mod.getName() + "}" + endl);
        //insert link at beginning of document; assume we already have "\maketitle"
        //as we should have visited a Definition before visiting a Module
        result.insert(result.indexOf("\\maketitle") + ".maketitle".length(), "\\hyperref[sec:" + mod.getName() + "]{" + mod.getName() + "}\\\\" + endl);

        if (cache.containsKey(mod))
            return null;
        for (ModuleItem mi : mod.getItems()) {
            this.visitNode(mi);
        }
        visit((DefinitionItem) mod, _);
        result.append("\\end{module}" + endl);
        return null;
    }

    @Override
    public Void visit(Rule rule, Void _) {
        // termComment = false;
        boolean process = false;
        for(String tag : options.experimental.documentation) {
            if(rule.containsAttribute(tag)) {
                process = true;
                break;
            }
        }
        if(process) super.visit(rule, _);
        return null;
    }
}
