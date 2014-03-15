package org.kframework.backend.latex;

import org.kframework.kil.Attributes;
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
    public void visit(Module mod) {
        result.append("\\begin{module}{\\moduleName{" + StringUtil.latexify(mod.getName()) + "}}" + endl);
        //insert section and label tags for link
        result.append("\\section{" + mod.getName() + "}" + endl);
        result.append("\\label{sec:" + mod.getName() + "}" + endl);
        //insert link at beginning of document; assume we already have "\maketitle"
        //as we should have visited a Definition before visiting a Module
        result.insert(result.indexOf("\\maketitle") + ".maketitle".length(), "\\hyperref[sec:" + mod.getName() + "]{" + mod.getName() + "}\\\\" + endl);

        if (isVisited(mod))
            return;
        for (ModuleItem mi : mod.getItems()) {
            mi.accept(this);
        }
        visit((DefinitionItem) mod);
        result.append("\\end{module}" + endl);
    }

    @Override
    public void visit(Rule rule) {
        // termComment = false;
        Attributes atts = rule.getAttributes(); 
        boolean process = false;
        for(String tag : options.experimental.documentation) {
            if(atts.containsKey(tag)) {
                process = true;
                break;
            }
        }
        if(process) super.visit(rule);
    }
}
