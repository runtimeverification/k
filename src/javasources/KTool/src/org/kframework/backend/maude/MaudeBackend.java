// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend.maude;

import org.apache.commons.lang3.StringEscapeUtils;
import org.kframework.backend.BasicBackend;
import org.kframework.compile.sharing.FreshVariableNormalizer;
import org.kframework.kil.Definition;
import org.kframework.kil.Production;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.StringBuilderUtil;
import org.kframework.utils.file.FileUtil;

import java.io.IOException;
import java.util.Map;

public class MaudeBackend extends BasicBackend {

    public MaudeBackend(Stopwatch sw, Context context) {
        super(sw, context);
    }

    @Override
    public void run(Definition definition) throws IOException {
        definition = (Definition) new FreshVariableNormalizer(context).visitNode(definition);
        MaudeFilter maudeFilter = new MaudeFilter(context);
        maudeFilter.visitNode(definition);

        final String mainModule = definition.getMainModule();
        StringBuilder maudified = maudeFilter.getResult();
        StringBuilderUtil.replaceFirst(maudified, mainModule, mainModule + "-BASE");

        FileUtil.save(context.kompiled.getAbsolutePath() + "/base.maude", maudified);
        sw.printIntermediate("Generating Maude file");

        StringBuilder consTable = getLabelTable(definition);
        FileUtil.save(context.dotk.getAbsolutePath() + "/consTable.txt", consTable);
    }
    
    private StringBuilder getLabelTable(Definition def) {
        StringBuilder b = new StringBuilder();
        /*
        b.append("# Each line has the SDF cons label, a literal tab, a space or * to mark preferred productions,\n"+
                 "# then P followed by the klabel for ordinary productions, a B for brackets,\n"+
                 "# or L followed by the klabel, a tab, and the separator.\n"+
                 "# strings escaped with \\t for tabs and \\n for newlines. # is comment to end of line");
         */
        for (Map.Entry<String,Production> e : context.conses.entrySet()) {
            String cons = e.getKey();
            Production p = e.getValue();
            b.append(StringEscapeUtils.escapeJava(cons));
            b.append('\t');
            if (p.containsAttribute("prefer")) {
                b.append('*');
            } else {
                b.append(' ');
            }
            if (p.isListDecl()) {
                b.append('L');
                b.append(StringEscapeUtils.escapeJava(p.getKLabel()));
                b.append('\t');
                b.append(StringEscapeUtils.escapeJava(((UserList)p.getItems().get(0)).getSeparator()));
            } else if (p.containsAttribute("bracket")) {
                b.append('B');
            } else {
                b.append('P');
                b.append(StringEscapeUtils.escapeJava(p.getKLabel()));
            }
            b.append('\n');            
        }
        return b;
    }

    @Override
    public String getDefaultStep() {
        return "LastStep";
    }
}
