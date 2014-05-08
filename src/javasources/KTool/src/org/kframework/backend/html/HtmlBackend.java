// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend.html;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;

import java.io.File;
import java.io.IOException;

public class HtmlBackend extends BasicBackend {

    public HtmlBackend(Stopwatch sw, Context context) {
        super(sw, context);
    }

    @Override
    public void run(Definition definition) throws IOException {
        String fileSep = System.getProperty("file.separator");
        String htmlIncludePath = KPaths.getKBase(false) + fileSep + "include" + fileSep + "html" + fileSep;
        HTMLFilter htmlFilter = new HTMLFilter(htmlIncludePath, context);
        htmlFilter.visitNode(definition);

        String html = htmlFilter.getHTML();

        FileUtil.save(options.output().getAbsolutePath(), html);
        FileUtil.save(new File(options.output().getCanonicalFile().getParent(), "k-definition.css").getCanonicalPath(),
                FileUtil.getFileContent(htmlIncludePath + "k-definition.css"));

        sw.printIntermediate("Generating HTML");

    }

    @Override
    public String getDefaultStep() {
        return "FirstStep";
    }
}
