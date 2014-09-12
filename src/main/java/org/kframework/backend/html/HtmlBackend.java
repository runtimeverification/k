// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend.html;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;

import com.google.inject.Inject;

import java.io.File;

public class HtmlBackend extends BasicBackend {

    @Inject
    HtmlBackend(Stopwatch sw, Context context) {
        super(sw, context);
    }

    @Override
    public void run(Definition definition) {
        String fileSep = System.getProperty("file.separator");
        String htmlIncludePath = JarInfo.getKBase(false) + fileSep + "include" + fileSep + "html" + fileSep;
        HTMLFilter htmlFilter = new HTMLFilter(htmlIncludePath, context);
        htmlFilter.visitNode(definition);

        String html = htmlFilter.getHTML();

        FileUtil.save(options.directory.getPath() + File.separator + FilenameUtils.removeExtension(new File(definition.getMainFile()).getName()) + ".html", html);
        FileUtil.save(options.directory.getPath() + File.separator + "k-definition.css",
                FileUtil.getFileContent(htmlIncludePath + "k-definition.css"));

        sw.printIntermediate("Generating HTML");

    }

    @Override
    public String getDefaultStep() {
        return "FirstStep";
    }

    @Override
    public boolean documentation() {
        return true;
    }

    @Override
    public boolean generatesDefinition() {
        return false;
    }
}
