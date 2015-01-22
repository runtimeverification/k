// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.backend.html;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.PosterBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;

import com.google.inject.Inject;

public class HtmlBackend extends PosterBackend {

    private final FileUtil files;

    @Inject
    HtmlBackend(Stopwatch sw, Context context, FileUtil files) {
        super(sw, context);
        this.files = files;
    }

    @Override
    public void run(Definition definition) {
        HTMLFilter htmlFilter = new HTMLFilter(context);
        htmlFilter.visitNode(definition);

        String html = htmlFilter.getHTML();

        files.saveToDefinitionDirectory(FilenameUtils.removeExtension(definition.getMainFile().getName()) + ".html", html);
        files.saveToDefinitionDirectory("k-definition.css", files.loadFromKBase("include/html/k-definition.css"));

        sw.printIntermediate("Generating HTML");

    }
}
