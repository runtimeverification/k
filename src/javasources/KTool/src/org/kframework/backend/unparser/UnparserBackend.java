package org.kframework.backend.unparser;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.ConcretizeSyntax;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.IOException;

public class UnparserBackend extends BasicBackend {
    private boolean unflattenFirst; // unflatten syntax before unparsing

    public UnparserBackend(Stopwatch sw, Context context) {
        super(sw, context);
        this.unflattenFirst = false;
    }

    public UnparserBackend(Stopwatch sw, Context context, boolean unflattenFirst) {
        super(sw, context);
        this.unflattenFirst = unflattenFirst;
    }

    @Override
    public void run(Definition definition) throws IOException {
        if (unflattenFirst) {
            ConcretizeSyntax concretizeSyntax = new ConcretizeSyntax(context);
            try {
                definition = (Definition)definition.accept(concretizeSyntax);
            } catch (TransformerException e) {
                System.err.println("Error unflattening syntax:");
                e.printStackTrace();
            }
        }
        UnparserFilter unparserFilter = new UnparserFilter(context);
        definition.accept(unparserFilter);

        String unparsedText = unparserFilter.getResult();

        FileUtil.save(context.dotk.getAbsolutePath() + "/def.k", unparsedText);

        FileUtil.save(options.directory.getPath() + File.separator + FilenameUtils.removeExtension(options.definition().getName()) + ".unparsed.k", unparsedText);
    }

    @Override
    public String getDefaultStep() {
        return "FirstStep";
    }

}
