// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.utils.kastparser;

import static org.junit.Assert.*;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;

import org.apache.commons.io.FileUtils;
import org.junit.Test;
import org.kframework.attributes.Source;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KSequence;
import org.kframework.kil.Term;


public class KastParserTest {

    @Test
    public void testLoadKastData() throws URISyntaxException, IOException {
        File f = new File(getClass().getResource("/kast-data.kast").toURI());
        String kast = FileUtils.readFileToString(f);
        Term t = KastParser.parse(kast, Source.apply(f.getAbsolutePath()));
        assertTrue(t instanceof KSequence);
        Term item = ((KSequence) t).getContents().get(0);
        assertEquals("TranslationUnit", ((KLabelConstant)((KApp) item).getLabel()).getLabel());
    }
}
