package org.kframework.koreimplementation.convertors;

import org.junit.Test;
import org.kframework.definition.Module;
import scala.Option;

import java.io.IOException;

public class TstBackendOnKORE extends BaseTest {
    @Test
    public void kapp() throws IOException {
        sdfTest();
    }

    protected String convert(BaseTest.DefinitionWithContext defWithContext) {
        KILtoKORE kilToKore = new KILtoKORE(defWithContext.context);
        org.kframework.definition.Definition koreDef = kilToKore.apply(defWithContext.definition);
        String koreDefString = koreDef.toString();

        Module mod = koreDef.getModule("TEST").get();



        return koreDefString;
    }

    @Override
    protected String expectedFilePostfix() {
        return "-backend-expected.txt";
    }
}
