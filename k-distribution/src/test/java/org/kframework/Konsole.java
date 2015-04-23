// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework;

import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.main.GlobalOptions;
import org.kframework.tiny.Rewriter;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URISyntaxException;
import java.util.function.BiFunction;

/**
 * A small console stub. Will need development. Tracked by #1441.
 */

public class Konsole {
    public static void main(String[] args) throws IOException, URISyntaxException {
        String definitionFilename = args[0];
        String mainModuleName = args[1];
        String programModuleName = args[2];

        KExceptionManager kem = new KExceptionManager(new GlobalOptions());

        CompiledDefinition compiledDef =
                new Kompile(new KompileOptions(), FileUtil.testFileUtil(), kem, false).run(new File(definitionFilename), mainModuleName, programModuleName, "K");

        Module module = compiledDef.executionModule();
        BiFunction<String, Source, K> programParser = compiledDef.getProgramParser();
        Rewriter rewriter = new org.kframework.tiny.Rewriter(module);
        String cmd;

        do {
            System.out.print(">");
            BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
            cmd = br.readLine();
            if (cmd.startsWith("rw")) {
                K result = rewriter.execute(programParser.apply(cmd.substring(2), Source.apply("<command line>")));
                System.out.println("=> " + result);
            } else if (cmd.equals("exit")) {
                break;
            } else
                System.out.println("Unknown command.");
            kem.print();
            kem.getExceptions().clear();
        } while (true);
        System.out.println("Bye!");
    }
}
