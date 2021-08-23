// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.parser;

import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.binary.BinaryParser;
import org.kframework.parser.inner.ParseInModule;
import org.kframework.parser.inner.generator.RuleGrammarGenerator;
import org.kframework.parser.inner.kernel.KSyntax2Bison;
import org.kframework.parser.inner.kernel.Scanner;
import org.kframework.parser.json.JsonParser;
import org.kframework.parser.kast.KastParser;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;

import javax.json.Json;
import javax.json.JsonObject;
import javax.json.JsonReader;

public class KRead {

    private final KExceptionManager kem;
    private final FileUtil files;
    private final InputModes input;
    private final GlobalOptions globalOptions;

    public KRead(
            KExceptionManager kem,
            FileUtil files,
            InputModes input,
            GlobalOptions globalOptions
    ) {
        this.kem = kem;
        this.files = files;
        this.input = input;
        this.globalOptions = globalOptions;
    }

    public K prettyRead(Module mod, Sort sort, CompiledDefinition def, Source source, String stringToParse) {
        return prettyRead(mod, sort, def, source, stringToParse, this.input);
    }

    public K prettyRead(Module mod, Sort sort, CompiledDefinition def, Source source, String stringToParse, InputModes inputMode) {
        switch (inputMode) {
            case BINARY:
            case JSON:
            case KAST:
                return deserialize(stringToParse, inputMode, source);
            case KORE:
                return new KoreParser(mod.sortAttributesFor()).parseString(stringToParse);
            case PROGRAM:
                return def.parseSingleTerm(mod, sort, kem, stringToParse, source);
            default:
                throw KEMException.criticalError("Unsupported input mode: " + inputMode);
        }
    }

    public void createBisonParser(Module mod, Sort sort, File outputFile, boolean glr, String bisonFile, long stackDepth) {
        Stopwatch sw = new Stopwatch(globalOptions);
        try (ParseInModule parseInModule = RuleGrammarGenerator.getCombinedGrammar(mod, true, null, true, false)) {
            try (Scanner scanner = parseInModule.getScanner(kem.options)) {
                File scannerFile = files.resolveTemp("scanner.l");
                File scanHdr = files.resolveTemp("scanner.h");
                File parserFile = files.resolveTemp("parser.y");
                scanner.writeStandaloneScanner(scannerFile);
                KSyntax2Bison.writeParser(parseInModule.getParsingModule(), parseInModule.getDisambiguationModule(), scanner, sort, parserFile, glr, stackDepth, kem);
                int exit = files.getProcessBuilder()
                  .directory(files.resolveTemp("."))
                  .command("flex", "--header-file=" + scanHdr.getAbsolutePath(), "-w", scannerFile.getAbsolutePath())
                  .inheritIO()
                  .start()
                  .waitFor();
                if (exit != 0) {
                    throw KEMException.internalError("flex returned nonzero exit code: " + exit + "\n");
                }
                exit = files.getProcessBuilder()
                  .directory(files.resolveTemp("."))
                  .command("bison", "-d", "-Wno-other", "-Wno-conflicts-sr", "-Wno-conflicts-rr", parserFile.getAbsolutePath())
                  .inheritIO()
                  .start()
                  .waitFor();
                if (exit != 0) {
                    throw KEMException.internalError("bison returned nonzero exit code: " + exit + "\n");
                }
                List<String> command = new ArrayList<>();
                command.addAll(Arrays.asList(
                      "gcc",
                      files.resolveKInclude("cparser/main.c").getAbsolutePath(),
                      files.resolveTemp("lex.yy.c").getAbsolutePath(),
                      files.resolveTemp("parser.tab.c").getAbsolutePath(),
                      "-iquote", files.resolveTemp(".").getAbsolutePath(),
                      "-iquote", files.resolveKInclude("cparser").getAbsolutePath(),
                      "-o", outputFile.getAbsolutePath()));
                if (bisonFile != null) {
                    command.add(files.resolveWorkingDirectory(bisonFile).getAbsolutePath());
                }
                exit = files.getProcessBuilder()
                  .command(command.toArray(new String[0]))
                  .inheritIO()
                  .start()
                  .waitFor();
                if (exit != 0) {
                    throw KEMException.internalError("gcc returned nonzero exit code: " + exit + "\n");
                }
            } catch(IOException | InterruptedException e) {
              throw KEMException.internalError("Failed to execute process.", e);
            }
        }
        sw.printIntermediate("  New Bison parser: " + mod.name());
    }

    public K deserialize(String stringToParse, Source source) {
        return deserialize(stringToParse, this.input, source);
    }

    public static K deserialize(String stringToParse, InputModes inputMode, Source source) {
        switch (inputMode) {
            case BINARY:
                return BinaryParser.parse(stringToParse.getBytes());
            case JSON:
                return JsonParser.parse(stringToParse);
            case KAST:
                return KastParser.parse(stringToParse, source);
            default:
                throw KEMException.criticalError("Unsupported input mode for deserialization: " + inputMode);
        }
    }

    public static K autoDeserialize(byte[] kast, Source source) {
        if (BinaryParser.isBinaryKast(kast))
            return BinaryParser.parse(kast);

        InputStream input = new ByteArrayInputStream(kast);
        int c;
        try {
            while (Character.isWhitespace(c = input.read()));
        } catch (IOException e) {
            throw KEMException.criticalError("Could not read output from parser: ", e);
        }

        if ( c == '{' ) {
            JsonReader reader = Json.createReader(new ByteArrayInputStream(kast));
            JsonObject data = reader.readObject();
            return JsonParser.parseJson(data);
        }

        try {
            return KastParser.parse(new String(kast), source);
        } catch ( KEMException e ) {
            throw KEMException.criticalError("Could not read input: " + source.source());
        }
    }
}
