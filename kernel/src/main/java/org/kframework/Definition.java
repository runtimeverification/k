// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework;

import com.google.common.collect.Lists;
import com.google.common.io.Files;
import com.google.inject.util.Providers;
import org.kframework.attributes.Source;
import org.kframework.kompile.Kompile;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.concrete2kore.ParserUtils;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

@API
public class Definition {

    /**
     * Parses the text to create a {@link Definition} object.
     * The main module of the definition will be last module defined in the text file.
     */
    public static org.kframework.definition.Definition from(String definitionText) {
        Pattern pattern = Pattern.compile("(?:^|\\s)module ([A-Z][A-Z\\-]*)");
        Matcher m = pattern.matcher(definitionText);
        if(!m.find()) {
            throw new RuntimeException("Could not find any module in the definition");
        }
        String nameOfLastModule = m.group(m.groupCount());
        return from(definitionText, nameOfLastModule, Source.apply("generated"));
    }

    /**
     * Parses the text to create a {@link Definition} object.
     */
    public static org.kframework.definition.Definition from(String definitionText, String mainModuleName) {
        return from(definitionText, mainModuleName, Source.apply("generated"));
    }

    /**
     * Parses the text to create a {@link Definition} object.
     */
    public static org.kframework.definition.Definition from(String definitionText, String mainModuleName, Source source) {
        return from(definitionText, mainModuleName, source, Lists.newArrayList(Kompile.BUILTIN_DIRECTORY));
    }

    /**
     * Parses the text to create a {@link Definition} object.
     */
    public static org.kframework.definition.Definition from(String definitionText, String mainModuleName, Source source, List<File> lookupDirectories) {
        File tempDir = Files.createTempDir();
        File theFileUtilTempDir = new File(tempDir.getAbsolutePath() + File.pathSeparator + "tempDir");
        File definitionDir = new File(tempDir.getAbsolutePath() + File.pathSeparator + "definitionDir");
        File workingDir = new File(tempDir.getAbsolutePath() + File.pathSeparator + "workingDir");
        File kompiledDir = new File(tempDir.getAbsolutePath() + File.pathSeparator + "kompiledDir");
        if(!theFileUtilTempDir.mkdir() || !definitionDir.mkdir() || !workingDir.mkdir() || !kompiledDir.mkdir()) {
            throw new AssertionError("Could not create one of the temporary directories");
        }
        GlobalOptions globalOptions = new GlobalOptions();
        KExceptionManager kem = new KExceptionManager(globalOptions);

        FileUtil fileUtil = new FileUtil(theFileUtilTempDir,
                Providers.of(definitionDir),
                workingDir,
                Providers.of(kompiledDir),
                globalOptions,
                System.getenv());
        ParserUtils parserUtils = new ParserUtils(fileUtil::resolveWorkingDirectory, kem, globalOptions);

        org.kframework.definition.Definition definition = parserUtils.loadDefinition(
                mainModuleName,
                mainModuleName,
                definitionText,
                source,
                workingDir,
                lookupDirectories,
                false
        );

        return definition;
    }
}
