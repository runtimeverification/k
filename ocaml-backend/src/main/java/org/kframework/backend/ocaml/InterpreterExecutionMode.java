// Copyright (c) 2016-2018 Runtime Verification, Inc. (RV-Match team). All Rights Reserved.
package org.kframework.backend.ocaml;

import com.google.inject.Inject;
import org.kframework.definition.Definition;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.krun.KRun;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.binary.BinaryParser;
import org.kframework.rewriter.Rewriter;
import org.kframework.unparser.ToBinary;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;

import java.io.*;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.util.function.Function;


public class InterpreterExecutionMode implements ExecutionMode {

    private final KExceptionManager kem;
    private final FileUtil files;
    private final DefinitionToOcaml converter;
    private final KRunOptions options;

    @Inject
    public InterpreterExecutionMode(
            KExceptionManager kem,
            FileUtil files,
            GlobalOptions globalOptions,
            KompileOptions kompileOptions,
            CompiledDefinition def,
            OcamlRewriter.InitializeDefinition init,
            KRunOptions options) {
        this.kem = kem;
        this.files = files;
        this.converter = new DefinitionToOcaml(kem, files, globalOptions, kompileOptions, null);
        converter.initialize(init.serialized, def);
        this.options = options;
    }

    @Override
    public Tuple2<K, Integer> execute(KRun.InitialConfiguration k, Function<Definition, Rewriter> unused, CompiledDefinition compiledDefinition) {
        OcamlRewriter rewriter = new OcamlRewriter(files, converter, options);
        K config = k.theConfig;
        k.theConfig = null;
        config = converter.preprocess(config);
        File input = files.resolveTemp("run.in");
        files.resolveTemp(".").mkdirs();
        try (OutputStream out = new BufferedOutputStream(new FileOutputStream(input))) {
            ToBinary.apply(out, config);
        } catch (IOException e) {
            throw KEMException.internalError("Could not write to file in temp directory.", e);
        }
        config = null; // so that the initial configuration can be garbage collected
        File output = files.resolveTemp("run.out");
        int exit = rewriter.execOcaml(files.resolveTemp("."),
                files.resolveKompiled("interpreter").getAbsolutePath(),
                files.resolveKompiled("realdef.cma").getAbsolutePath(),
                "-t", input.getAbsolutePath(), "binaryfile", "--output-file",
                output.getAbsolutePath(),
                "--depth", options.depth == null ? "-1" : options.depth.toString()
                );

        try (FileChannel channel = FileChannel.open(output.toPath())) {
            ByteBuffer buf = channel.map(FileChannel.MapMode.READ_ONLY, 0, channel.size());
            K result = BinaryParser.parse(buf);
            return Tuple2.apply(result, exit);
        } catch (IOException e) {
            throw KEMException.internalError("Could not read from file in temp directory.", e);
        }
    }
}
