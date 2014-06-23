// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.krun;

import java.io.BufferedReader;
import java.io.Console;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.HashMap;
import java.util.Map;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.compile.ConfigurationCleaner;
import org.kframework.compile.FlattenModules;
import org.kframework.compile.transformers.AddTopCellConfig;
import org.kframework.compile.transformers.Cell2DataStructure;
import org.kframework.compile.utils.CompileDataStructures;
import org.kframework.compile.utils.ConfigurationStructureVisitor;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.Configuration;
import org.kframework.kil.DataStructureBuiltin;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.Definition;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.ResolveVariableAttribute;
import org.kframework.kompile.KompileOptions;
import org.kframework.kompile.KompileOptions.Backend;
import org.kframework.krun.KRunOptions.ConfigurationCreationOptions;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class ExecutionContext {

    private final Context context;
    private final Definition definition;
    private final Term initialConfiguration;
    private final Stopwatch sw;
        
    //public final String kdir;
    
    //public final String krunDir, krunTempDir, maude_in, maude_out, maude_err, maude_output, processed_maude_output, krun_output;    

    public ExecutionContext(KRunOptions krunOptions, ConfigurationCreationOptions ccOptions, Stopwatch sw) {
        
        
        this.sw = sw;
        
        KompileOptions kompileOptions = BinaryLoader.load(KompileOptions.class,
                new File(ccOptions.definitionLoading.definition(),
                        "kompile-options.bin").getAbsolutePath(), krunOptions.global.debug);
        //merge krun options into kompile options object
        kompileOptions.global = krunOptions.global;
        
        sw.printIntermediate("Loading serialized kompile options");
        
        context = new Context(krunOptions, ccOptions, kompileOptions);

        context.dotk = new File(
                ccOptions.definitionLoading.definition().getParent() + File.separator
                        + ".k");
        if (!context.dotk.exists()) {
            context.dotk.mkdirs();
        }
        context.kompiled = ccOptions.definitionLoading.definition();

        sw.printIntermediate("Initializing definition paths");

        definition = getDefinition(sw, context);

        sw.printIntermediate("Preprocessing definition");

        Configuration cfg = BinaryLoader.load(Configuration.class, new File(context.kompiled, "configuration.bin").getAbsolutePath(), context);

        sw.printIntermediate("Reading configuration from binary");
        
        initialConfiguration = makeConfiguration(ccOptions, cfg, krunOptions.io());
    }


    public static Definition getDefinition(Stopwatch sw, Context context)
            throws AssertionError {
        KompileOptions kompileOptions = context.kompileOptions;
        File serializedDefinition;
        if (kompileOptions.backend == Backend.MAUDE || kompileOptions.backend == Backend.SYMBOLIC ||
                kompileOptions.backend == Backend.JAVA) {
            serializedDefinition = new File(context.kompiled, "defx-" + kompileOptions.backend.name().toLowerCase() + ".bin");
        } else {
            throw new AssertionError("currently only three execution backends are supported: MAUDE, SYMBOLIC, and JAVA");
        }
        if (!serializedDefinition.exists()) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, 
                    "Could not find the compiled definition.", null, serializedDefinition.getAbsolutePath()));
        }
        Definition javaDef = BinaryLoader.load(Definition.class, serializedDefinition.getAbsolutePath(), context);

        sw.printIntermediate("Reading definition from binary");

        // This is essential for generating maude
        javaDef = new FlattenModules(context).compile(javaDef, null);

        sw.printIntermediate("Flattening modules");

        javaDef = (Definition) new AddTopCellConfig(context).visitNode(javaDef);

        sw.printIntermediate("Adding top cell to configuration");
        
        ConfigurationStructureVisitor cfgStrVisitor =
                new ConfigurationStructureVisitor(context);
        cfgStrVisitor.visitNode(javaDef);
        context.setMaxConfigurationLevel(cfgStrVisitor.getMaxLevel());
        
        sw.printIntermediate("Computing configuration abstraction");

        javaDef.preprocess(context);
        
        return javaDef;
    }
    

    public Term makeConfiguration(ConfigurationCreationOptions options, Configuration cfg,
                                         boolean io) {

        if (options.term()) {
            sw.printIntermediate("Parse term");
            return new RunProcess().runParserOrDie(options.parser(context),
                    options.pgm(), false, null, context);
        }

        HashMap<String, Term> output = new HashMap<String, Term>();
        for (Map.Entry<String, Pair<String, String>> entry 
                : options.configVars(context).entrySet()) {
            String name = entry.getKey();
            String value = entry.getValue().getLeft();
            String parser = entry.getValue().getRight();
            if (!context.configVarSorts.containsKey(name)) {
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, 
                        "User specified configuration variable " + name + " which does not exist."));
            }
            String startSymbol = context.configVarSorts.get(name);
            Term parsed = new RunProcess().runParserOrDie(parser, value, false, startSymbol, context);
            parsed = (Term) new ResolveVariableAttribute(context).visitNode(parsed);
            output.put("$" + name, parsed);
        }
        sw.printIntermediate("Parse configuration variables");
        if (io) {
            DataStructureSort myList = context.dataStructureListSortOf(DataStructureSort.DEFAULT_LIST_SORT);
            if (myList != null) {
                output.put("$noIO", DataStructureBuiltin.empty(myList));
            }
            output.put("$stdin", StringBuiltin.EMPTY);
        } else {
            String stdin = getStdinBuffer();
            KApp noIO = KApp.of(KLabelConstant.of("'#noIO", context));
            DataStructureSort myList = context.dataStructureListSortOf(DataStructureSort.DEFAULT_LIST_SORT);
            if (myList != null) {
                output.put("$noIO", DataStructureBuiltin.element(myList, noIO));
            }
            output.put("$stdin", StringBuiltin.kAppOf(stdin));
        }

        sw.printIntermediate("Make configuration");

        return plug(output, cfg);
    }
    
    private String getStdinBuffer() {
        String buffer = "";

        try {
            BufferedReader br = new BufferedReader(
                    new InputStreamReader(System.in));
            // detect if the input comes from console or redirected
            // from a pipeline
            Console c = System.console();
            if (c == null && br.ready()) {
                buffer = br.readLine();
            }
        } catch (IOException e) {
            if (context.globalOptions.debug) {
                e.printStackTrace();
            }
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, 
                    "IO error detected reading from stdin"));
        }
        if (buffer == null) {
            return "";
        }
        return buffer + "\n";
    }

    public Term plug(Map<String, Term> args, Configuration cfg) {
        ASTNode cfgCleanedNode = null;
        cfgCleanedNode = new ConfigurationCleaner(context).visitNode(cfg);
        
        Term cfgCleaned;
        if (cfgCleanedNode == null) {
            cfgCleaned = Bag.EMPTY;
        } else {
            if (!(cfgCleanedNode instanceof Configuration)) {
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                        KExceptionGroup.INTERNAL,
                        "Configuration Cleaner failed.", cfg.getFilename(), cfg
                        .getLocation()));
            }
            cfgCleaned = ((Configuration) cfgCleanedNode).getBody();
        }

        sw.printIntermediate("Plug configuration variables");

        Term configuration = (Term) new SubstitutionFilter(args, context).visitNode(cfgCleaned);
        configuration = (Term) new Cell2DataStructure(context).visitNode(configuration);
        configuration = (Term) new CompileDataStructures(context).visitNode(configuration);
        return configuration;
    }
    
    public Term getInitialConfiguration() {
        return initialConfiguration;
    }
    
    public Context getContext() {
        return context;
    }
    
    public Definition getDefinition() {
        return definition;
    }
}
