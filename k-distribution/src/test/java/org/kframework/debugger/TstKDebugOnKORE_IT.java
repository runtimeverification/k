package org.kframework.debugger;

import com.google.inject.Guice;
import com.google.inject.Injector;
import org.junit.BeforeClass;
import org.junit.rules.TestName;
import org.kframework.backend.java.symbolic.JavaSymbolicCommonModule;
import org.kframework.backend.java.symbolic.Stage;
import org.kframework.builtin.Sorts;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.DefinitionScoped;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.inject.SimpleScope;
import org.kframework.utils.options.SMTOptions;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;


/**
 * Created by Manasvi on 6/19/15.
 * <p>
 * Test File for the Debugger Interface Implementation
 */
public class TstKDebugOnKORE_IT {


    @org.junit.Rule
    public TestName name = new TestName();

    protected File testResource(String baseName) throws URISyntaxException {
        return new File(TstKDebugOnKORE_IT.class.getResource(baseName).toURI());
    }

    @BeforeClass
    public void setup() throws IOException, URISyntaxException {
        String filename = "/convertor-tests/" + name.getMethodName() + ".k";

        File definitionFile = testResource(filename);
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());

        try {
            CompiledDefinition compiledDef = new Kompile(new KompileOptions(), FileUtil.testFileUtil(), kem, false).run(definitionFile, "IMP", "IMP-SYNTAX", Sorts.K());
            SimpleScope requestScope = new SimpleScope();
            Injector injector = Guice.createInjector(new JavaSymbolicCommonModule() {
                @Override
                protected void configure() {
                    super.configure();
                    bind(GlobalOptions.class).toInstance(new GlobalOptions());
                    bind(SMTOptions.class).toInstance(new SMTOptions());
                    bind(Stage.class).toInstance(Stage.REWRITING);
                    bind(FileSystem.class).to(PortableFileSystem.class);
                    bind(FileUtil.class).toInstance(FileUtil.testFileUtil());

                    bindScope(RequestScoped.class, requestScope);
                    bindScope(DefinitionScoped.class, requestScope);
                }
            });

        } finally {

        }

    }
}
