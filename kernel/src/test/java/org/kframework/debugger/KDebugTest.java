package test.java.org.kframework.debugger;

import com.google.inject.Injector;
import com.google.inject.Module;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.kframework.krun.KRunFrontEnd;

import java.util.List;

/**
 * Created by Manasvi on 6/19/15.
 *
 * Test File for the Debugger Interface Implementation
 */
public class KDebugTest {

    @BeforeClass
    public static void setup() {
        List<Module> modules = KRunFrontEnd.getDefinitionSpecificModules();
    }



}
