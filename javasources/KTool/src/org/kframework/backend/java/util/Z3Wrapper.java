package org.kframework.backend.java.util;

import com.microsoft.z3.Z3Exception;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;

/**
 * @author Traian
 */
public class Z3Wrapper {
    public static boolean initialized = false;
    public static com.microsoft.z3.Context newContext() throws Z3Exception {
        if (!initialized) {
            String libz3 = "libz3";
            switch (GlobalSettings.os()) {
                case WIN:
                    libz3 += ".dll";
                    break;
                case UNIX:
                    libz3 += ".so";
                    break;
                case OSX:
                    libz3 += ".dylib";
            }
            System.load(KPaths.getJavaLibraryPath() + File.separator + libz3);
            initialized = true;
        }
        return new com.microsoft.z3.Context();
    }
}
