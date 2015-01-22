// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.utils;

import java.io.*;

import org.kframework.parser.concrete.DefinitionLocalKParser;
import org.kframework.utils.errorsystem.KExceptionManager;

public class ResourceExtractor {

    public static void Extract(String resource, File destination) {
        try (
            InputStream k2 = new BufferedInputStream(DefinitionLocalKParser.resourceDomain().getResourceAsStream(resource));
            OutputStream os = new BufferedOutputStream(new FileOutputStream(destination))) {

            while (true) {
                int reader = k2.read();
                if (reader >= 0) {
                    os.write(reader);
                } else
                    break;
            }
        } catch (IOException e) {
            throw KExceptionManager.internalError("IO error detected writing to "
                    + destination.getAbsolutePath(), e);
        }
    }

    public static void ExtractDefSDF(File basePath) {
        if (!basePath.exists() && !basePath.mkdirs()) {
            throw KExceptionManager.internalError("Could not create directory " + basePath);
        }
        Extract("/Concrete.sdf", new File(basePath.getAbsoluteFile() + "/Concrete.sdf"));
        Extract("/Common.sdf", new File(basePath.getAbsoluteFile() + "/Common.sdf"));
        Extract("/KBuiltinsBasic.sdf", new File(basePath.getAbsoluteFile() + "/KBuiltinsBasic.sdf"));
        Extract("/KTechnique.sdf", new File(basePath.getAbsoluteFile() + "/KTechnique.sdf"));
        Extract("/Variables.sdf", new File(basePath.getAbsoluteFile() + "/Variables.sdf"));
    }

    public static void ExtractGroundSDF(File basePath) {
        if (!basePath.exists() && !basePath.mkdirs()) {
            throw KExceptionManager.internalError("Could not create directory " + basePath);
        }
        Extract("/Concrete.sdf", new File(basePath.getAbsoluteFile() + "/Concrete.sdf"));
        Extract("/Common.sdf", new File(basePath.getAbsoluteFile() + "/Common.sdf"));
        Extract("/KBuiltinsBasic.sdf", new File(basePath.getAbsoluteFile() + "/KBuiltinsBasic.sdf"));
        Extract("/KTechnique.sdf", new File(basePath.getAbsoluteFile() + "/KTechnique.sdf"));
    }

    public static void ExtractProgramSDF(File basePath) {
        if (!basePath.exists() && !basePath.mkdirs()) {
            throw KExceptionManager.internalError("Could not create directory " + basePath);
        }
        Extract("/Common.sdf", new File(basePath.getAbsoluteFile() + "/Common.sdf"));
        Extract("/KBuiltinsBasic.sdf", new File(basePath.getAbsoluteFile() + "/KBuiltinsBasic.sdf"));
    }
}
