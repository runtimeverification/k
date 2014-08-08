// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.utils;

import java.io.*;

import org.kframework.utils.general.GlobalSettings;

public class ResourceExtractor {

    public static void Extract(String resource, File destination) {
        try (
            InputStream k2 = new BufferedInputStream(Object.class.getResourceAsStream(resource));
            OutputStream os = new BufferedOutputStream(new FileOutputStream(destination))) {

            while (true) {
                int reader = k2.read();
                if (reader >= 0) {
                    os.write(reader);
                } else
                    break;
            }
        } catch (IOException e) {
            GlobalSettings.kem.registerInternalError("IO error detected writing to "
                    + destination.getAbsolutePath(), e);
        }
    }

    public static void ExtractDefSDF(File basePath) {
        basePath.mkdirs();
        Extract("/sdf/Concrete.sdf", new File(basePath.getAbsoluteFile() + "/Concrete.sdf"));
        Extract("/sdf/Common.sdf", new File(basePath.getAbsoluteFile() + "/Common.sdf"));
        Extract("/sdf/KBuiltinsBasic.sdf", new File(basePath.getAbsoluteFile() + "/KBuiltinsBasic.sdf"));
        Extract("/sdf/KTechnique.sdf", new File(basePath.getAbsoluteFile() + "/KTechnique.sdf"));
        Extract("/sdf/Variables.sdf", new File(basePath.getAbsoluteFile() + "/Variables.sdf"));
    }

    public static void ExtractGroundSDF(File basePath) {
        basePath.mkdirs();
        Extract("/sdf/Concrete.sdf", new File(basePath.getAbsoluteFile() + "/Concrete.sdf"));
        Extract("/sdf/Common.sdf", new File(basePath.getAbsoluteFile() + "/Common.sdf"));
        Extract("/sdf/KBuiltinsBasic.sdf", new File(basePath.getAbsoluteFile() + "/KBuiltinsBasic.sdf"));
        Extract("/sdf/KTechnique.sdf", new File(basePath.getAbsoluteFile() + "/KTechnique.sdf"));
    }

    public static void ExtractProgramSDF(File basePath) {
        basePath.mkdirs();
        Extract("/sdf/Common.sdf", new File(basePath.getAbsoluteFile() + "/Common.sdf"));
        Extract("/sdf/KBuiltinsBasic.sdf", new File(basePath.getAbsoluteFile() + "/KBuiltinsBasic.sdf"));
    }
}
