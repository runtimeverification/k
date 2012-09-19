package org.kframework.utils;

import java.io.*;

public class ResourceExtractor {

	public static void Extract(String resource, File destination) throws IOException {
		BufferedInputStream k2 = new BufferedInputStream(Object.class.getResourceAsStream(resource));
		BufferedOutputStream os = new BufferedOutputStream(new FileOutputStream(destination));

		while (true) {
			int reader = k2.read();
			if (reader >= 0) {
				os.write(reader);
			} else
				break;
		}
		os.close();
	}

	public static void ExtractAllSDF(File basePath) throws IOException {
		File def = new File(basePath.getAbsolutePath() + "/def");
		def.mkdirs();
		Extract("/sdf/K3Disamb.sdf", new File(def.getAbsoluteFile() + "/K3Disamb.sdf"));
		Extract("/sdf/Common.sdf", new File(def.getAbsoluteFile() + "/Common.sdf"));
		Extract("/sdf/KBuiltinsBasic.sdf", new File(def.getAbsoluteFile() + "/KBuiltinsBasic.sdf"));
		Extract("/sdf/KTechnique.sdf", new File(def.getAbsoluteFile() + "/KTechnique.sdf"));
	}

	public static void ExtractProgramSDF(File basePath) throws IOException {
		File def = new File(basePath.getAbsolutePath() + "/pgm");
		def.mkdirs();
		Extract("/sdf/Common.sdf", new File(def.getAbsoluteFile() + "/Common.sdf"));
		Extract("/sdf/KBuiltinsBasic.sdf", new File(def.getAbsoluteFile() + "/KBuiltinsBasic.sdf"));
	}
}
