package ro.uaic.info.fmse.k2m.main;

import java.io.File;
import java.io.UnsupportedEncodingException;
import java.net.URLDecoder;

import ro.uaic.info.fmse.k2m.utils.FileUtil;

public class Kil2Maude {

	/**
	 * @param args
	 * @throws Exception
	 */
	public static void main(String[] args) throws Exception {
		// TODO Auto-generated method stub

		if (args.length == 1) {
			String file = args[0];
			// System.out.println(new File(file).exists());
			System.out.println(KILFiletoMEL(args[0]).trim());
			String load = "load \"" + getKBase(true) + "/core/maude/lib/k-prelude\"\n";
			String compile = " load \""
					+ getKBase(true)
					+ "/core/maude/compiler/all-tools\"\n loop compile .\n(compile SIMPLE-UNTYPED transitions \"transition=()\" superheats \"superheat=()\" supercools \"supercool=()\" .)\n quit\n";
			FileUtil.saveInFile("maudified.maude", load + KILFiletoMEL(file).trim() + "\n" + compile);
		} else if (args.length == 2) {
			// String definition = FileUtil.readFileAsString(args[0]);
			// String program = FileUtil.readFileAsString(args[1]);

			// String ast = KILProgram2Maude(definition, program);

			// FileUtil.saveInFile("pgm.maude", ast);
		} else {
			System.out.println("You must provide exactly one argument: <KIL> file name.");
		}
	}

	public static String windowfyPath(String file) {
		if (System.getProperty("os.name").toLowerCase().contains("win")) {
			file = file.replaceFirst("([a-zA-Z]):(.*)", "/cygdrive/$1$2");
			file = file.replaceAll("\\\\", "/");
		}
		return file;
	}

	public static boolean isDebugMode() {
		String path = new File(Kil2Maude.class.getProtectionDomain().getCodeSource().getLocation().getPath()).getAbsolutePath();
		return !path.endsWith(".jar");
	}
	
	/**
	 * Returns the K installation directory
	 * @param windowfy - if true, then the path will be transformed into /cygdirve/c/... when on windows (just for maude)
	 * @return The path to the K installation
	 */
	public static String getKBase(boolean windowfy) {
		// String env = System.getenv("K_BASE");
		String path = new File(Kil2Maude.class.getProtectionDomain().getCodeSource().getLocation().getPath()).getAbsolutePath();
		if (!path.endsWith(".jar"))
			path = new File(path).getParentFile().getParentFile().getParentFile().getAbsolutePath() + "/dist/bin/java/k3.jar";
		try {
			String decodedPath = URLDecoder.decode(path, "UTF-8");
			File parent = new File(decodedPath).getParentFile().getParentFile().getParentFile();
			if (windowfy)
				return windowfyPath(parent.getAbsolutePath());
			else
				return parent.getAbsolutePath();
		} catch (UnsupportedEncodingException e) {
			e.printStackTrace();
		}
		return null;
	}

	public static String KILProgram2Ast(String definition, String program) {
		try {
			Maude maude = new Maude(definition);
			return maude.getAst(program);
		} catch (Exception e) {
			e.printStackTrace();
		}

		System.exit(1);
		return null;
	}

	/**
	 * 
	 * @param Definition
	 *            XML string representing the definition
	 * @param Program
	 *            XML string representing the program
	 * @return The maudified program, ready to be runed.
	 */
	public static String KILProgram2Maude(String definition, String program, File defFile) {
		String ast = null;
		try {
			Maude maude = new Maude(definition);

			String fileName = defFile.getName().substring(0, defFile.getName().length() - 2);

			ast = "load ../" + fileName + "-compiled.maude\n";
			ast += "set show command off .\n erewrite #eval(__((_|->_((# \"PGM\"(.List{K})) , (\n\n";
			ast += maude.getAst(program);
			ast += "\n\n))),(.).Map))  .\n quit\n";
		} catch (Exception e) {
			e.printStackTrace();
		}

		return ast;
	}

	/**
	 * Transform file content into membership equational logic.
	 * 
	 * @param kil
	 * @return the MEL output as string
	 * @throws Exception
	 */
	public static String KILFiletoMEL(String xmlFilePath) throws Exception {
		String content = FileUtil.readFileAsString(xmlFilePath);
		return KILtoMEL(content).trim();
	}

	/**
	 * Transform argument into membership equational logic.
	 * 
	 * @param kil
	 * @return the MEL output as string
	 * @throws Exception
	 */
	public static String KILtoMEL(String kil) throws Exception {
		// Transformer transformer = new Transformer(kil);
		// return transformer.getMEL();
		Maude maude = new Maude(kil);
		long ms = System.currentTimeMillis();
		String mel = maude.getMEL();
		ms = (System.currentTimeMillis() - ms);
		// System.out.println("Time: " + ms + " ms.");

		return mel;
	}

}
