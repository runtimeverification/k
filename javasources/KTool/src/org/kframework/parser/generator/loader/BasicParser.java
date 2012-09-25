package org.kframework.parser.generator.loader;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Module;
import org.kframework.kil.Require;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.parser.basic.KParser;
import org.kframework.utils.XmlLoader;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KMessages;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.utils.file.FileUtil;
import org.kframework.utils.utils.file.KPaths;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class BasicParser {
	private List<DefinitionItem> moduleItems;
	private Map<String, Module> modulesMap;
	private List<String> filePaths;
	private File mainFile;
	private String mainModule;

	public BasicParser() {
	}

	/**
	 * Given a file, this method parses it and creates a list of modules from all of the included files.
	 * 
	 * @param filepath
	 */
	public void slurp(String fileName) {
		moduleItems = new ArrayList<DefinitionItem>();
		modulesMap = new HashMap<String, Module>();
		filePaths = new ArrayList<String>();

		try {
			File file = buildCanonicalPath("autoinclude.k", new File("."));
			if (file == null)
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, KMessages.ERR1004 + fileName + " autoimporeted for every definition ", fileName, ""));
			slurp2(file, new File("."));
			setMainFile(file);
			file = new File(fileName);
			if (!file.exists())
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, KMessages.ERR1004 + fileName + " given at console.", "", ""));
			slurp2(file, new File("."));
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private File buildCanonicalPath(String fileName, File parentFile) throws IOException {
		File file = new File(parentFile.getCanonicalFile().getParentFile().getCanonicalPath() + "/" + fileName);
		if (file.exists())
			return file;
		file = new File(KPaths.getKBase(false) + "/include/" + fileName);
		if (file.exists())
			return file;

		return null;
	}

	private void slurp2(File file, File parentFile) throws IOException {
		String cannonicalPath = file.getCanonicalPath();
		if (!filePaths.contains(cannonicalPath)) {
			filePaths.add(cannonicalPath);

			List<DefinitionItem> defItemList = parseFile(file);

			// go through every required file
			for (DefinitionItem di : defItemList) {
				if (di instanceof Require) {
					Require req = (Require) di;

					if (GlobalSettings.verbose)
						System.out.println("Including file: " + req.getValue());

					File newFile = buildCanonicalPath(req.getValue(), file);
					if (newFile == null)
						GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, KMessages.ERR1004 + req.getValue(), req.getFilename(), req.getLocation()));
					slurp2(newFile, file);
				}
			}

			// add the modules to the modules list and to the map for easy access
			for (DefinitionItem di : defItemList) {
				if (di instanceof Module) {
					Module m = (Module) di;
					this.moduleItems.add(m);
					this.modulesMap.put(m.getName(), m);
				}
			}
		}
	}

	public static List<DefinitionItem> parseFile(File file) {
		String content = FileUtil.getFileContent(file.getAbsolutePath());

		String parsed = KParser.ParseKString(content);
		Document doc = XmlLoader.getXMLDoc(parsed);
		XmlLoader.addFilename(doc.getFirstChild(), file.getAbsolutePath());
		XmlLoader.reportErrors(doc);

		NodeList nl = doc.getFirstChild().getChildNodes();
		List<DefinitionItem> defItemList = new ArrayList<DefinitionItem>();

		for (int i = 0; i < nl.getLength(); i++) {
			if (nl.item(i).getNodeType() == Node.ELEMENT_NODE) {
				Element elm = (Element) nl.item(i);
				defItemList.add((DefinitionItem) JavaClassesFactory.getTerm(elm));
			}
		}

		return defItemList;
	}

	public void setMainFile(File mainFile) {
		this.mainFile = mainFile;
	}

	public File getMainFile() {
		return mainFile;
	}

	public void setMainModule(String mainModule) {
		this.mainModule = mainModule;
	}

	public String getMainModule() {
		return mainModule;
	}

	public List<DefinitionItem> getModuleItems() {
		return moduleItems;
	}

	public void setModuleItems(List<DefinitionItem> moduleItems) {
		this.moduleItems = moduleItems;
	}

	public Map<String, Module> getModulesMap() {
		return modulesMap;
	}

	public void setModulesMap(Map<String, Module> modulesMap) {
		this.modulesMap = modulesMap;
	}
}
