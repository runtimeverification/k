import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.junit.Test;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

public class Initialize {

	private Document doc;
	private Element root;

	public Initialize() {
		try {
			DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
			DocumentBuilder db;
			db = dbf.newDocumentBuilder();
			this.doc = db.newDocument();
			
			root = doc.createElement("tests");
			doc.appendChild(root);
			
			// Remove this thing.
			// StaticK.toolsDir = "/home/andrei.arusoaie/work/trunk/tests/tools";
			
		} catch (ParserConfigurationException e) {
		    System.out.println("Jenkins: " + e.getLocalizedMessage());
			System.exit(1);
		}
	}

	@Test
	public void testAll()
	{
		testExamples();
		testRegression();
	}
	
	public void testExamples() {

		String kframework = StaticK.kbasedir;

		String examplesDefDir = kframework + StaticK.fileSep + "dist"
				+ StaticK.fileSep + "examples";
		String examplesTestDir = kframework + StaticK.fileSep + "tests"
				+ StaticK.fileSep + "examples";

		// iterate trough examples
		List<String> defs = getKFilesFromDir(examplesDefDir);
		for (String def : defs)
		{
			String defRelPath = def.substring(kframework.length());
			String programsRelDir = new File(def).getParent().substring(kframework.length());
			String testsRelDir = (examplesTestDir + new File(def).getParentFile().getAbsolutePath().substring(examplesDefDir.length())).substring(kframework.length());
			
			root.appendChild(createTest(kframework, defRelPath, programsRelDir, testsRelDir, doc, "example"));
		}
		
		save();
	}

	public void testRegression()
	{
		String kframework = StaticK.kbasedir;

		String regressionTests = kframework + StaticK.fileSep + "tests" + StaticK.fileSep + "regression";
		
		List<String> regTests = getKFilesFromDir(regressionTests);
		
		for(String t : regTests)
		{
			String defRelPath = t.substring(kframework.length());
			String programsRelDir = new File(t).getParent().substring(kframework.length());
			String testsRelDir = programsRelDir + StaticK.fileSep + "tests";
			root.appendChild(createTest(kframework, defRelPath, programsRelDir, testsRelDir, doc, "regression"));
		}
		
		save();
	}
	
	private List<String> getKFilesFromDir(String dir) {
		List<String> files = new LinkedList<String>();

		if (new File(dir).isHidden())
			return files;
		
		File directory = new File(dir);
//		System.out.println("DIR: " + directory.getAbsolutePath());
		String[] dirFiles = directory.list();
		List<String> temp = new LinkedList<String>();
		for (int i = 0; i < dirFiles.length; i++) {
			File file = new File(dir + StaticK.fileSep + dirFiles[i]);
			if (file.isFile() && file.getAbsolutePath().endsWith(".k")) {
				temp.add(file.getAbsolutePath());
			} else if (file.isDirectory()) {
				files.addAll(getKFilesFromDir(file.getAbsolutePath()));
			}
		}

		if (temp.size() == 1)
			files.addAll(temp);
		else if (temp.size() > 1)
		{
			String best = temp.get(0);
			for(String file:temp)
				if (score(file) > score(best))
					best = file;
			files.add(best);
		}
		
		return files;
	}

	private int score(String best) {
		File file = new File(best);
		String name = file.getName();
		String dirParent = file.getAbsoluteFile().getParent();
		
		if (new File(dirParent).getName().equals(name.replaceAll("\\.\\S+$", "")))
			return Integer.MAX_VALUE;
		
		int score = 0;
		String[] split = name.split("-");
		for(int i = 0; i < split.length; i++)
			if (dirParent.matches("/" + split[i] + "/"))
				score ++;
		return score;
	}

	private Element createTest(String rootPath, String defRelPath,
			String programsRelDir, String testsRelDir, Document root, String mainTagName) {
		
		// DEFAULTS
		File f = new File(rootPath + defRelPath);
		String defDir = f.getParent();
		String defName = f.getName();
		String defNameNoExtension = f.getName().replaceAll("\\..*?$", "");
		String moduleName = defNameNoExtension.toUpperCase();
		String compiledDef = defNameNoExtension + "-compiled.maude";
		String programsExtension = defNameNoExtension;
		String programsDir = rootPath + programsRelDir;
		
		/**** CHANGE DEFAULTS if config.xml is present in testsDir ****/
		String xmlConfigFile = rootPath + testsRelDir + StaticK.fileSep + "config.xml";
		Element config = null;
		if (new File(xmlConfigFile).exists())
		{
			Document doc = Report.getDocument(xmlConfigFile);
			config = doc.getDocumentElement();
			
			NodeList tests = config.getElementsByTagName("test");				
			Element test = (Element)tests.item(0);
			defDir  = test.getAttribute("def").equals("") ? defDir  : new File(rootPath + test.getAttribute("def")).getParent();
			defName = test.getAttribute("def").equals("") ? defName : new File(rootPath + test.getAttribute("def")).getName();
			moduleName = test.getAttribute("module-name").equals("") ? moduleName : test.getAttribute("module-name");
			compiledDef = test.getAttribute("compiled-file-name").equals("") ? compiledDef : test.getAttribute("compiled-file-name");
			programsExtension = test.getAttribute("program-extension").equals("") ? programsExtension : test.getAttribute("program-extension");
		}
		/************************************************/

		List<String> programs = searchInDir(programsExtension, rootPath,
				programsDir);
		
		
		// create example tag
		Element example = root.createElement(mainTagName);
		example.setAttribute("dir", defDir.substring(rootPath.length()));
		example.setAttribute("mainfile", defName);
		example.setAttribute("mainmodule", moduleName);
		example.setAttribute("compiledfile", compiledDef);
		
//		System.out.println("Programs dir: " + programsDir + " search: " + programsExtension);
		for (String program : programs) {
			// create test tag
			Element test = root.createElement("test");
			test.setAttribute("file", program);
			
			// search the input and the output pair
			String in = new File(program).getName() + ".in";
			String out = new File(program).getName() + ".out";
			String input = searchRecFile(rootPath + testsRelDir, in, rootPath);
			String output = searchRecFile(rootPath + testsRelDir, out, rootPath);
			
			Map<String, String> krunoptions = new HashMap<String, String>();
			krunoptions.put("--no-color", "");
			krunoptions.put("--output-mode", "none");
			boolean ignore = false;
			
			/******************* CHANGING DEFAULTS ACCORDING TO CONFIG FILE  ******************/
			if(config != null)
			{
				NodeList kopts = config.getElementsByTagName("krun-options");
				if(kopts.getLength() > 0)
				{
				Element krunopts = (Element)kopts.item(0);
				boolean set = false;
				
				NodeList pgms = krunopts.getElementsByTagName("program");
				for(int i = 0; i < pgms.getLength(); i++)
				{
					Element pgm = (Element) pgms.item(i);
					String name = pgm.getAttribute("name");
					String ignoreAttr = pgm.getAttribute("ignore");
					if (ignoreAttr.equals("yes"))
					{
						if (name.equals(new File(program).getName()))
							ignore = true;
					}

					if (name.equals(new File(program).getName()))
					{
						set = true;
						
						// reconsider input and output
						input = pgm.getAttribute("input").equals("") ? "" : pgm.getAttribute("input");
						output = pgm.getAttribute("output").equals("") ? "" : pgm.getAttribute("output");
						
						// consider krun options if any
						NodeList options = pgm.getElementsByTagName("option");
						if (options.getLength() > 0)
							krunoptions = new HashMap<String, String>();
						for(int j = 0; j < options.getLength(); j++)
							{
								Element opt = (Element)options.item(j);
								krunoptions.put(opt.getAttribute("name"), opt.getAttribute("value"));
							}
					}
				}
				if (!set)
				{
					NodeList generalOpts = krunopts.getElementsByTagName("general");
					if (generalOpts.getLength() > 0)
						krunoptions = new HashMap<String, String>();
					for(int i = 0; i < generalOpts.getLength(); i++)
					{
						Element genOpt = (Element)generalOpts.item(i);
						NodeList opts = genOpt.getElementsByTagName("option");
						for(int j = 0; j < opts.getLength(); j++)
						{
							Element opt = (Element)opts.item(j);
							krunoptions.put(opt.getAttribute("name"), opt.getAttribute("value"));
						}
					}
				}
				}
			}
			/*************************************/
			
			
			test.setAttribute("input", input);
			test.setAttribute("output", output);
			
			if (!krunoptions.isEmpty())
			{
				for(Entry<String, String> option : krunoptions.entrySet())
				{
					Element opt = doc.createElement("option");
					opt.setAttribute("name", option.getKey());
					opt.setAttribute("value", option.getValue());
					test.appendChild(opt);
				}
			}
			
			if (!ignore)
				example.appendChild(test);
		}

		return example;
	}

	private String searchRecFile(String directory, String file, String relativeTo) {
		File dir = new File(directory);
		if (dir.exists())
		{
			String[] dirFiles = dir.list();
			for(int i = 0; i < dirFiles.length; i++)
			{
				File temp = new File(directory + StaticK.fileSep + dirFiles[i]);
				if (temp.isFile() && file.equals(temp.getName()))
				{
					return (directory + StaticK.fileSep + file).replace(relativeTo, "");
				}
				if (temp.isDirectory() && !temp.isHidden())
				{
					String search = searchRecFile(temp.getAbsolutePath(), file, relativeTo);
					if (file.equals(search))
						return search;
				}
			}
		}
		
		return "";
	}

	private List<String> searchInDir(String fileNamePattern,
			String relativeToDir, String directory) {

		List<String> files = new LinkedList<String>();

		File dir = new File(directory);
		if (dir.exists() && dir.isDirectory() && !dir.isHidden()) {
			String[] dirFiles = dir.list();
			for (int i = 0; i < dirFiles.length; i++) {
				File temp = new File(directory + StaticK.fileSep + dirFiles[i]);
				if (temp.isFile()) {
					String fileName = temp.getName();
					if (fileName.endsWith(fileNamePattern))
					{
						files.add(temp.getAbsolutePath().replace(relativeToDir, ""));
					}
				}
				if (temp.isDirectory() && !temp.isHidden()) {
					files.addAll(searchInDir(fileNamePattern, relativeToDir,
							temp.getAbsolutePath()));
				}
			}
		}

		return files;
	}
	
	public void save() {
		StaticK.configuration = StaticK.kbasedir + StaticK.fileSep + "configuration.xml";
		String file = StaticK.configuration;
		try {
			FileWriter fstream = new FileWriter(file);
			BufferedWriter out = new BufferedWriter(fstream);
			out.write(Report.format(doc));
			out.close();
		} catch (IOException e) {
		    System.out.println("Jenkins: " + e.getLocalizedMessage());
			e.printStackTrace();
		}
	}
}
