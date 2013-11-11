package org.kframework.ktest2.Config;

import org.apache.commons.io.FilenameUtils;
import org.kframework.ktest2.CmdArgs.CmdArg;
import org.kframework.ktest2.KTest;
import org.kframework.ktest2.PgmArg;
import org.kframework.ktest2.Test.TestCase;
import org.w3c.dom.*;
import org.xml.sax.SAXException;

import javax.xml.XMLConstants;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Source;
import javax.xml.transform.stream.StreamSource;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Validator;
import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class ConfigFileParser {

    private final Document doc;
    private final CmdArg cmdArgs;

    public ConfigFileParser(File configFile, CmdArg cmdArgs) throws IOException, SAXException,
            ParserConfigurationException {
        // validate xml file structure
        Source schemaFile = new StreamSource(new File(getSchema()));
        Source xmlFile = new StreamSource(configFile);
        SchemaFactory schemaFactory = SchemaFactory.newInstance(XMLConstants
                .W3C_XML_SCHEMA_NS_URI);
        Schema schema = schemaFactory.newSchema(schemaFile);
        Validator validator = schema.newValidator();
        validator.validate(xmlFile);

        // parse xml file
        this.cmdArgs = cmdArgs;
        DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
        DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
        doc = dBuilder.parse(configFile);
    }

    /**
     * Parse config file.
     * @return List of test cases, all file path fields will be normalized using command line
     * arguments (directory, programs and results file paths)
     * @throws InvalidConfigError when config file contains invalid information
     */
    public List<TestCase> parse() throws InvalidConfigError {
        NodeList testsNode = doc.getElementsByTagName("tests");
        NodeList tests = testsNode.item(0).getChildNodes();
        return parseTestCases(tests);
    }

    /**
     * Parse <test> ... </test> nodes in NodeList.
     *
     * @param tests NodeList that contains `test' elements
     * @return list of `TestCase's
     * @throws InvalidConfigError when config file contains invalid information
     */
    private List<TestCase> parseTestCases(NodeList tests) throws InvalidConfigError {
        List<TestCase> testCases = new LinkedList<>();

        for (int testNodeIdx = 0; testNodeIdx < tests.getLength(); testNodeIdx++) {
            if (tests.item(testNodeIdx).getNodeType() != Node.ELEMENT_NODE)
                continue;

            Element testNode = (Element) tests.item(testNodeIdx);
            NamedNodeMap testAttrs = testNode.getAttributes();

            Node definitionNode = testAttrs.getNamedItem("definition");

            String definition = normalize(definitionNode.getNodeValue(), cmdArgs.directory);
            String[] programs = normalize(splitNodeValue(testAttrs.getNamedItem("programs")),
                    cmdArgs.programs);
            String[] results = normalize(splitNodeValue(testAttrs.getNamedItem("results")),
                    cmdArgs.results);

            String[] extensions = splitNodeValue(testAttrs.getNamedItem("extension"));
            String[] excludes = splitNodeValue(testAttrs.getNamedItem("exclude"));

            // handle children of `test' node
            NodeList childNodes = testNode.getChildNodes();

            List<PgmArg> kompileOpts = parseKompileOpts(childNodes);
            List<PgmArg> krunOpts = parseAllPgmsKrunOpts(childNodes);
            Map<String, List<PgmArg>> pgmSpecificKRunOpts = parsePgmSpecificKRunOpts(childNodes);

            testCases.add(new TestCase(definition, programs, extensions, excludes, results,
                    kompileOpts, krunOpts, pgmSpecificKRunOpts));
        }

        return testCases;
    }

    private String normalize(String path, String root) {
        return FilenameUtils.concat(root, path);
    }

    private String[] normalize(String[] paths, String root) {
        for (int i = 0; i < paths.length; i++)
            paths[i] = normalize(paths[i], root);
        return paths;
    }

    /**
     * Parse <kompile-option> ... </kompile-option> elements in a NodeList.
     *
     * @param nodes NodeList to search `kompile-option' elements
     * @return List of kompile arguments
     */
    private List<PgmArg> parseKompileOpts(NodeList nodes) {
        List<PgmArg> ret = new LinkedList<>();
        for (int childNodeIdx = 0; childNodeIdx < nodes.getLength(); childNodeIdx++) {
            Node childNode = nodes.item(childNodeIdx);
            if (childNode.getNodeType() == Node.ELEMENT_NODE
                    && childNode.getNodeName().equals("kompile-option")) {
                Element elem = (Element) childNode;

                // TODO: there is a problem with our current config files,
                // correct parameter for backend is `--backend', not `-backend' or `backend'. but
                // in config file it's specified as `-backed'. for now I'm handling it in ad-hoc
                // way. we should fix this in config files. (this applies to other parameters too)
                // (osa1)
                String name = elem.getAttribute("name");
                while (name.startsWith("-"))
                    name = name.substring(1);
                ret.add(new PgmArg(name, elem.getAttribute("value")));
            }
        }
        return ret;
    }

    /**
     * Parse <all-programs> ... </all-programs> elements in a NodeList.
     *
     * @param nodes NodeList to search `all-programs' elements
     * @return List of krun arguments
     */
    private List<PgmArg> parseAllPgmsKrunOpts(NodeList nodes) {
        List<PgmArg> ret = new LinkedList<>();
        for (int childNodeIdx = 0; childNodeIdx < nodes.getLength(); childNodeIdx++) {
            Node childNode = nodes.item(childNodeIdx);
            if (childNode.getNodeType() == Node.ELEMENT_NODE
                    && childNode.getNodeName().equals("all-programs"))
                ret.addAll(parseKrunOpts(childNode.getChildNodes()));
        }
        return ret;
    }

    /**
     * Parse <krun-option> ... </krun-option> elements in a NodeList.
     *
     * @param nodes NodeList to search `krun-option' elements
     * @return List of krun arguments
     */
    private List<PgmArg> parseKrunOpts(NodeList nodes) {
        List<PgmArg> ret = new LinkedList<>();
        for (int i = 0; i < nodes.getLength(); i++) {
            Node n = nodes.item(i);
            if (n.getNodeType() == Node.ELEMENT_NODE
                    && n.getNodeName().equals("krun-option")) {
                Element e = (Element) n;

                // TODO: see comments in parseKompileOpts
                String name = e.getAttribute("name");
                while (name.startsWith("-"))
                    name = name.substring(1);
                ret.add(new PgmArg(name, e.getAttribute("value")));
            }
        }
        return ret;
    }

    /**
     * Parse <program name=...> ... </program> elements in a NodeList.
     *
     * @param nodes NodeList to search `program' elements
     * @return Map from program names to list of program arguments
     */
    private Map<String, List<PgmArg>> parsePgmSpecificKRunOpts(NodeList nodes) {
        Map<String, List<PgmArg>> ret = new HashMap<>();
        for (int childNodeIdx = 0; childNodeIdx < nodes.getLength(); childNodeIdx++) {
            Node childNode = nodes.item(childNodeIdx);
            if (childNode.getNodeType() == Node.ELEMENT_NODE
                    && childNode.getNodeName().equals("program")) {
                Element elem = (Element) childNode;
                ret.put(FilenameUtils.concat(cmdArgs.programs, elem.getAttribute("name")),
                        parseKrunOpts(elem.getChildNodes()
                ));
            }
        }
        return ret;
    }

    private String[] splitNodeValue(Node node) {
        if (node == null)
            return new String[0];
        return node.getNodeValue().split("\\s+");
    }

    private String getSchema() {
        return FilenameUtils.concat(getKHome(), FilenameUtils.concat("lib", "ktest.xsd"));
    }

    private String getKHome() {
        return new File(KTest.class.getProtectionDomain().getCodeSource()
                .getLocation().getPath()).getParentFile().getParentFile()
                .getParentFile().getPath();
    }
}
