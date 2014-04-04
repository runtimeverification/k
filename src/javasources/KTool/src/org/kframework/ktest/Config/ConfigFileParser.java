package org.kframework.ktest.Config;

import org.apache.commons.io.FilenameUtils;
import org.kframework.ktest.Annotated;
import org.kframework.ktest.CmdArgs.CmdArg;
import org.kframework.ktest.KTest;
import org.kframework.ktest.KTestStep;
import org.kframework.ktest.PgmArg;
import org.kframework.ktest.Test.TestCase;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.*;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.XMLReader;
import org.xml.sax.helpers.XMLReaderFactory;

import javax.xml.XMLConstants;
import javax.xml.parsers.*;
import javax.xml.transform.Source;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMResult;
import javax.xml.transform.sax.SAXSource;
import javax.xml.transform.stream.StreamSource;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Validator;
import java.io.File;
import java.io.IOException;
import java.util.*;

public class ConfigFileParser {

    private final Document doc;
    private final CmdArg cmdArgs;

    public ConfigFileParser(File configFile, CmdArg cmdArgs) throws IOException, SAXException,
            ParserConfigurationException, TransformerException {
        this.cmdArgs = cmdArgs;

        // validate xml file structure
        Source schemaFile = new StreamSource(new File(getSchema()));
        Source xmlFile = new StreamSource(configFile);
        SchemaFactory schemaFactory = SchemaFactory.newInstance(XMLConstants
                .W3C_XML_SCHEMA_NS_URI);
        Schema schema = schemaFactory.newSchema(schemaFile);
        Validator validator = schema.newValidator();
        validator.validate(xmlFile);

        // parse xml file
        DocumentBuilderFactory documentBuilderFactory = DocumentBuilderFactory.newInstance();
        TransformerFactory transformerFactory = TransformerFactory.newInstance();
        Transformer nullTransformer = transformerFactory.newTransformer();

        // annotate XML file with location information of elements and resolve environment
        // variables in attributes/elements
        // (also see comments in ConfigPreProcessor)

        // Create an empty document to be populated within a DOMResult.
        DocumentBuilder docBuilder = documentBuilderFactory.newDocumentBuilder();
        doc = docBuilder.newDocument();
        DOMResult domResult = new DOMResult(doc);

        // Create SAX parser/XMLReader that will parse XML.
        XMLReader xmlReader = XMLReaderFactory.createXMLReader();

        // Create our filter to wrap the SAX parser, that captures the locations of elements
        // and annotates their nodes as they are inserted into the DOM.
        ConfigPreProcessor locationAnnotator = new ConfigPreProcessor(xmlReader, doc);

        // Create the SAXSource to use the annotator.
        String systemId = configFile.getAbsolutePath();
        InputSource inputSource = new InputSource(systemId);
        SAXSource saxSource = new SAXSource(locationAnnotator, inputSource);

        // Finally read the XML into the DOM.
        nullTransformer.transform(saxSource, domResult);
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
     * Parse `test' and `include' nodes in NodeList.
     *
     * @param tests NodeList that contains `test' and `include' elements
     * @return list of `TestCase's
     * @throws InvalidConfigError when config file contains invalid information
     */
    private List<TestCase> parseTestCases(NodeList tests) throws InvalidConfigError {
        List<TestCase> testCases = new LinkedList<>();

        for (int testNodeIdx = 0; testNodeIdx < tests.getLength(); testNodeIdx++) {
            if (tests.item(testNodeIdx).getNodeType() != Node.ELEMENT_NODE)
                continue;

            Element node = (Element) tests.item(testNodeIdx);
            switch (node.getNodeName()) {
                case "test": if (isValidTestCase(node)) testCases.add(parseTestCase(node)); break;
                case "include": testCases.addAll(parseInclude(node)); break;
                default: assert false; // this case should not happen, XML files are validated
                                       // using XSD and this should be ensured by XSD file
            }
        }

        return testCases;
    }

    /**
     * Check if `test' node is semantically valid.
     */
    private boolean isValidTestCase(Element testNode) {
        // posixOnly attribute is valid only on Posix-compliant OS
        return testNode.getAttributes().getNamedItem("posixOnly") == null
                || GlobalSettings.isPosix();
    }

    /**
     * Parse a `include' node.
     * @param includeNode `include' element
     * @return List of test cases.
     * @throws InvalidConfigError
     */
    private List<TestCase> parseInclude(Element includeNode) throws InvalidConfigError {
        NamedNodeMap includeAttrs = includeNode.getAttributes();
        LocationData location =
                (LocationData) includeNode.getUserData(LocationData.LOCATION_DATA_KEY);

        String fileValue = includeAttrs.getNamedItem("file").getNodeValue();
        String file = concat(FilenameUtils.getFullPath(cmdArgs.getTargetFile()),fileValue);

        if (!new File(file).isFile())
            throw new InvalidConfigError(
                    "file attribute " + file + " in `include' is not a valid file", location);

        String directory = concat(cmdArgs.getDirectory(),
                getAttributeWDefault(includeAttrs, "directory", ""));

        String programs = concat(cmdArgs.getPrograms(),
                getAttributeWDefault(includeAttrs, "programs", FilenameUtils.getFullPath(file)));

        String results = concat(cmdArgs.getResults(),
                getAttributeWDefault(includeAttrs, "results", FilenameUtils.getFullPath(file)));

        CmdArg cmdArgs1 = new CmdArg(cmdArgs)
                .setDirectory(directory)
                .setPrograms(programs)
                .setResults(results)
                .setTargetFile(file);

        ConfigFileParser configFileParser;
        try {
            configFileParser = new ConfigFileParser(new File(file), cmdArgs1);
        } catch (Exception e) {
            // I'm not happy with that part ...
            throw new InvalidConfigError("error occured while parsing included file " + file +
                    ":\n" + e.getMessage(), location);
        }

        List<TestCase> ret = configFileParser.parse();

        // handle overridden attributes
        NodeList childNodes = includeNode.getChildNodes();
        if (includeAttrs.getNamedItem("exclude") != null)
            overrideExcludes(ret, splitNodeValue(includeAttrs.getNamedItem("exclude")));
        // note that we need to run `hasElement' because parse* methods will return containers
        // with 0 element when relevant elements are not found.
        if (hasElement(childNodes, "kompile-option"))
            overrideKompileOptions(ret, parseKompileOpts(childNodes));
        if (hasElement(childNodes, "all-programs"))
            overrideKrunOpts(ret, parseAllPgmsKrunOpts(childNodes));
        if (hasElement(childNodes, "program"))
            overridePgmSpecificKRunOpts(ret, parsePgmSpecificKRunOpts(childNodes));

        // handle extended attributes
        if (includeAttrs.getNamedItem("more-programs") != null)
            for (String p : splitNodeValue(includeAttrs.getNamedItem("more-programs")))
                extendPrograms(ret, annotate(normalize(p, cmdArgs.getPrograms()), location));
        if (includeAttrs.getNamedItem("more-results") != null)
            for (String r : splitNodeValue(includeAttrs.getNamedItem("more-results")))
                extendResults(ret, annotate(normalize(r, cmdArgs.getPrograms()), location));

        for (TestCase tc : ret)
            tc.validate();
        return ret;
    }

    private void overrideExcludes(List<TestCase> tests, String[] excludes) {
        for (TestCase tc : tests)
            tc.setExcludes(excludes);
    }

    private void overrideKompileOptions(List<TestCase> tests, List<PgmArg> kompileOpts) {
        for (TestCase tc : tests)
            tc.setKompileOpts(kompileOpts);
    }

    private void overrideKrunOpts(List<TestCase> tests, List<PgmArg> krunOpts) {
        for (TestCase tc : tests)
            tc.setKrunOpts(krunOpts);
    }

    private void overridePgmSpecificKRunOpts(
            List<TestCase> tests, Map<String, List<PgmArg>> pgmSpecificKrunOpts) {
        for (TestCase tc : tests)
            tc.setPgmSpecificKRunOpts(pgmSpecificKrunOpts);
    }

    private void extendPrograms(List<TestCase> tests, Annotated<String, LocationData> p) {
        for (TestCase tc : tests)
            tc.addProgram(p);
    }

    private void extendResults(List<TestCase> tests, Annotated<String, LocationData> r) {
        for (TestCase tc : tests)
            tc.addResult(r);
    }

    private boolean hasElement(NodeList nodes, String elemName) {
        for (int i = 0; i < nodes.getLength(); i++)
            if (nodes.item(i).getNodeName().equals(elemName))
                return true;
        return false;
    }

    /**
     * Parse a `test' node.
     * @param testNode `test' element.
     * @return a test case
     * @throws InvalidConfigError
     */
    private TestCase parseTestCase(Element testNode) throws InvalidConfigError {
        NamedNodeMap testAttrs = testNode.getAttributes();
        // I couldn't find a way to annotate attributes with location information using SAX api
        // (maybe it's not possible?) so I'm annotation attributes with location data of
        // parent node (element)
        LocationData location =
                (LocationData) testNode.getUserData(LocationData.LOCATION_DATA_KEY);

        Node definitionNode = testAttrs.getNamedItem("definition");

        Annotated<String, LocationData> definition =
                annotate(normalize(addDefinitionExt(definitionNode.getNodeValue()),
                        cmdArgs.getDirectory()), location);
        List<Annotated<String, LocationData>> programs =
                annotateLst(normalize(splitNodeValue(testAttrs.getNamedItem("programs")),
                        cmdArgs.getPrograms()), location);
        List<Annotated<String, LocationData>> results =
                annotateLst(normalize(splitNodeValue(testAttrs.getNamedItem("results")),
                        cmdArgs.getResults()), location);

        String[] extensions = splitNodeValue(testAttrs.getNamedItem("extension"));
        String[] excludes = splitNodeValue(testAttrs.getNamedItem("exclude"));
        Set<KTestStep> skips = parseSkips(testAttrs.getNamedItem("skip"), location);
        String posixOnly = parsePosixOnly(testAttrs.getNamedItem("posixOnly"));

        // handle children of `test' node
        NodeList childNodes = testNode.getChildNodes();

        List<PgmArg> kompileOpts = parseKompileOpts(childNodes);
        List<PgmArg> krunOpts = parseAllPgmsKrunOpts(childNodes);
        Map<String, List<PgmArg>> pgmSpecificKRunOpts = parsePgmSpecificKRunOpts(childNodes);

        TestCase ret = new TestCase(definition, programs, extensions, excludes, results,
                kompileOpts, krunOpts, pgmSpecificKRunOpts, skips);
        if (posixOnly != null) {
            ret.setPosixInitScript(posixOnly);
        }
        ret.validate();
        return ret;
    }

    private String addDefinitionExt(String nodeValue) {
        if (FilenameUtils.getExtension(nodeValue).equals("k"))
            return nodeValue;
        return nodeValue + ".k";
    }

    private Set<KTestStep> parseSkips(Node node, LocationData location) throws InvalidConfigError {
        Set<KTestStep> skips = new HashSet<>();
        if (node == null)
            return skips;
        for (String s : node.getNodeValue().split("\\s+")) {
            switch (s.trim()) {
                case "kompile": skips.add(KTestStep.KOMPILE); break;
                case "pdf": skips.add(KTestStep.PDF); break;
                case "krun": skips.add(KTestStep.KRUN); break;
                case "": break;
                default: throw new InvalidConfigError(
                        "skip attribute option should be [kompile|pdf|krun]+", location);
            }
        }
        return skips;
    }

    private String parsePosixOnly(Node node) {
        if (node == null) {
            return null;
        }
        return normalize(node.getNodeValue(), cmdArgs.getDirectory());
    }

    private Annotated<String, LocationData> annotate(String str, LocationData location) {
        return new Annotated<>(str, location);
    }

    private List<Annotated<String, LocationData>> annotateLst(String[] strs, LocationData location) {
        List<Annotated<String, LocationData>> ret = new LinkedList<>();
        for (String str : strs)
            ret.add(annotate(str, location));
        return ret;
    }

    private String normalize(String path, String root) {
        return concat(root, path);
    }

    private String[] normalize(String[] paths, String root) {
        for (int i = 0; i < paths.length; i++)
            paths[i] = concat(root, paths[i]);
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

                String name = elem.getAttribute("name");
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

                ret.add(new PgmArg(e.getAttribute("name"),
                    e.getAttribute("key"),
                    e.getAttribute("value")));
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
                ret.put(elem.getAttribute("name"), parseKrunOpts(elem.getChildNodes()));
            }
        }
        return ret;
    }

    private String[] splitNodeValue(Node node) {
        if (node == null)
            return new String[0];
        return node.getNodeValue().split("\\s+");
    }

    private String getAttributeWDefault(NamedNodeMap attrs, String name, String def) {
        Node n = attrs.getNamedItem(name);
        if (n == null)
            return def;
        return n.getNodeValue();
    }

    private String getSchema() {
        return concat(getKHome(), concat("lib", "ktest.xsd"));
    }

    private String getKHome() {
        return new File(KTest.class.getProtectionDomain().getCodeSource()
                .getLocation().getPath()).getParentFile().getParentFile()
                .getParentFile().getPath();
    }

    private String concat(String s1, String s2) {
        // HACK: FilenameUtils.concat return "" when two "." is concatenated,
        // we don't want this because new File("").isDirectory() return false, which causes
        // test validation to fail (it checks directory/results/programs to be valid folders)
        String ret = FilenameUtils.concat(s1, s2);
        assert ret != null : "concat(" + s1 + ", " + s2 + ") returned null";
        if (ret.equals("")) return ".";
        return ret;
    }
}
