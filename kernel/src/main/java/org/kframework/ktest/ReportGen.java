// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.ktest;

import org.apache.commons.io.FilenameUtils;
import org.apache.commons.io.IOUtils;
import org.apache.commons.lang3.StringUtils;
import org.kframework.utils.errorsystem.KEMException;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.TransformerFactoryConfigurationError;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import java.io.*;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class ReportGen {

    private final Map<String, List<Report>> reports;
    private int count = 0;
    private int failures = 0;

    private final File junitFolder;

    public ReportGen(File junitFolder) {
        reports = new HashMap<>();
        this.junitFolder = junitFolder;
    }

    public void addFailure(String definition, String name, long timeDelta, String stdout,
                           String stderr, String errorMsg) {
        getReportLst(definition).add(
                Report.reportFailure(name, timeDelta, stdout, stderr, errorMsg));
        failures++;
        count++;
    }

    public void addSuccess(String definition, String name, long timeDelta, String stdout,
                           String stderr) {
        getReportLst(definition).add(
                Report.reportSuccess(name, timeDelta, stdout, stderr));
        count++;
    }

    public void save() throws ParserConfigurationException, TransformerException, IOException {
        if (!junitFolder.isDirectory()) {
            if (!junitFolder.mkdirs()) {
                throw KEMException.criticalError("Could not create directory " + junitFolder);
            }
        }

        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        DocumentBuilder db = dbf.newDocumentBuilder();
        Document doc = db.newDocument();

        for (Map.Entry<String, List<Report>> e : reports.entrySet()) {
            Element elem = genElem(doc, e.getKey(), e.getValue());

            File targetFile = new File(junitFolder.getAbsolutePath(),
                    StringUtils.replace(FilenameUtils.getPath(e.getKey()), File.separator, "-")
                            + FilenameUtils.getBaseName(e.getKey()) + ".xml");
            writeXmlFile(targetFile, elem);
        }

        Element elem = genSummary(doc, reports);
        File targetFile = new File(junitFolder.getAbsolutePath(),
                "summary.xml");
        writeXmlFile(targetFile, elem);

    }

    private void writeXmlFile(File targetFile, Element elem)
            throws TransformerFactoryConfigurationError, TransformerException, IOException {
        Transformer transformer = TransformerFactory.newInstance().newTransformer();
        transformer.setOutputProperty("indent", "yes");
        transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "2");

        // initialize StreamResult with File object to save to file
        StreamResult result = new StreamResult(new StringWriter());
        DOMSource source = new DOMSource(elem);
        transformer.transform(source, result);

        IOUtils.write(result.getWriter().toString(), new FileOutputStream(targetFile));
    }

    /**
     * Generate `<testsuite ...> ... </testsuite>' element from list of reports.
     * @param name name of testsuite
     * @param reports reports to generate testsuite element
     * @return testsuite element
     */
    private Element genElem(Document doc, String name, List<Report> reports) {
        Element testSuiteElem = doc.createElement("testsuite");
        testSuiteElem.setAttribute("name", name);

        for (Report r : reports)
            testSuiteElem.appendChild(r.genElement(doc));

        return testSuiteElem;
    }

    private Element genSummary(Document doc, Map<String, List<Report>> reports) {
        Element summary = doc.createElement("failsafe-summary");
        String result;
        if (count == 0) {
            result = "254"; //NO_TESTS
        } else if (failures > 0) {
            result = "255"; //FAILURE
        } else {
            result = "0"; //SUCCESS
        }
        summary.setAttribute("result", result);
        summary.setAttribute("timeout", "false");
        Element completed = doc.createElement("completed");
        completed.setTextContent(Integer.toString(count));
        Element errors = doc.createElement("errors");
        errors.setTextContent("0");
        Element failures = doc.createElement("failures");
        failures.setTextContent(Integer.toString(this.failures));
        Element skipped = doc.createElement("skipped");
        skipped.setTextContent("0");
        Element failureMessage = doc.createElement("failureMessage");
        summary.appendChild(completed);
        summary.appendChild(errors);
        summary.appendChild(failures);
        summary.appendChild(skipped);
        summary.appendChild(failureMessage);

        return summary;
    }

    private List<Report> getReportLst(String definition) {
        List<Report> rs = reports.get(definition);
        if (rs == null) {
            rs = new LinkedList<>();
            reports.put(definition, rs);
        }
        return rs;
    }
}
