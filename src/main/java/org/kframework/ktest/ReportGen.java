// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.ktest;

import org.apache.commons.io.FilenameUtils;
import org.apache.commons.io.IOUtils;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.*;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class ReportGen {

    private final Map<String, List<Report>> reports;

    public ReportGen() {
        reports = new HashMap<>();
    }

    public void addFailure(String definition, String name, long timeDelta, String stdout,
                           String stderr, String errorMsg) {
        getReportLst(definition).add(
                Report.reportFailure(name, timeDelta, stdout, stderr, errorMsg));
    }

    public void addSuccess(String definition, String name, long timeDelta, String stdout,
                           String stderr) {
        getReportLst(definition).add(
                Report.reportSuccess(name, timeDelta, stdout, stderr));
    }

    public void save() throws ParserConfigurationException, TransformerException, IOException {
        File junitFolder = new File("junit-reports");
        if (!junitFolder.isDirectory())
            junitFolder.mkdirs();

        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        DocumentBuilder db = dbf.newDocumentBuilder();
        Document doc = db.newDocument();

        for (Map.Entry<String, List<Report>> e : reports.entrySet()) {
            Element elem = genElem(doc, e.getKey(), e.getValue());

            Transformer transformer = TransformerFactory.newInstance().newTransformer();
            transformer.setOutputProperty("indent", "yes");
            transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "2");

            // initialize StreamResult with File object to save to file
            StreamResult result = new StreamResult(new StringWriter());
            DOMSource source = new DOMSource(elem);
            transformer.transform(source, result);

            File targetFile = new File(junitFolder.getAbsolutePath(),
                    FilenameUtils.getPath(e.getKey()).replaceAll(File.separator, "-")
                            + FilenameUtils.getBaseName(e.getKey()) + ".xml");
            IOUtils.write(result.getWriter().toString(), new FileOutputStream(targetFile));
        }
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

    private List<Report> getReportLst(String definition) {
        List<Report> rs = reports.get(definition);
        if (rs == null) {
            rs = new LinkedList<>();
            reports.put(definition, rs);
        }
        return rs;
    }
}
