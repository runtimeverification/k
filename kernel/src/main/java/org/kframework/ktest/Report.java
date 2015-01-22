// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.ktest;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class Report {

    private final String name;

    private final boolean failed;

    private final long timeDelta;

    private final String stdout;

    private final String stderr;

    private final String errorMsg;

    private Report(String name, boolean failed, long timeDelta, String stdout, String stderr,
                   String errorMsg) {
        this.name = name;
        this.failed = failed;
        this.timeDelta = timeDelta;
        this.stdout = stdout;
        this.stderr = stderr;
        this.errorMsg = errorMsg;
    }

    public static Report reportFailure(String name, long timeDelta, String stdout, String stderr,
                                String errorMsg) {
        return new Report(name, true, timeDelta, stdout, stderr, errorMsg);
    }

    public static Report reportSuccess(String name, long timeDelta, String stdout, String stderr) {
        return new Report(name, false, timeDelta, stdout, stderr, null);
    }

    /**
     * Generate `<testcase ...> ... </testcase>' element for a test.
     * @return testcase element
     */
    public Element genElement(Document doc) {
        Element testElem = doc.createElement("testcase");
        testElem.setAttribute("name", name);
        testElem.setAttribute("status", failed ? "failed" : "success");
        testElem.setAttribute("time", String.valueOf(timeDelta));

        Element sysout = doc.createElement("system-out");
        sysout.setTextContent(stdout);

        Element syserr = doc.createElement("system-err");
        syserr.setTextContent(stderr);

        testElem.appendChild(sysout);
        testElem.appendChild(syserr);

        if (failed) {
            Element error = doc.createElement("error");
            error.setAttribute("message", errorMsg);
            testElem.appendChild(error);
        }

        return testElem;
    }

    public boolean failed() {
        return failed;
    }
}

