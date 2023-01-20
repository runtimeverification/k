package org.kframework.lsp;


import org.eclipse.lsp4j.*;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.kil.DefinitionItem;
import org.kframework.parser.outer.ExtractFencedKCodeFromMarkdown;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class KTextDocument {

    public String content = "";
    public String uri = "";
    public int[] lines;
    public int[] columns;
    public boolean linesOutdated = true;
    public boolean disOutdated = true;
    public List<Diagnostic> problems = new ArrayList<>();
    // definition items provided by outer parsing
    public List<DefinitionItem> dis = new ArrayList<>();
    public static final ExtractFencedKCodeFromMarkdown mdExtractor = new ExtractFencedKCodeFromMarkdown(null, "k");

    public void updateText(String input) {
        disOutdated = true;
        linesOutdated = true;
        content = input;
    }

    Pattern p = Pattern.compile("(module|endmodule|syntax|context|configuration|rule|claim|require[s]?|import[s]?)");

    // get the last keyword at Position in order to provide contextual completion
    public String getContextAt(Position pos) {
        if (linesOutdated) {
            linesOutdated = false;
            lines = new int[content.length() + 1];
            columns = new int[content.length() + 1];
            int l = 1;
            int c = 1;
            for (int offset = 0; offset < content.length(); offset++) {
                lines[offset] = l;
                columns[offset] = c;
                if (content.codePointAt(offset) == '\n') {
                    l++;
                    c =  0;
                }
                c++;
            }
        }
        pos = new Position(pos.getLine() + 1, pos.getCharacter() + 1);
        Matcher m = p.matcher(content);
        String context = "requires";
        while (m.find()) {
            context = m.group();
            System.out.println(context + " idx: " + m.start() + "-" + m.end() + " l: " + lines[m.start()] + " c: " + columns[m.start()]);
            if (lines[m.end()] > pos.getLine() || lines[m.end()] == pos.getLine() && columns[m.end()] < pos.getCharacter())
                break;
        }
        return context;
    }

    public void outerParse() {
        if (disOutdated) {
            disOutdated = false;
            problems.clear();
            try {
                String contents = this.content;
                if (uri.endsWith(".md"))
                    contents = mdExtractor.extract(contents, Source.apply(uri));
                dis = Outer.parse(Source.apply(uri), contents, null);
            } catch (KEMException e) {
                Location loc = e.exception.getLocation();
                if (loc == null) loc = new Location(1, 1, 1, 2);
                Range range = KTextDocumentService.loc2range(loc);
                Diagnostic d = new Diagnostic(range, e.exception.getMessage(), DiagnosticSeverity.Error, "Outer Parser");
                problems.add(d);
            }
        }
    }
}
