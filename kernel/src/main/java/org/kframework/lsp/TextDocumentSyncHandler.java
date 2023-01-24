package org.kframework.lsp;


import org.eclipse.lsp4j.DidChangeTextDocumentParams;
import org.eclipse.lsp4j.DidCloseTextDocumentParams;
import org.eclipse.lsp4j.DidOpenTextDocumentParams;
import org.eclipse.lsp4j.DidSaveTextDocumentParams;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Require;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;

public class TextDocumentSyncHandler {

    public Map<String, KTextDocument> files = new HashMap<>();
    private final LSClientLogger clientLogger;

    public TextDocumentSyncHandler(LSClientLogger clientLogger) {
        this.clientLogger = clientLogger;
    }

    public void add(String uri) {
        try {
            KTextDocument doc = new KTextDocument();
            files.put(uri, doc);
            doc.uri = uri;
            doc.updateText(FileUtil.load(new File(new URI(uri))));
            doc.outerParse();
        } catch (URISyntaxException e) {
            clientLogger.logMessage(TextDocumentSyncHandler.class + ".addUri failed: " + uri);
        }
    }

    public void didOpen(DidOpenTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
        KTextDocument doc;
        if (files.containsKey(uri))
            doc = files.get(uri);
        else {
            doc = new KTextDocument();
            doc.uri = uri;
            files.put(uri, doc);
        }
        doc.updateText(params.getTextDocument().getText());
    }

    public void didChange(DidChangeTextDocumentParams params) {
        files.get(params.getTextDocument().getUri()).updateText(params.getContentChanges().get(0).getText());
    }

    public void didSave(DidSaveTextDocumentParams params) {
        KTextDocument doc = files.get(params.getTextDocument().getUri());
        doc.outerParse();
    }

    public void didClose(DidCloseTextDocumentParams params) {
        files.remove(params.getTextDocument().getUri());
    }

    // recurse through all the required files and return the list of DefinitionItems
    public List<DefinitionItem> slurp(String uri) {
        Set<String> visited = new HashSet<>();
        visited.add(KTextDocumentService.domains.toString());
        visited.add(KTextDocumentService.kast.toString());
        slurp2(uri, visited);
        List<DefinitionItem> dis = files.entrySet().stream()
                .filter(e -> visited.contains(e.getKey()))
                .flatMap(e -> e.getValue().dis.stream())
                .collect(Collectors.toList());
        return dis;
    }

    private void slurp2(String uri, Set<String> visited) {
        if (!files.containsKey(uri)) {
            try {
                if (new File(new URI(uri)).exists())
                    add(uri);
            } catch (URISyntaxException e) {
                clientLogger.logMessage(TextDocumentSyncHandler.class + ".slurp failed1: " + uri + "\n" + e.getMessage());
            }
        }
        KTextDocument current = files.get(uri);
        if (current.parsingOutdated)
            current.outerParse();
        if (!visited.contains(uri) && files.containsKey(uri)) {
            visited.add(uri);
            files.get(uri).dis.forEach(r -> {
                if (r instanceof Require) {
                    try {
                        Require req = (Require) r;
                        URI targetURI = Path.of(new File(new URI(uri)).getParent(), req.getValue()).toRealPath(LinkOption.NOFOLLOW_LINKS).toUri();
                        slurp2(targetURI.toString(), visited);
                    } catch (IOException | URISyntaxException e) {
                        clientLogger.logMessage(TextDocumentSyncHandler.class + ".slurp failed2: " + uri + "\n" + e);
                    }
                }
            });
        }
    }
}
