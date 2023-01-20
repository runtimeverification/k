package org.kframework.lsp;


import org.eclipse.lsp4j.DidChangeTextDocumentParams;
import org.eclipse.lsp4j.DidCloseTextDocumentParams;
import org.eclipse.lsp4j.DidOpenTextDocumentParams;
import org.eclipse.lsp4j.DidSaveTextDocumentParams;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.HashMap;
import java.util.Map;

public class TextDocumentSyncHandler {

    public Map<String, KTextDocument> files = new HashMap<>();

    public void add(String uri) {
        KTextDocument doc = new KTextDocument();
        files.put(uri, doc);
        doc.uri = uri;
        try {
            doc.updateText(FileUtil.load(new File(new URI(uri))));
            doc.outerParse();
        } catch (URISyntaxException e) {
            throw new RuntimeException();
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
}
