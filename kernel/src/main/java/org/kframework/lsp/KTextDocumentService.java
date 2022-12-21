package org.kframework.lsp;

import org.eclipse.lsp4j.*;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.services.TextDocumentService;
import org.kframework.attributes.Source;
import org.kframework.kil.DefinitionItem;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.StringUtil;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;

/**
 * TextDocumentService implementation for K.
 */
public class KTextDocumentService implements TextDocumentService {

    private KLanguageServer languageServer;
    private LSClientLogger clientLogger;

    private Map<String, List<DefinitionItem>> elems = new HashMap<>();

    public KTextDocumentService(KLanguageServer languageServer) {
        this.languageServer = languageServer;
        this.clientLogger = LSClientLogger.getInstance();
    }

    @Override
    public void didOpen(DidOpenTextDocumentParams didOpenTextDocumentParams) {
        this.clientLogger.logMessage("Operation '" + "text/didOpen" +
                "' {fileUri: '" + didOpenTextDocumentParams.getTextDocument().getUri() + "'} opened");
        outerParse(didOpenTextDocumentParams.getTextDocument().getUri());
    }

    @Override
    public void didChange(DidChangeTextDocumentParams didChangeTextDocumentParams) {
        this.clientLogger.logMessage("Operation '" + "text/didChange" +
                "' {fileUri: '" + didChangeTextDocumentParams.getTextDocument().getUri() + "'} Changed");
    }

    @Override
    public void didClose(DidCloseTextDocumentParams didCloseTextDocumentParams) {
        this.clientLogger.logMessage("Operation '" + "text/didClose" +
                "' {fileUri: '" + didCloseTextDocumentParams.getTextDocument().getUri() + "'} Closed");
    }

    @Override
    public void didSave(DidSaveTextDocumentParams didSaveTextDocumentParams) {
        this.clientLogger.logMessage("Operation '" + "text/didSave" +
                "' {fileUri: '" + didSaveTextDocumentParams.getTextDocument().getUri() + "'} Saved");
        outerParse(didSaveTextDocumentParams.getTextDocument().getUri());
    }

    @Override
    public CompletableFuture<Either<List<CompletionItem>, CompletionList>> completion(CompletionParams position) {
        return CompletableFuture.supplyAsync(() -> {
            this.clientLogger.logMessage("Operation '" + "text/completion");
            CompletionItem completionItem = new CompletionItem();
            completionItem.setLabel("Test completion item");
            completionItem.setInsertText("Test");
            completionItem.setDetail("Snippet");
            completionItem.setKind(CompletionItemKind.Snippet);
            return Either.forLeft(Arrays.asList(completionItem));
        });
        /*return CompletableFuture.supplyAsync(() -> {
            this.clientLogger.logMessage("Operation '" + "text/completion");
            CompletionItem completionItem = new CompletionItem();
            completionItem.setLabel("Test completion item");
            completionItem.setInsertText("Test");
            completionItem.setDetail("Snippet");
            completionItem.setKind(CompletionItemKind.Snippet);
            return Either.forLeft(Arrays.asList(completionItem));
        });*/
    }

    private void outerParse(String uri) {
        List<DefinitionItem> di = null;
        try {
            di = Outer.parse(Source.apply(uri),FileUtil.load(new File(new URI(uri))),null);
        } catch (URISyntaxException e) {
            throw new RuntimeException(e);
        }
        elems.put(uri, di);
        this.clientLogger.logMessage("Operation '" + "outerParse" + " #di: " + di.size());
    }
}
