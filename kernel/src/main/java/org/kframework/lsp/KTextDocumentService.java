package org.kframework.lsp;

import org.eclipse.lsp4j.*;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.services.TextDocumentService;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.CompletableFuture;

/**
 * TextDocumentService implementation for K.
 */
public class KTextDocumentService implements TextDocumentService {

    private KLanguageServer languageServer;
    private LSClientLogger clientLogger;

    public KTextDocumentService(KLanguageServer languageServer) {
        this.languageServer = languageServer;
        this.clientLogger = LSClientLogger.getInstance();
    }

    @Override
    public void didOpen(DidOpenTextDocumentParams didOpenTextDocumentParams) {
        this.clientLogger.logMessage("Operation '" + "text/didOpen" +
                "' {fileUri: '" + didOpenTextDocumentParams.getTextDocument().getUri() + "'} opened");
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
    }
}
