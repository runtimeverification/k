// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.lsp;

import org.eclipse.lsp4j.*;
import org.eclipse.lsp4j.services.WorkspaceService;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.concurrent.CompletableFuture;

/**
 * WorkspaceService implementation for K.
 */
public class KWorkspaceService implements WorkspaceService {

    private KLanguageServer languageServer;
    LSClientLogger clientLogger;

    public KWorkspaceService(KLanguageServer languageServer) {
        this.languageServer = languageServer;
        this.clientLogger = LSClientLogger.getInstance();
    }

    @Override
    public void didChangeConfiguration(DidChangeConfigurationParams didChangeConfigurationParams) {
        this.clientLogger.logMessage("Operation 'workspace/didChangeConfiguration' Ack");
    }

    @Override
    public void didChangeWatchedFiles(DidChangeWatchedFilesParams didChangeWatchedFilesParams) {
        this.clientLogger.logMessage("Operation 'workspace/didChangeWatchedFiles' Ack");
        KTextDocumentService ktxt = (KTextDocumentService) languageServer.getTextDocumentService();
        ktxt.memo.loadCaches();
        languageServer.languageClient.refreshDiagnostics();
    }

    @Override
    public void didRenameFiles(RenameFilesParams params) {
        this.clientLogger.logMessage("Operation 'workspace/didRenameFiles' Ack");
    }

    @Override
    public CompletableFuture<Object> executeCommand(ExecuteCommandParams params) {
        return CompletableFuture.supplyAsync(() -> {
            clientLogger.logMessage("Operation 'workspace/executeCommand' " + params.getCommand());
            String kast = ((KTextDocumentService) languageServer.getTextDocumentService()).memo.showKast(params.getCommand());
            return List.of();
        });
    }
}
