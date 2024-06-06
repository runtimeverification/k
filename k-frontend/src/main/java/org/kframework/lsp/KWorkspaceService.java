// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.lsp;

import org.eclipse.lsp4j.DidChangeConfigurationParams;
import org.eclipse.lsp4j.DidChangeWatchedFilesParams;
import org.eclipse.lsp4j.RenameFilesParams;
import org.eclipse.lsp4j.services.WorkspaceService;

/** WorkspaceService implementation for K. */
public class KWorkspaceService implements WorkspaceService {

  private final KLanguageServer languageServer;
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
}
