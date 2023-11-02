// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.lsp;

import static org.kframework.kompile.Kompile.CACHE_FILE_NAME;

import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;
import org.eclipse.lsp4j.*;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.services.LanguageClient;
import org.eclipse.lsp4j.services.LanguageClientAware;
import org.eclipse.lsp4j.services.LanguageServer;
import org.eclipse.lsp4j.services.TextDocumentService;
import org.eclipse.lsp4j.services.WorkspaceService;
import org.kframework.main.Main;

/** Language Server implementation for the K framework. */
public class KLanguageServer implements LanguageServer, LanguageClientAware {

  private final TextDocumentService textDocumentService;
  private final WorkspaceService workspaceService;
  private ClientCapabilities clientCapabilities;
  LanguageClient languageClient;
  List<WorkspaceFolder> workspaceFolders;
  private int shutdown = 1;

  public KLanguageServer() {
    try {
      this.textDocumentService = new KTextDocumentService(this);
    } catch (URISyntaxException e) {
      throw new RuntimeException(e);
    }
    this.workspaceService = new KWorkspaceService(this);
  }

  @Override
  public CompletableFuture<InitializeResult> initialize(InitializeParams initializeParams) {
    workspaceFolders = initializeParams.getWorkspaceFolders();
    LSClientLogger.getInstance()
        .logMessage("initWorkspaceFolders: " + initializeParams.getWorkspaceFolders());

    final InitializeResult response = new InitializeResult(new ServerCapabilities());
    // Set the document synchronization capabilities to full.
    response.getCapabilities().setTextDocumentSync(TextDocumentSyncKind.Full);
    this.clientCapabilities = initializeParams.getCapabilities();

    /* Check if dynamic registration of completion capability is allowed by the client. If so we don't register the capability.
      Else, we register the completion capability.
    */
    // TODO: check if this needs to be guarded
    response.getCapabilities().setReferencesProvider(true);
    response.getCapabilities().setDefinitionProvider(true);
    response.getCapabilities().setSelectionRangeProvider(true);

    if (!isDynamicCompletionRegistration())
      response.getCapabilities().setCompletionProvider(new CompletionOptions());
    if (!isDiagnosticRegistration())
      response
          .getCapabilities()
          .setDiagnosticProvider(new DiagnosticRegistrationOptions(false, false));
    return CompletableFuture.supplyAsync(() -> response);
  }

  @Override
  public void initialized(InitializedParams params) {
    // Check if dynamic completion support is allowed, if so register.
    if (isDynamicCompletionRegistration()) {
      CompletionRegistrationOptions completionRegistrationOptions =
          new CompletionRegistrationOptions();
      Registration completionRegistration =
          new Registration(
              UUID.randomUUID().toString(),
              "textDocument/completion",
              completionRegistrationOptions);
      languageClient.registerCapability(new RegistrationParams(List.of(completionRegistration)));
    }
    if (isDiagnosticRegistration()) {
      DiagnosticRegistrationOptions diagnosticRegistrationOptions =
          new DiagnosticRegistrationOptions(false, false);
      Registration diagnosticRegistration =
          new Registration(
              UUID.randomUUID().toString(),
              "textDocument/diagnostic",
              diagnosticRegistrationOptions);
      languageClient.registerCapability(new RegistrationParams(List.of(diagnosticRegistration)));
    }
    // Register file watchers
    List<FileSystemWatcher> watchers = new ArrayList<>();
    watchers.add(
        new FileSystemWatcher(
            Either.forLeft("/**/" + CACHE_FILE_NAME),
            WatchKind.Create + WatchKind.Delete + WatchKind.Change));
    DidChangeWatchedFilesRegistrationOptions opts =
        new DidChangeWatchedFilesRegistrationOptions(watchers);
    Registration registration =
        new Registration(UUID.randomUUID().toString(), "workspace/didChangeWatchedFiles", opts);
    languageClient.registerCapability(
        new RegistrationParams(Collections.singletonList(registration)));
  }

  @Override
  public CompletableFuture<Object> shutdown() {
    shutdown = 0;
    return CompletableFuture.supplyAsync(Object::new);
  }

  @Override
  public void exit() {
    Main.exit(shutdown);
  }

  @Override
  public TextDocumentService getTextDocumentService() {
    return this.textDocumentService;
  }

  @Override
  public WorkspaceService getWorkspaceService() {
    return this.workspaceService;
  }

  @Override
  public void connect(LanguageClient languageClient) {
    this.languageClient = languageClient;
    LSClientLogger.getInstance().initialize(this.languageClient);
  }

  private boolean isDynamicCompletionRegistration() {
    TextDocumentClientCapabilities textDocumentCapabilities = clientCapabilities.getTextDocument();
    return textDocumentCapabilities != null
        && textDocumentCapabilities.getCompletion() != null
        && Boolean.FALSE.equals(textDocumentCapabilities.getCompletion().getDynamicRegistration());
  }

  private boolean isDiagnosticRegistration() {
    TextDocumentClientCapabilities textDocumentCapabilities = clientCapabilities.getTextDocument();
    return textDocumentCapabilities != null && textDocumentCapabilities.getDiagnostic() != null;
  }
}
