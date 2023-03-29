// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.lsp;

import org.eclipse.lsp4j.MessageParams;
import org.eclipse.lsp4j.MessageType;
import org.eclipse.lsp4j.services.LanguageClient;

/**
 * Use this class to send log messages to the client.
 */
public class LSClientLogger {

    private static LSClientLogger INSTANCE;
    private LanguageClient client;
    private boolean isInitialized;

    private LSClientLogger() {
    }

    public void initialize(LanguageClient languageClient) {
        if (!Boolean.TRUE.equals(isInitialized)) {
            this.client = languageClient;
        }
        isInitialized = true;
    }

    public static LSClientLogger getInstance() {
        if (INSTANCE == null) {
            INSTANCE = new LSClientLogger();
        }
        return INSTANCE;
    }

    public void logMessage(String message) {
        if (!isInitialized) {
            return;
        }
        client.logMessage(new MessageParams(MessageType.Info, message));
    }
}
