package org.kframework.lsp;


import org.eclipse.lsp4j.*;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.kframework.kil.Module;
import org.kframework.kil.*;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.inner.ParseCache;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.util.*;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.Executor;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import static org.kframework.lsp.CompletionHelper.*;

/**
 * Handle the caches of all the files of interest.
 */
public class TextDocumentSyncHandler {

    public Map<String, KTextDocument> files = new HashMap<>();
    public java.util.List<IDECache> caches;
    private final LSClientLogger clientLogger;
    private final WorkspaceFolder workspaceFolder;

    private static final BinaryLoader loader = new BinaryLoader(new KExceptionManager(new GlobalOptions()));


    public TextDocumentSyncHandler(LSClientLogger clientLogger, WorkspaceFolder workspaceFolder) {
        this.clientLogger = clientLogger;
        this.workspaceFolder = workspaceFolder;
    }

    public void findCacheFile() {
        if (workspaceFolder == null)
            return;
        try {
            Optional<Path> cacheFile = Files.walk(Path.of(workspaceFolder.getName())).filter(p -> p.endsWith("cache.bin.ide")).findFirst();
            cacheFile.ifPresent(path -> caches = loader.loadCache(java.util.List.class, path.toFile()));
        } catch (IOException e) {
            clientLogger.logMessage("findCachesException: " + e);
        }
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

    // Create a list of CompletionItems depending on the context.
    // A work in progress file may not parse, but we still want to have completion working, therefore we use a regex
    // to find the closest keyword, and approximate the context.
    public CompletableFuture<Either<List<CompletionItem>, CompletionList>> completion(CompletionParams position) {
        return CompletableFuture.supplyAsync(() -> {
            KPos pos = new KPos(position.getPosition());
            List<CompletionItem> lci = new ArrayList<>();
            KTextDocument doc = files.get(position.getTextDocument().getUri());
            String context = doc.getContextAt(pos);
            List<DefinitionItem> allDi = slurp(position.getTextDocument().getUri());
            switch (context) {
                case "":
                    lci.add(getNewRequiresCompletion());
                    lci.add(getNewModuleCompletion()); break;
                case "endmodule":
                    lci.add(getNewModuleCompletion()); break;
                case "module":
                    lci.add(getNewImportCompletion());
                    lci.addAll(getNewSentenceCompletion()); break;
                case "import":
                case "imports":
                    lci.add(getNewImportCompletion());
                    lci.addAll(getNewSentenceCompletion());
                    lci.addAll(getImportCompletion(allDi)); break;
                case "syntax":
                    lci.addAll(getNewSentenceCompletion());
                    lci.addAll(getSyntaxCompletion(allDi)); break;
                case "context":
                case "rule":
                case "configuration":
                case "claim":
                    lci.addAll(getNewSentenceCompletion());
                    lci.addAll(getRuleCompletion(allDi)); break;
            }
            this.clientLogger.logMessage("Operation '" + "text/completion: " + position.getTextDocument().getUri() + " #pos: "
                    + pos.getLine() + " " + pos.getCharacter() + " context: " + context + " #: " + lci.size());

            // TODO: add completion for attributes
            return Either.forLeft(lci);
        });
    }

    // At the moment we only have access to outer parsing information, so we can find the definition for
    // imported module names and required files
    public CompletableFuture<Either<List<? extends org.eclipse.lsp4j.Location>, List<? extends LocationLink>>> definition(DefinitionParams params) {
        KPos pos = new KPos(params.getPosition());
        return CompletableFuture.supplyAsync(() -> {
            this.clientLogger.logMessage("Operation '" + "text/definition: " + params.getTextDocument().getUri() + " #pos: " + pos.getLine() + " " + pos.getCharacter());
            List<LocationLink> lls = new ArrayList<>();
            try {
                List<DefinitionItem> dis = files.get(params.getTextDocument().getUri()).dis;
                for (DefinitionItem di : dis) {
                    if (di instanceof Require) {
                        org.kframework.attributes.Location loc = getSafeLoc(di);
                        if (isPositionOverLocation(pos, loc)) {
                            Require req = (Require) di;
                            File f = new File(new URI(params.getTextDocument().getUri()));
                            URI targetURI = Path.of(f.getParent(), req.getValue()).toRealPath(LinkOption.NOFOLLOW_LINKS).toUri();
                            lls.add(new LocationLink(targetURI.toString(),
                                    new Range(new Position(0, 0), new Position(10, 0)),
                                    new Range(new Position(0, 0), new Position(0, 0)),
                                    loc2range(loc)));
                            break;
                        }
                    } else if (di instanceof Module) {
                        Module m = (Module) di;
                        for (ModuleItem mi : m.getItems()) {
                            if (mi instanceof Import) {
                                org.kframework.attributes.Location loc = getSafeLoc(mi);
                                if (isPositionOverLocation(pos, loc)) {
                                    Import imp = (Import) mi;
                                    List<DefinitionItem> allDi = slurp(params.getTextDocument().getUri());
                                    allDi.stream().filter(ddi -> ddi instanceof Module)
                                            .map(ddi -> ((Module) ddi))
                                            .filter(m2 -> m2.getName().equals(imp.getName()))
                                            .forEach(m3 -> lls.add(new LocationLink(URI.create(m3.getSource().source()).toString(),
                                                    loc2range(getSafeLoc(m3)),
                                                    loc2range(getSafeLoc(m3)),
                                                    loc2range(getSafeLoc(imp)))));
                                    break;
                                }
                            }
                        }
                    }
                }
            } catch (URISyntaxException | IOException e) {
                clientLogger.logMessage("definition failed: " + params.getTextDocument().getUri() + e);
            }

            return Either.forRight(lls);
        });
    }

    // in case a node doesn't have a location information, return Location(0,0,0,0)
    public static org.kframework.attributes.Location getSafeLoc(ASTNode node) {
        return node.location().orElse(new org.kframework.attributes.Location(0,0,0,0));
    }

    // true if Position(l,c) is over Location(startL, startC, endL, endC). Expects Position to start from 1, just as Location
    public static boolean isPositionOverLocation(KPos pos, org.kframework.attributes.Location loc) {
        return (loc.startLine() < pos.getLine() || (loc.startLine() == pos.getLine() && loc.startColumn() <= pos.getCharacter())) &&
                (pos.getLine() < loc.endLine() || (pos.getLine() == loc.endLine() && pos.getCharacter() <= loc.endColumn()));
    }

    // K starts counting lines and columns from 1 and LSP starts counting from 0
    public static Range loc2range(org.kframework.attributes.Location loc) {
        return new Range(new Position(loc.startLine() - 1 , loc.startColumn() - 1), new Position(loc.endLine() - 1, loc.endColumn() - 1));
    }

    // previous diagnostics task. If it's still active, cancel it and run a newer, updated one
    private final Map<String, CompletableFuture<DocumentDiagnosticReport>> latestDiagnosticScheduled = new HashMap<>();

    public CompletableFuture<DocumentDiagnosticReport> diagnostic(DocumentDiagnosticParams params) {
        String uri = params.getTextDocument().getUri();
        if (latestDiagnosticScheduled.containsKey(uri) && !latestDiagnosticScheduled.get(uri).isDone())
            latestDiagnosticScheduled.get(uri).completeExceptionally(new Throwable("Cancelled diagnostic publisher"));

        Executor delayedExecutor = CompletableFuture.delayedExecutor(KTextDocumentService.DELAY_EXECUTION_MS, TimeUnit.MILLISECONDS);
        CompletableFuture<DocumentDiagnosticReport> scheduledFuture = CompletableFuture.supplyAsync(() -> {
            files.get(params.getTextDocument().getUri()).outerParse();
            List<Diagnostic> problems = files.get(params.getTextDocument().getUri()).problems;
            DocumentDiagnosticReport report = new DocumentDiagnosticReport(new RelatedFullDocumentDiagnosticReport(problems));
            this.clientLogger.logMessage("Operation '" + "text/diagnostics: " + params.getTextDocument().getUri() + " #problems: " + problems.size());
            return report;
        }, delayedExecutor);
        latestDiagnosticScheduled.put(uri, scheduledFuture);
        return scheduledFuture;
    }

    // find references of modules being used in imports
    public CompletableFuture<List<? extends Location>> references(ReferenceParams params) {
        return CompletableFuture.supplyAsync(() -> {
            KPos pos = new KPos(params.getPosition());
            List<Location> lloc = new ArrayList<>();

            // look in the current file and check if we are positioned anywhere on `module NAME`
            // then find all the imports with this name
            List<DefinitionItem> dis = files.get(params.getTextDocument().getUri()).dis;
            for (DefinitionItem di : dis) {
                org.kframework.attributes.Location loc = getSafeLoc(di);
                if (di instanceof Module && isPositionOverLocation(pos, loc)) {
                    Module m = (Module) di;
                    // we don't store the exact position for the module name so try to calculate it
                    String name = m.getName();
                    org.kframework.attributes.Location nameLoc = new org.kframework.attributes.Location(
                            loc.startLine(), loc.startColumn(), loc.startLine(), loc.startColumn() + "module ".length() + name.length());

                    if (isPositionOverLocation(pos, nameLoc)) {
                        List<DefinitionItem> allDi = files.values().stream()
                                .flatMap(doc -> doc.dis.stream()).collect(Collectors.toList());
                        allDi.stream().filter(ddi -> ddi instanceof Module)
                            .map(ddi -> ((Module) ddi))
                            .forEach(m3 -> m3.getItems().stream()
                                .filter(mi -> mi instanceof Import)
                                .map(mmi -> (Import) mmi)
                                .filter(i -> i.getName().equals(name))
                                .forEach(imp ->
                                    lloc.add(new Location(URI.create(m3.getSource().source()).toString(),
                                        loc2range(getSafeLoc(imp))))));
                    }
                }
            }
            this.clientLogger.logMessage("Operation '" + "text/references: " + params.getTextDocument().getUri() + " #pos: "
                    + pos.getLine() + " " + pos.getCharacter() + " found: " + lloc.size());

            return lloc;
        });
    }
}
