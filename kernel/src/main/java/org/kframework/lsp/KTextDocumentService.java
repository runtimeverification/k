package org.kframework.lsp;

import org.eclipse.lsp4j.*;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.services.TextDocumentService;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Module;
import org.kframework.kil.Syntax;
import org.kframework.kil.Terminal;
import org.kframework.kompile.Kompile;
import org.kframework.kore.Sort;
import org.kframework.parser.outer.ExtractFencedKCodeFromMarkdown;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.LinkOption;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executor;
import java.util.concurrent.TimeUnit;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * TextDocumentService implementation for K.
 */
public class KTextDocumentService implements TextDocumentService {

    private final KLanguageServer languageServer;
    private final LSClientLogger clientLogger;

    private final Map<String, List<DefinitionItem>> elems = new HashMap<>();
    private final ExtractFencedKCodeFromMarkdown mdExtractor = new ExtractFencedKCodeFromMarkdown(null, "k");
    private static final URI domains;
    private static final URI kast;

    static {
        try {
            domains = new File(Kompile.BUILTIN_DIRECTORY.toString() + File.separatorChar + "domains.md").toPath().toRealPath(LinkOption.NOFOLLOW_LINKS).toUri();
            kast = new File(Kompile.BUILTIN_DIRECTORY.toString() + File.separatorChar + "kast.md").toPath().toRealPath(LinkOption.NOFOLLOW_LINKS).toUri();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }


    public KTextDocumentService(KLanguageServer languageServer) throws URISyntaxException {
        this.languageServer = languageServer;
        this.clientLogger = LSClientLogger.getInstance();
    }

    @Override
    public void didOpen(DidOpenTextDocumentParams didOpenTextDocumentParams) {
        this.clientLogger.logMessage("Operation '" + "text/didOpen" +
                "' {fileUri: '" + didOpenTextDocumentParams.getTextDocument().getUri() + "'} opened");
        outerParse(didOpenTextDocumentParams.getTextDocument().getUri());
        if (!elems.containsKey(domains.toString())) {
            this.clientLogger.logMessage("Builtin: " + domains);
            outerParse(domains.toString());
        }
        if (!elems.containsKey(kast.toString())) {
            this.clientLogger.logMessage("Builtin: " + domains);
            outerParse(kast.toString());
        }
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
            List<DefinitionItem> fileDi = new ArrayList<>(elems.getOrDefault(position.getTextDocument().getUri(), List.of()));
            fileDi.addAll(elems.get(domains.toString()));
            fileDi.addAll(elems.get(kast.toString()));
            this.clientLogger.logMessage("Operation '" + "text/completion: " + position.getTextDocument() + " #di: " + fileDi.size());
            return Either.forLeft(getCompletionItems(fileDi));
        });
    }

    static Pattern ptrn = Pattern.compile("[a-zA-Z0-9#]+");

    private static List<CompletionItem> getCompletionItems(List<DefinitionItem> dis) {
        List<CompletionItem> lci = new ArrayList<>();
        dis.stream().filter(i -> i instanceof Module)
                .map(m -> ((Module) m))
                .forEach(m -> m.getItems().stream()
                        .filter(mi -> mi instanceof Syntax)
                        .map(s -> ((Syntax) s))
                        .forEach(s -> s.getPriorityBlocks()
                                .forEach((pb -> pb.getProductions()
                                        .forEach(p -> p.getItems().stream()
                                                .filter(pi -> pi instanceof Terminal)
                                                .map(t -> (Terminal) t)
                                                .forEach(t -> {
                                                    if (ptrn.matcher(t.getTerminal()).matches()) {
                                                        CompletionItem completionItem = new CompletionItem();
                                                        completionItem.setLabel(t.getTerminal());
                                                        completionItem.setInsertText(t.getTerminal());
                                                        completionItem.setDetail("module " + m.getName());
                                                        String doc = "syntax ";
                                                        doc += !s.getParams().isEmpty() ?
                                                                "{" + s.getParams().stream().map(Sort::toString).collect(Collectors.joining(", ")) + "} " : "";
                                                        doc += s.getDeclaredSort() + " ::= ";
                                                        doc += p.toString();
                                                        completionItem.setDocumentation(doc);
                                                        completionItem.setKind(CompletionItemKind.Snippet);
                                                        lci.add(completionItem);
                                                    }
                                                }))))));

        return lci;
    }

    private List<Diagnostic> outerParse(String uri) {
        List<DefinitionItem> di = null;
        List<Diagnostic> problems = new ArrayList<>();
        try {
            String contents = FileUtil.load(new File(new URI(uri)));
            if (uri.endsWith(".md"))
                contents = mdExtractor.extract(contents, Source.apply(uri));
            di = Outer.parse(Source.apply(uri), contents, null);
            elems.put(uri, di);
        } catch (URISyntaxException e) {
            throw new RuntimeException(e);
        } catch (KEMException e) {
            Location loc = e.exception.getLocation();
            if (loc == null) loc = new Location(1, 1, 1, 2);
            Range range = new Range(new Position(loc.startLine() - 1, loc.startColumn() - 1),
                    new Position(loc.endLine() - 1, loc.endColumn() - 1));
            Diagnostic d = new Diagnostic(range, e.exception.getMessage(), DiagnosticSeverity.Error, "Outer Parser");
            problems.add(d);
        }
        if (problems.isEmpty())
            this.clientLogger.logMessage("Operation 'outerParse' #di: " + di.size());
        else
            this.clientLogger.logMessage("Operation 'outerParse' #problems: " + problems.size());
        return problems;
    }

    // for quick testing
    public static void main(String[] args) throws InterruptedException, ExecutionException, URISyntaxException {
        String uri = "file:///home/radu/work/test/test.k";
        List<DefinitionItem> dis = Outer.parse(Source.apply(uri), FileUtil.load(new File(new URI(uri))), null);
        List<DefinitionItem> doma = Outer.parse(Source.apply(domains.toString()), FileUtil.load(new File(domains)), null);
        List<DefinitionItem> kst = Outer.parse(Source.apply(kast.toString()), FileUtil.load(new File(kast)), null);
        List<CompletionItem> x = getCompletionItems(dis);
        System.out.println(x.size());
    }

    // previous diagnostics task. If it's still active, cancel it and run a newer, updated one
    private CompletableFuture<DocumentDiagnosticReport> latestScheduled;
    public CompletableFuture<DocumentDiagnosticReport> diagnostic(DocumentDiagnosticParams params) {
        if (latestScheduled != null && !latestScheduled.isDone())
            latestScheduled.completeExceptionally(new Throwable("Cancelled diagnostic publisher"));

        Executor delayedExecutor = CompletableFuture.delayedExecutor(1, TimeUnit.SECONDS);
        CompletableFuture<DocumentDiagnosticReport> scheduledFuture = CompletableFuture.supplyAsync(() -> {
            List<Diagnostic> problems = outerParse(params.getTextDocument().getUri());
            DocumentDiagnosticReport report = new DocumentDiagnosticReport(new RelatedFullDocumentDiagnosticReport(problems));
            this.clientLogger.logMessage("Operation '" + "text/diagnostics: " + params.getTextDocument() + " #problems: " + problems.size());
            return report;
        }, delayedExecutor);
        latestScheduled = scheduledFuture;
        return scheduledFuture;
    }
}
