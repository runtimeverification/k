package org.kframework.lsp;

import org.eclipse.lsp4j.*;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.services.TextDocumentService;
import org.jetbrains.annotations.NotNull;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.kil.*;
import org.kframework.kil.Module;
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
            Position pos = position.getPosition();
            List<CompletionItem> lci = new ArrayList<>();
            List<DefinitionItem> fileDi = new ArrayList<>(elems.getOrDefault(position.getTextDocument().getUri(), List.of()));
            fileDi.addAll(elems.get(domains.toString()));
            fileDi.addAll(elems.get(kast.toString()));
            fileDi.stream().filter(i -> i instanceof Module)
                    .map(m -> ((Module) m))
                    .forEach(m -> m.getItems().forEach((mi -> {
                        if (isPositionOverLocation(pos, mi.getLocation())) {
                            if (mi instanceof Import) {
                                elems.forEach((uri, ddis) -> ddis.stream()
                                        .filter(mi2 -> mi2 instanceof Module)
                                        .map(m2 -> ((Module) m2))
                                        .forEach(m2 -> {
                                            CompletionItem ci = new CompletionItem();
                                            ci.setLabel(m2.getName());
                                            ci.setInsertText(m2.getName());
                                            ci.setKind(CompletionItemKind.Snippet);
                                            lci.add(new CompletionItem());
                                        }));
                            } else if (mi instanceof Syntax) {
                                fileDi.stream().filter(i -> i instanceof Module)
                                        .map(m3 -> ((Module) m3))
                                        .forEach(m3 -> m3.getItems().stream()
                                                .filter(mi3 -> mi3 instanceof Syntax)
                                                .map(s -> ((Syntax) s))
                                                .forEach(s -> {
                                                    CompletionItem ci = new CompletionItem();
                                                    ci.setLabel(s.getDeclaredSort().getSort().name());
                                                    ci.setInsertText(s.getDeclaredSort().getSort().name());
                                                    ci.setKind(CompletionItemKind.Snippet);
                                                    lci.add(new CompletionItem());
                                                }));
                            } else if (mi instanceof StringSentence) {
                                lci.addAll(getCompletionItems(fileDi));
                            }
                        }
                    })));
// TODO: add completion for attributes
            this.clientLogger.logMessage("Operation '" + "text/completion: " + position.getTextDocument().getUri() + " #pos: " + pos.getLine() + " " + pos.getCharacter());
            return Either.forLeft(lci);
        });
    }

    static Pattern ptrn = Pattern.compile("[a-zA-Z0-9#]+");

    private static List<CompletionItem> getCompletionItems(List<DefinitionItem> dis) {
        List<CompletionItem> lci = new ArrayList<>();
        // Traverse all the modules and all the syntax declarations to find the Terminals in productions
        // For each Terminal that follows the <ptrn> above, create a CompletionItem with some documentation
        // Tree structure: Definition -> Module -> Syntax -> PriorityBlock -> Production -> Terminal
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
                                                        CompletionItem completionItem = buildCompletionItem(m, s, p, t);
                                                        lci.add(completionItem);
                                                    }
                                                }))))));

        return lci;
    }

    @NotNull
    private static CompletionItem buildCompletionItem(Module m, Syntax s, Production p, Terminal t) {
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
        return completionItem;
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
            Range range = loc2range(loc);
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
        String uri = args[0];
        ExtractFencedKCodeFromMarkdown mdExtractor = new ExtractFencedKCodeFromMarkdown(null, "k");
        List<DefinitionItem> dis = Outer.parse(Source.apply(uri), FileUtil.load(new File(new URI(uri))), null);
        List<DefinitionItem> doma = Outer.parse(Source.apply(domains.toString()), mdExtractor.extract(FileUtil.load(new File(domains)), Source.apply(uri)), null);
        List<DefinitionItem> kst = Outer.parse(Source.apply(kast.toString()), mdExtractor.extract(FileUtil.load(new File(kast)), Source.apply(uri)), null);
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
            this.clientLogger.logMessage("Operation '" + "text/diagnostics: " + params.getTextDocument().getUri() + " #problems: " + problems.size());
            return report;
        }, delayedExecutor);
        latestScheduled = scheduledFuture;
        return scheduledFuture;
    }

    public CompletableFuture<Either<List<? extends org.eclipse.lsp4j.Location>, List<? extends LocationLink>>> definition(DefinitionParams params) {
        Position pos = new Position(params.getPosition().getLine() + 1, params.getPosition().getCharacter() + 1);
        this.clientLogger.logMessage("Operation '" + "text/definition: " + params.getTextDocument().getUri() + " #pos: " + pos.getLine() + " " + pos.getCharacter());
        return CompletableFuture.supplyAsync(() -> {
            List<LocationLink> lls = new ArrayList<>();
            try {
                List<DefinitionItem> dis = elems.getOrDefault(params.getTextDocument().getUri(), List.of());
                for (DefinitionItem di : dis) {
                    if (di instanceof Require) {
                        Location loc = getSafeLoc(di);
                        if (isPositionOverLocation(pos, loc)) {
                            Require req = (Require) di;
                            File f = new File(new URI(params.getTextDocument().getUri()));
                            URI targetURI = new File(f.getParent() + File.separatorChar + req.getValue()).toURI();

                            lls.add(new LocationLink(targetURI.toString(),
                                    new Range(new Position(0, 0), new Position(0, 0)),
                                    new Range(new Position(0, 0), new Position(0, 0)),
                                    loc2range(loc)));
                        }
                    } else if (di instanceof Module) {
                        Module m = (Module) di;
                        for (ModuleItem mi : m.getItems()) {
                            if (mi instanceof Import) {
                                Location loc = getSafeLoc(mi);
                                if (isPositionOverLocation(pos, loc)) {
                                    Import imp = (Import) mi;
                                    elems.forEach((uri, ddis) -> ddis.forEach((ddi) -> {
                                        if (ddi instanceof Module && ((Module) ddi).getName().equals(imp.getName()))
                                            lls.add(new LocationLink(uri,
                                                    loc2range(getSafeLoc(ddi)),
                                                    loc2range(getSafeLoc(ddi)),
                                                    loc2range(getSafeLoc(imp))));
                                        })
                                    );
                                }
                            }
                        }
                    }
                }
            } catch (URISyntaxException e) {
                throw new RuntimeException();
            }

            return Either.forRight(lls);
        });
    }

    public static Location getSafeLoc(ASTNode node) {
        return node.location().orElse(new Location(0,0,0,0));
    }
    public static boolean isPositionOverLocation(Position pos, Location loc) {
        return loc.startLine() <= pos.getLine() &&
                pos.getLine() <= loc.endLine() &&
                loc.startColumn() <= pos.getCharacter() &&
                pos.getCharacter() <= loc.endColumn();
    }
    public static Range loc2range(Location loc) {
        return new Range(new Position(loc.startLine() -1 , loc.startColumn() - 1), new Position(loc.endLine() - 1, loc.endColumn() - 1));
    }
}