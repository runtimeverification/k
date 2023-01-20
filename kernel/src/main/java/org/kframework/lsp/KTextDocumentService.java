package org.kframework.lsp;

import org.eclipse.lsp4j.*;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.services.TextDocumentService;
import org.jetbrains.annotations.NotNull;
import org.kframework.attributes.Att;
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
import scala.Tuple2;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.LinkOption;
import java.util.*;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executor;
import java.util.concurrent.TimeUnit;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import static org.kframework.Collections.*;

/**
 * TextDocumentService implementation for K.
 */
public class KTextDocumentService implements TextDocumentService {

    private final KLanguageServer languageServer;
    private final LSClientLogger clientLogger;

    public final TextDocumentSyncHandler files = new TextDocumentSyncHandler();
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
        TextDocumentSyncHandler d = new TextDocumentSyncHandler();
        files.add(domains.toString());
        files.add(kast.toString());
    }

    @Override
    public void didOpen(DidOpenTextDocumentParams didOpenTextDocumentParams) {
        this.clientLogger.logMessage("Operation '" + "text/didOpen" +
                "' {fileUri: '" + didOpenTextDocumentParams.getTextDocument().getUri() + "'} opened");
        files.didOpen(didOpenTextDocumentParams);
    }

    @Override
    public void didChange(DidChangeTextDocumentParams didChangeTextDocumentParams) {
        this.clientLogger.logMessage("Operation '" + "text/didChange" +
                "' {fileUri: '" + didChangeTextDocumentParams.getTextDocument().getUri() + "'} Changed");
        files.didChange(didChangeTextDocumentParams);
    }

    @Override
    public void didClose(DidCloseTextDocumentParams didCloseTextDocumentParams) {
        this.clientLogger.logMessage("Operation '" + "text/didClose" +
                "' {fileUri: '" + didCloseTextDocumentParams.getTextDocument().getUri() + "'} Closed");
        if (!(didCloseTextDocumentParams.getTextDocument().getUri().equals(domains.toString())
                || didCloseTextDocumentParams.getTextDocument().getUri().equals(kast.toString())))
            files.didClose(didCloseTextDocumentParams);
    }

    @Override
    public void didSave(DidSaveTextDocumentParams didSaveTextDocumentParams) {
        this.clientLogger.logMessage("Operation '" + "text/didSave" +
                "' {fileUri: '" + didSaveTextDocumentParams.getTextDocument().getUri() + "'} Saved");
        files.didSave(didSaveTextDocumentParams);
    }

    @Override
    public CompletableFuture<Either<List<CompletionItem>, CompletionList>> completion(CompletionParams position) {
        return CompletableFuture.supplyAsync(() -> {
            Position pos = position.getPosition();
            List<CompletionItem> lci = new ArrayList<>();
            KTextDocument doc = files.files.get(position.getTextDocument().getUri());
            String context = doc.getContextAt(position.getPosition());
            List<DefinitionItem> allDi = files.files.entrySet().stream().flatMap((u) -> u.getValue().dis.stream()).collect(Collectors.toList());
            switch (context) {
                case "import":
                case "imports":
                    files.files.forEach((uri, ddis) -> ddis.dis.stream()
                            .filter(mi2 -> mi2 instanceof Module)
                            .map(m2 -> ((Module) m2))
                            .forEach(m2 -> {
                                CompletionItem ci = new CompletionItem();
                                ci.setLabel(m2.getName());
                                ci.setInsertText(m2.getName());
                                ci.setKind(CompletionItemKind.Snippet);
                                lci.add(ci);
                            })); break;
                case "syntax":
                    Map<String, Set<Att>> allSorts = allDi.stream().filter(i -> i instanceof Module)
                            .map(m3 -> ((Module) m3))
                            .flatMap(m3 -> m3.getItems().stream()
                                    .filter(mi3 -> mi3 instanceof Syntax)
                                    .map(s -> ((Syntax) s))
                                    .filter(s -> !s.getParams().contains(s.getDeclaredSort().getRealSort()))
                                    .map(s -> Tuple2.apply(s.getDeclaredSort().getRealSort().name(), s.getAttributes())))
                            .collect(Collectors.groupingBy(Tuple2::_1, Collectors.mapping(Tuple2::_2, Collectors.toSet())));
                    Map<String, Att> allSorts2 = allSorts.entrySet().stream()
                            .map(e -> Tuple2.apply(e.getKey(), Att.mergeAttributes(immutable(e.getValue()))))
                            .collect(Collectors.toMap(Tuple2::_1, Tuple2::_2));
                    allSorts2.forEach((sortName, at) -> {
                        CompletionItem ci = new CompletionItem();
                        ci.setLabel(sortName);
                        ci.setInsertText(sortName);
                        //ci.setDetail("module " + m.getName());
                        String documentation = "syntax " + sortName + " ";
                        documentation += at.toString();
                        ci.setDocumentation(documentation);
                        ci.setKind(CompletionItemKind.Snippet);
                        lci.add(ci);
                    }); break;

                case "context":
                case "rule":
                case "configuration":
                case "claim":
                    lci.addAll(getCompletionItems(allDi)); break;
            }
            this.clientLogger.logMessage("Operation '" + "text/completion: " + position.getTextDocument().getUri() + " #pos: " + pos.getLine() + " " + pos.getCharacter()
            + " context: " + context + " #: " + lci.size());

            // TODO: add completion for attributes
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

    // for quick testing
    public static void main(String[] args) throws InterruptedException, ExecutionException, URISyntaxException {
        String uri = args[0];
        System.out.println(isPositionOverLocation(new Position(10, 16), new Location(9, 3, 12, 17)));
        KLanguageServer kls = new KLanguageServer();
        kls.getTextDocumentService().didOpen(new DidOpenTextDocumentParams(new TextDocumentItem(uri, "kframework", 1, FileUtil.load(new File(new URI(uri))))));

        CompletableFuture<DocumentDiagnosticReport> diags = kls.getTextDocumentService().diagnostic(new DocumentDiagnosticParams(new TextDocumentIdentifier(uri)));
        RelatedFullDocumentDiagnosticReport z = diags.get().getLeft();
        //System.out.println("Diags: " + z);

        CompletableFuture<Either<List<CompletionItem>, CompletionList>> x = kls.getTextDocumentService().completion(new CompletionParams(new TextDocumentIdentifier(uri), new Position(10, 17)));
        List<CompletionItem> y = x.get().getLeft();
        System.out.println("Completion: " + y.size());

        CompletableFuture<Either<List<? extends org.eclipse.lsp4j.Location>, List<? extends LocationLink>>> defin = kls.getTextDocumentService().definition(new DefinitionParams(new TextDocumentIdentifier(uri), new Position(21, 6)));
        List<? extends LocationLink> defRez = defin.get().getRight();
        //System.out.println("GoToDef: " + defRez);
    }

    // previous diagnostics task. If it's still active, cancel it and run a newer, updated one
    private CompletableFuture<DocumentDiagnosticReport> latestScheduled;

    public CompletableFuture<DocumentDiagnosticReport> diagnostic(DocumentDiagnosticParams params) {
        if (latestScheduled != null && !latestScheduled.isDone())
            latestScheduled.completeExceptionally(new Throwable("Cancelled diagnostic publisher"));

        Executor delayedExecutor = CompletableFuture.delayedExecutor(1, TimeUnit.SECONDS);
        CompletableFuture<DocumentDiagnosticReport> scheduledFuture = CompletableFuture.supplyAsync(() -> {
            files.files.get(params.getTextDocument().getUri()).outerParse();
            List<Diagnostic> problems = files.files.get(params.getTextDocument().getUri()).problems;
            DocumentDiagnosticReport report = new DocumentDiagnosticReport(new RelatedFullDocumentDiagnosticReport(problems));
            this.clientLogger.logMessage("Operation '" + "text/diagnostics: " + params.getTextDocument().getUri() + " #problems: " + problems.size());
            return report;
        }, delayedExecutor);
        latestScheduled = scheduledFuture;
        return scheduledFuture;
    }

    public CompletableFuture<Either<List<? extends org.eclipse.lsp4j.Location>, List<? extends LocationLink>>> definition(DefinitionParams params) {
        Position pos = new Position(params.getPosition().getLine() + 1, params.getPosition().getCharacter() + 1);
        return CompletableFuture.supplyAsync(() -> {
            this.clientLogger.logMessage("Operation '" + "text/definition: " + params.getTextDocument().getUri() + " #pos: " + pos.getLine() + " " + pos.getCharacter());
            List<LocationLink> lls = new ArrayList<>();
            try {
                List<DefinitionItem> dis = files.files.get(params.getTextDocument().getUri()).dis;
                for (DefinitionItem di : dis) {
                    if (di instanceof Require) {
                        Location loc = getSafeLoc(di);
                        if (isPositionOverLocation(pos, loc)) {
                            Require req = (Require) di;
                            File f = new File(new URI(params.getTextDocument().getUri()));
                            URI targetURI = new File(f.getParent() + File.separatorChar + req.getValue()).toURI();

                            lls.add(new LocationLink(targetURI.toString(),
                                    new Range(new Position(0, 0), new Position(10, 0)),
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
                                    files.files.forEach((uri, ddis) -> ddis.dis.forEach((ddi) -> {
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
        return (loc.startLine() < pos.getLine() || (loc.startLine() == pos.getLine() && loc.startColumn() <= pos.getCharacter())) &&
                (pos.getLine() < loc.endLine() || (pos.getLine() == loc.endLine() && pos.getCharacter() <= loc.endColumn()));
    }
    public static Range loc2range(Location loc) {
        return new Range(new Position(loc.startLine() -1 , loc.startColumn() - 1), new Position(loc.endLine() - 1, loc.endColumn() - 1));
    }
}