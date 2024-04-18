// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.lsp;

import static org.kframework.kompile.Kompile.CACHE_FILE_NAME;
import static org.kframework.lsp.CompletionHelper.*;

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
import java.util.concurrent.atomic.AtomicReference;
import java.util.stream.Collectors;
import org.eclipse.lsp4j.*;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.kframework.attributes.Att;
import org.kframework.attributes.Source;
import org.kframework.definition.Bubble;
import org.kframework.definition.KViz;
import org.kframework.kil.*;
import org.kframework.kil.Module;
import org.kframework.kompile.DefinitionParsing;
import org.kframework.kore.K;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.inner.ParseCache;
import org.kframework.parser.inner.RuleGrammarGenerator;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

/** Handle the caches of all the files of interest. */
public class TextDocumentSyncHandler {

  public Map<String, KTextDocument> files = new HashMap<>();
  public Map<String, ParseCache> caches = new HashMap<>();
  private final LSClientLogger clientLogger;
  private final KLanguageServer kls;
  private WorkspaceFolder workspaceFolder;
  private Optional<Path> cacheFile = Optional.empty();

  private static final BinaryLoader loader =
      new BinaryLoader(new KExceptionManager(new GlobalOptions()));

  public TextDocumentSyncHandler(LSClientLogger clientLogger, KLanguageServer kls) {
    this.clientLogger = clientLogger;
    this.kls = kls;
  }

  public void findCacheFile() {
    if (workspaceFolder != null || kls.workspaceFolders == null) return;
    try {
      workspaceFolder = kls.workspaceFolders.get(0);
      // TODO: find a better way to get the kompiled directory - maybe with the toml file from
      // KBuild
      cacheFile =
          Files.walk(Path.of(URI.create(workspaceFolder.getUri())))
              .filter(p -> p.endsWith(CACHE_FILE_NAME))
              .min(Comparator.comparing(Path::getNameCount, Comparator.naturalOrder()));
      clientLogger.logMessage("Found cache file: " + cacheFile);
      loadCaches();
    } catch (IOException e) {
      clientLogger.logMessage("findCachesException: " + e);
    }
  }

  public void loadCaches() {
    cacheFile.ifPresent(path -> caches = loader.loadCache(java.util.Map.class, path.toFile()));
    if (caches == null) caches = new HashMap<>();
    caches.forEach(
        (key, val) -> {
          String uri =
              Path.of(
                      val.module()
                          .att()
                          .get(Att.SOURCE(), org.kframework.attributes.Source.class)
                          .source())
                  .toUri()
                  .toString();
          // load into LSP all the files found in the caches, even if they are not open in the IDE.
          // this way we can find all the updated locations when finding references
          if (!files.containsKey(uri)) add(uri);
        });
    clientLogger.logMessage("Loaded cached modules: " + caches.size());
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
    if (files.containsKey(uri)) doc = files.get(uri);
    else {
      doc = new KTextDocument();
      doc.uri = uri;
      files.put(uri, doc);
    }
    doc.updateText(params.getTextDocument().getText());
  }

  public void didChange(DidChangeTextDocumentParams params) {
    files
        .get(params.getTextDocument().getUri())
        .updateText(params.getContentChanges().get(0).getText());
  }

  public void didSave(DidSaveTextDocumentParams params) {
    KTextDocument doc = files.get(params.getTextDocument().getUri());
    doc.outerParse();
  }

  public void didClose(DidCloseTextDocumentParams params) {
    // do not remove files from memory
    // files.remove(params.getTextDocument().getUri());
  }

  // recurse through all the required files and return the list of DefinitionItems
  public List<DefinitionItem> slurp(String uri) {
    Set<String> visited = new HashSet<>();
    visited.add(KTextDocumentService.domains.toString());
    visited.add(KTextDocumentService.kast.toString());
    slurp2(uri, visited);
    List<DefinitionItem> dis =
        files.entrySet().stream()
            .filter(e -> visited.contains(e.getKey()))
            .flatMap(e -> e.getValue().dis.stream())
            .collect(Collectors.toList());
    return dis;
  }

  private void slurp2(String uri, Set<String> visited) {
    if (!files.containsKey(uri)) {
      try {
        if (new File(new URI(uri)).exists()) add(uri);
      } catch (URISyntaxException e) {
        clientLogger.logMessage(
            TextDocumentSyncHandler.class + ".slurp failed1: " + uri + "\n" + e.getMessage());
      }
    }
    KTextDocument current = files.get(uri);
    if (current.parsingOutdated) current.outerParse();
    if (!visited.contains(uri) && files.containsKey(uri)) {
      visited.add(uri);
      files
          .get(uri)
          .dis
          .forEach(
              r -> {
                if (r instanceof Require) {
                  try {
                    Require req = (Require) r;
                    URI targetURI =
                        Path.of(new File(new URI(uri)).getParent(), req.getValue())
                            .toRealPath(LinkOption.NOFOLLOW_LINKS)
                            .toUri();
                    slurp2(targetURI.toString(), visited);
                  } catch (IOException | URISyntaxException e) {
                    clientLogger.logMessage(
                        TextDocumentSyncHandler.class + ".slurp failed2: " + uri + "\n" + e);
                  }
                }
              });
    }
  }

  // Create a list of CompletionItems depending on the context.
  // A work in progress file may not parse, but we still want to have completion working, therefore
  // we use a regex
  // to find the closest keyword, and approximate the context.
  public CompletableFuture<Either<List<CompletionItem>, CompletionList>> completion(
      CompletionParams position) {
    return CompletableFuture.supplyAsync(
        () -> {
          KPos pos = new KPos(position.getPosition());
          List<CompletionItem> lci = new ArrayList<>();
          KTextDocument doc = files.get(position.getTextDocument().getUri());
          String context = doc.getContextAt(pos);
          List<DefinitionItem> allDi = slurp(position.getTextDocument().getUri());
          switch (context) {
            case "" -> {
              lci.add(getNewRequiresCompletion());
              lci.add(getNewModuleCompletion());
            }
            case "endmodule" -> lci.add(getNewModuleCompletion());
            case "module" -> {
              lci.add(getNewImportCompletion());
              lci.addAll(getNewSentenceCompletion());
            }
            case "import", "imports" -> {
              lci.add(getNewImportCompletion());
              lci.addAll(getNewSentenceCompletion());
              lci.addAll(getImportCompletion(allDi));
            }
            case "syntax" -> {
              lci.addAll(getNewSentenceCompletion());
              lci.addAll(getSyntaxCompletion(allDi));
            }
            case "context", "rule", "configuration", "claim" -> {
              lci.addAll(getNewSentenceCompletion());
              lci.addAll(getRuleCompletion(allDi));
            }
          }
          this.clientLogger.logMessage(
              "Operation '"
                  + "text/completion: "
                  + position.getTextDocument().getUri()
                  + " #pos: "
                  + pos.getLine()
                  + " "
                  + pos.getCharacter()
                  + " context: "
                  + context
                  + " #: "
                  + lci.size());

          // TODO: add completion for attributes
          return Either.forLeft(lci);
        });
  }

  // ctrl+click - goto definition for requires, imports terms inside rules
  public CompletableFuture<
          Either<List<? extends org.eclipse.lsp4j.Location>, List<? extends LocationLink>>>
      definition(DefinitionParams params) {
    findCacheFile();
    KPos pos = new KPos(params.getPosition());
    return CompletableFuture.supplyAsync(
        () -> {
          this.clientLogger.logMessage(
              "Operation '"
                  + "text/definition: "
                  + params.getTextDocument().getUri()
                  + " #pos: "
                  + pos.getLine()
                  + " "
                  + pos.getCharacter());
          List<LocationLink> lls = new ArrayList<>();
          try {
            List<DefinitionItem> dis = files.get(params.getTextDocument().getUri()).dis;
            for (DefinitionItem di : dis) {
              if (di instanceof Require) { // goto required file
                org.kframework.attributes.Location loc = getSafeLoc(di);
                if (isPositionOverLocation(pos, loc)) {
                  Require req = (Require) di;
                  File f = new File(new URI(params.getTextDocument().getUri()));
                  URI targetURI =
                      Path.of(f.getParent(), req.getValue())
                          .toRealPath(LinkOption.NOFOLLOW_LINKS)
                          .toUri();
                  lls.add(
                      new LocationLink(
                          targetURI.toString(),
                          new Range(new Position(0, 0), new Position(10, 0)),
                          new Range(new Position(0, 0), new Position(0, 0)),
                          loc2range(loc)));
                  break;
                }
              } else if (di instanceof Module m) {
                for (ModuleItem mi : m.getItems()) {
                  org.kframework.attributes.Location loc = getSafeLoc(mi);
                  if (isPositionOverLocation(pos, loc)) {
                    if (mi instanceof Import imp) { // goto module definition
                      List<DefinitionItem> allDi = slurp(params.getTextDocument().getUri());
                      allDi.stream()
                          .filter(ddi -> ddi instanceof Module)
                          .map(ddi -> ((Module) ddi))
                          .filter(m2 -> m2.getName().equals(imp.getName()))
                          .forEach(
                              m3 ->
                                  lls.add(
                                      new LocationLink(
                                          URI.create(m3.getSource().source()).toString(),
                                          loc2range(getSafeLoc(m3)),
                                          loc2range(getSafeLoc(m3)),
                                          loc2range(getSafeLoc(imp)))));
                    } else if (mi instanceof StringSentence ss) { // goto syntax of term inside rule
                      String suffix =
                          ss.getType().equals(DefinitionParsing.configuration)
                              ? "-" + RuleGrammarGenerator.CONFIG_CELLS
                              : "-" + RuleGrammarGenerator.RULE_CELLS;
                      Optional<Map.Entry<String, ParseCache>> ch =
                          caches.entrySet().stream()
                              .filter(elm -> elm.getKey().startsWith(m.getName() + suffix))
                              .findFirst();
                      if (ch.isPresent()) {
                        Map<String, ParseCache.ParsedSentence> parsedSent =
                            ch.get().getValue().cache();
                        if (parsedSent.containsKey(ss.getContent())) {
                          Bubble b =
                              new Bubble(
                                  ss.getType(),
                                  ss.getContent(),
                                  ss.getAttributes()
                                      .add(
                                          Att.LOCATION(),
                                          org.kframework.attributes.Location.class,
                                          ss.getLocation())
                                      .add(Att.SOURCE(), Source.class, ss.getSource())
                                      .add(Att.CONTENT_START_LINE(), ss.getContentStartLine())
                                      .add(Att.CONTENT_START_COLUMN(), ss.getContentStartColumn()));
                          ParseCache.ParsedSentence parse =
                              DefinitionParsing.updateLocation(parsedSent.get(ss.getContent()), b);
                          AtomicReference<K> x = new AtomicReference<>();
                          KViz.from(
                                  t -> {
                                    if (isPositionOverLocation(pos, t.location().get()))
                                      x.set(t); // find the deepest term that contains this position
                                    return t;
                                  },
                                  "Find def in rule")
                              .apply(parse.parse());
                          if (x.get() != null
                              && x.get()
                                  .att()
                                  .get(Att.PRODUCTION(), org.kframework.definition.Production.class)
                                  .source()
                                  .isPresent()) {
                            org.kframework.definition.Production prd =
                                x.get()
                                    .att()
                                    .get(
                                        Att.PRODUCTION(),
                                        org.kframework.definition.Production.class);
                            if (prd.source()
                                .isPresent()) // exclude generated productions like casts
                            lls.add(
                                  new LocationLink(
                                      URI.create(prd.source().get().source()).toString(),
                                      loc2range(prd.location().get()),
                                      loc2range(prd.location().get()),
                                      loc2range(
                                          x.get()
                                              .att()
                                              .get(
                                                  Att.LOCATION(),
                                                  org.kframework.attributes.Location.class))));
                          } else
                            clientLogger.logMessage(
                                "definition failed no origin for prod: "
                                    + (x.get() != null
                                        ? x.get()
                                            .att()
                                            .get(
                                                Att.PRODUCTION(),
                                                org.kframework.definition.Production.class)
                                        : null));
                        }
                      } else {
                        kls.languageClient.showMessage(
                            new MessageParams(
                                MessageType.Error,
                                "No caches found for this sentence. 'Go to definition' inside rules"
                                    + " is only available in workspace mode and requires a kompiled"
                                    + " definition."));
                      }
                    }
                    break;
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
    return node.location().orElse(new org.kframework.attributes.Location(0, 0, 0, 0));
  }

  // true if Position(l,c) is over Location(startL, startC, endL, endC). Expects Position to start
  // from 1, just as Location
  public static boolean isPositionOverLocation(KPos pos, org.kframework.attributes.Location loc) {
    return (loc.startLine() < pos.getLine()
            || (loc.startLine() == pos.getLine() && loc.startColumn() <= pos.getCharacter()))
        && (pos.getLine() < loc.endLine()
            || (pos.getLine() == loc.endLine() && pos.getCharacter() <= loc.endColumn()));
  }

  // K starts counting lines and columns from 1 and LSP starts counting from 0
  public static Range loc2range(org.kframework.attributes.Location loc) {
    return new Range(
        new Position(loc.startLine() - 1, loc.startColumn() - 1),
        new Position(loc.endLine() - 1, loc.endColumn() - 1));
  }

  // previous diagnostics task. If it's still active, cancel it and run a newer, updated one
  private final Map<String, CompletableFuture<DocumentDiagnosticReport>> latestDiagnosticScheduled =
      new HashMap<>();

  public CompletableFuture<DocumentDiagnosticReport> diagnostic(DocumentDiagnosticParams params) {
    findCacheFile();
    String uri = params.getTextDocument().getUri();
    if (latestDiagnosticScheduled.containsKey(uri) && !latestDiagnosticScheduled.get(uri).isDone())
      latestDiagnosticScheduled
          .get(uri)
          .completeExceptionally(new Throwable("Cancelled diagnostic publisher"));

    Executor delayedExecutor =
        CompletableFuture.delayedExecutor(
            KTextDocumentService.DELAY_EXECUTION_MS, TimeUnit.MILLISECONDS);
    CompletableFuture<DocumentDiagnosticReport> scheduledFuture =
        CompletableFuture.supplyAsync(
            () -> {
              // make sure the out syntax is up to date
              files.get(params.getTextDocument().getUri()).outerParse();
              List<Diagnostic> problems = files.get(params.getTextDocument().getUri()).problems;
              // for each bubble in the current file
              // search for a cached parsed version and collect reported errors
              files.get(params.getTextDocument().getUri()).dis.stream()
                  .filter(di -> di instanceof Module)
                  .map(di -> (Module) di)
                  .forEach(
                      m ->
                          m.getItems().stream()
                              .filter(mi -> mi instanceof StringSentence)
                              .map(mi -> (StringSentence) mi)
                              .forEach(
                                  ss -> {
                                    String suffix =
                                        ss.getType().equals(DefinitionParsing.configuration)
                                            ? "-" + RuleGrammarGenerator.CONFIG_CELLS
                                            : "-" + RuleGrammarGenerator.RULE_CELLS;
                                    Optional<Map.Entry<String, ParseCache>> ch =
                                        caches.entrySet().stream()
                                            .filter(
                                                elm ->
                                                    elm.getKey().startsWith(m.getName() + suffix))
                                            .findFirst();
                                    if (ch.isPresent()) {
                                      ParseCache parseCache = ch.get().getValue();
                                      Map<String, ParseCache.ParsedSentence> parsedSent =
                                          parseCache.cache();
                                      if (parsedSent.containsKey(ss.getContent())) {
                                        Bubble b =
                                            new Bubble(
                                                ss.getType(),
                                                ss.getContent(),
                                                ss.getAttributes()
                                                    .add(
                                                        Att.LOCATION(),
                                                        org.kframework.attributes.Location.class,
                                                        ss.getLocation())
                                                    .add(Att.SOURCE(), Source.class, ss.getSource())
                                                    .add(
                                                        Att.CONTENT_START_LINE(),
                                                        ss.getContentStartLine())
                                                    .add(
                                                        Att.CONTENT_START_COLUMN(),
                                                        ss.getContentStartColumn()));
                                        ParseCache.ParsedSentence parse =
                                            DefinitionParsing.updateLocation(
                                                parsedSent.get(b.contents()), b);
                                        parse
                                            .errors()
                                            .forEach(
                                                err -> {
                                                  Diagnostic d =
                                                      new Diagnostic(
                                                          loc2range(err.exception.getLocation()),
                                                          err.exception.getMessage(),
                                                          DiagnosticSeverity.Error,
                                                          "Inner Parser");
                                                  problems.add(d);
                                                });
                                        parse
                                            .warnings()
                                            .forEach(
                                                err -> {
                                                  Diagnostic d =
                                                      new Diagnostic(
                                                          loc2range(err.exception.getLocation()),
                                                          err.exception.getMessage(),
                                                          DiagnosticSeverity.Warning,
                                                          "Inner Parser");
                                                  problems.add(d);
                                                });
                                      }
                                    }
                                  }));

              DocumentDiagnosticReport report =
                  new DocumentDiagnosticReport(new RelatedFullDocumentDiagnosticReport(problems));
              this.clientLogger.logMessage(
                  "Operation '"
                      + "text/diagnostics: "
                      + params.getTextDocument().getUri()
                      + " #problems: "
                      + problems.size());
              return report;
            },
            delayedExecutor);
    latestDiagnosticScheduled.put(uri, scheduledFuture);
    return scheduledFuture;
  }

  // find references of modules being used in imports and syntax used in rules
  public CompletableFuture<List<? extends Location>> references(ReferenceParams params) {
    return CompletableFuture.supplyAsync(
        () -> {
          KPos pos = new KPos(params.getPosition());
          List<Location> lloc = new ArrayList<>();

          // look in the current file and find the term under KPos
          List<DefinitionItem> dis = files.get(params.getTextDocument().getUri()).dis;
          for (DefinitionItem di : dis) {
            org.kframework.attributes.Location loc = getSafeLoc(di);
            if (isPositionOverLocation(pos, loc)) {
              Module m = (Module) di;
              // want to activate when over `module NAME` and nothing else but,
              // we don't store the exact position for the module name so try to calculate it
              String name = m.getName();
              org.kframework.attributes.Location nameLoc =
                  new org.kframework.attributes.Location(
                      loc.startLine(),
                      loc.startColumn(),
                      loc.startLine(),
                      loc.startColumn() + "module ".length() + name.length());

              if (isPositionOverLocation(pos, nameLoc)) {
                List<DefinitionItem> allDi =
                    files.values().stream().flatMap(doc -> doc.dis.stream()).toList();
                allDi.stream()
                    .filter(ddi -> ddi instanceof Module)
                    .map(ddi -> ((Module) ddi))
                    .forEach(
                        m3 ->
                            m3.getItems().stream()
                                .filter(mi -> mi instanceof Import)
                                .map(mmi -> (Import) mmi)
                                .filter(i -> i.getName().equals(name))
                                .forEach(
                                    imp ->
                                        lloc.add(
                                            new Location(
                                                URI.create(m3.getSource().source()).toString(),
                                                loc2range(getSafeLoc(imp))))));
              } else {
                // look for syntax references
                AtomicReference<Production> xprd = new AtomicReference<>();
                m.getItems().stream()
                    .filter(a -> a instanceof Syntax)
                    .map(a -> ((Syntax) a))
                    .forEach(
                        b ->
                            b.getPriorityBlocks()
                                .forEach(
                                    c ->
                                        c.getProductions().stream()
                                            .filter(
                                                d -> isPositionOverLocation(pos, d.getLocation()))
                                            .forEach(xprd::set)));
                if (xprd.get() != null) {
                  Production prd = xprd.get();
                  String psource = Path.of(URI.create(prd.source().get().source())).toString();
                  org.kframework.attributes.Location ploc = prd.location().get();

                  if (caches.isEmpty())
                    kls.languageClient.showMessage(
                        new MessageParams(
                            MessageType.Error,
                            "No caches found. 'Find references' for productions is only available"
                                + " in workspace mode and requires a kompiled definition."));

                  // caches remember previous versions for quick access, so we may find more
                  // instances than there actually exist in the source file
                  // 1. for each cached sentence
                  // 2. find if it still exists in the source file and get its updated location
                  caches.forEach(
                      (mname, parseCache) -> {
                        String uri =
                            Path.of(
                                    parseCache
                                        .module()
                                        .att()
                                        .get(Att.SOURCE(), org.kframework.attributes.Source.class)
                                        .source())
                                .toUri()
                                .toString();
                        files.get(uri).dis.stream()
                            .filter(di2 -> di2 instanceof Module)
                            .map(di2 -> (Module) di2)
                            .filter(mm -> mname.startsWith((mm.getName())))
                            .forEach(
                                mm ->
                                    mm.getItems().stream()
                                        .filter(mi -> mi instanceof StringSentence)
                                        .map(mi -> (StringSentence) mi)
                                        .forEach(
                                            ss -> {
                                              if (parseCache.cache().containsKey(ss.getContent())) {
                                                ParseCache.ParsedSentence ps =
                                                    parseCache.cache().get(ss.getContent());
                                                if (ps.parse() != null) {
                                                  Bubble b =
                                                      new Bubble(
                                                          ss.getType(),
                                                          ss.getContent(),
                                                          ss.getAttributes()
                                                              .add(
                                                                  Att.LOCATION(),
                                                                  org.kframework.attributes.Location
                                                                      .class,
                                                                  ss.getLocation())
                                                              .add(
                                                                  Att.SOURCE(),
                                                                  Source.class,
                                                                  ss.getSource())
                                                              .add(
                                                                  Att.CONTENT_START_LINE(),
                                                                  ss.getContentStartLine())
                                                              .add(
                                                                  Att.CONTENT_START_COLUMN(),
                                                                  ss.getContentStartColumn()));
                                                  ps = DefinitionParsing.updateLocation(ps, b);
                                                  KViz.from(
                                                          t -> {
                                                            // the two production elements are not
                                                            // compatible so compare location
                                                            // information which should match
                                                            // if the definition wasn't modified
                                                            org.kframework.definition.Production
                                                                dprd =
                                                                    t.att()
                                                                        .get(
                                                                            Att.PRODUCTION(),
                                                                            org.kframework
                                                                                .definition
                                                                                .Production.class);
                                                            if (dprd.location().isPresent()
                                                                && dprd.location()
                                                                    .get()
                                                                    .equals(ploc)
                                                                && dprd.source().isPresent()
                                                                && dprd.source()
                                                                    .get()
                                                                    .source()
                                                                    .equals(psource)) {
                                                              lloc.add(
                                                                  new Location(
                                                                      URI.create(
                                                                              t.source()
                                                                                  .get()
                                                                                  .source())
                                                                          .toString(),
                                                                      loc2range(
                                                                          t.location().get())));
                                                            }
                                                            return t;
                                                          },
                                                          "Find ref in rule")
                                                      .apply(ps.parse());
                                                }
                                              }
                                            }));
                      });
                }
              }
              break;
            }
          }
          // TODO: check why sometimes this message is duplicated
          clientLogger.logMessage(
              "Operation '"
                  + "text/references: "
                  + params.getTextDocument().getUri()
                  + " #pos: "
                  + pos.getLine()
                  + " "
                  + pos.getCharacter()
                  + " found: "
                  + lloc.size());

          return lloc;
        });
  }

  // Return the selection tree for a given position. This follows the AST as much as we have
  // location information.
  // The SelectionRange object is a recursive structure where the head is the smallest AST node next
  // to the cursor
  // and the deepest element is the entire file, the root of the document.
  public CompletableFuture<List<SelectionRange>> selectionRange(SelectionRangeParams params) {
    return CompletableFuture.supplyAsync(
        () -> {
          List<SelectionRange> lloc = new ArrayList<>();

          KTextDocument txtDoc = files.get(params.getTextDocument().getUri());
          List<DefinitionItem> dis = txtDoc.dis;
          txtDoc.getContextAt(new KPos(1, 1)); // warmup to avoid NPE
          SelectionRange topsr =
              new SelectionRange(
                  new Range(
                      new Position(0, 0),
                      new Position(
                          txtDoc.lines[txtDoc.content.length()],
                          txtDoc.columns[txtDoc.content.length()])),
                  null);
          for (Position ppos : params.getPositions()) {
            KPos pos = new KPos(ppos);
            for (DefinitionItem di : dis) {
              if (isPositionOverLocation(pos, getSafeLoc(di))) {
                if (di instanceof Module m) {
                  SelectionRange msr = new SelectionRange(loc2range(m.getLocation()), topsr);
                  for (ModuleItem mi : m.getItems()) {
                    if (isPositionOverLocation(pos, getSafeLoc(mi))) {
                      SelectionRange sentsr = new SelectionRange(loc2range(getSafeLoc(mi)), msr);
                      if (mi instanceof Syntax stx) {
                        for (PriorityBlock pb : stx.getPriorityBlocks()) {
                          SelectionRange pbsr =
                              new SelectionRange(loc2range(getSafeLoc(pb)), sentsr);
                          for (Production prd : pb.getProductions())
                            if (isPositionOverLocation(pos, getSafeLoc(prd)))
                              lloc.add(new SelectionRange(loc2range(getSafeLoc(prd)), pbsr));
                        }
                      } else if (mi
                          instanceof
                          StringSentence
                          ss) { // if we have caches, find the deepest term
                        String suffix =
                            ss.getType().equals(DefinitionParsing.configuration)
                                ? "-" + RuleGrammarGenerator.CONFIG_CELLS
                                : "-" + RuleGrammarGenerator.RULE_CELLS;
                        Optional<Map.Entry<String, ParseCache>> ch =
                            caches.entrySet().stream()
                                .filter(elm -> elm.getKey().startsWith(m.getName() + suffix))
                                .findFirst();
                        AtomicReference<SelectionRange> x = new AtomicReference<>(sentsr);
                        if (ch.isPresent()) {
                          Map<String, ParseCache.ParsedSentence> parsedSent =
                              ch.get().getValue().cache();
                          if (parsedSent.containsKey(ss.getContent())) {
                            Bubble b =
                                new Bubble(
                                    ss.getType(),
                                    ss.getContent(),
                                    ss.getAttributes()
                                        .add(
                                            Att.LOCATION(),
                                            org.kframework.attributes.Location.class,
                                            ss.getLocation())
                                        .add(Att.SOURCE(), Source.class, ss.getSource())
                                        .add(Att.CONTENT_START_LINE(), ss.getContentStartLine())
                                        .add(
                                            Att.CONTENT_START_COLUMN(),
                                            ss.getContentStartColumn()));
                            ParseCache.ParsedSentence parse =
                                DefinitionParsing.updateLocation(
                                    parsedSent.get(ss.getContent()), b);
                            KViz.from(
                                    t -> {
                                      if (isPositionOverLocation(pos, t.location().get())) {
                                        SelectionRange tsr =
                                            new SelectionRange(
                                                loc2range(t.location().get()), x.get());
                                        x.set(tsr); // find the deepest term that contains this
                                        // position
                                      }
                                      return t;
                                    },
                                    "Find selectionRange in rule")
                                .apply(parse.parse());
                          }
                        }
                        lloc.add(x.get());
                      } else { // anything else that doesn't have a complex structure: Import,
                        // SyntaxPriorities...
                        lloc.add(new SelectionRange(loc2range(getSafeLoc(mi)), msr));
                      }
                    }
                  }
                } else {
                  lloc.add(new SelectionRange(loc2range(di.getLocation()), topsr));
                }
              }
            }
          }

          String poss =
              params.getPositions().stream()
                  .map(pos -> new KPos(pos).toString())
                  .collect(Collectors.joining(" "));
          clientLogger.logMessage(
              "Operation '"
                  + "text/selectionRange: "
                  + params.getTextDocument().getUri()
                  + " #poss: "
                  + poss
                  + " rezDepth: "
                  + lloc.stream().map(TextDocumentSyncHandler::getSelectionRangeDepth).toList());

          return lloc;
        });
  }

  // for debug purposes, return the depth of the selection range
  private static int getSelectionRangeDepth(SelectionRange sr) {
    if (sr == null) return 0;
    return 1 + getSelectionRangeDepth(sr.getParent());
  }
}
