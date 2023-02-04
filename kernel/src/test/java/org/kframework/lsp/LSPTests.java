package org.kframework.lsp;

import org.eclipse.lsp4j.*;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.junit.Assert;
import org.junit.Test;
import org.kframework.attributes.Location;
import org.kframework.kil.DefinitionItem;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.inner.ParseCache;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.stream.Collectors;

public class LSPTests {

    String def = "//require \"Copy (10) test.k\"\n" +
            "require \"spec.k\"\n" +
            "\n" +
            "module A\n" +
            "  syntax A ::= \"a\"\n" +
            "endmodule\n" +
            "\n" +
            "module B\n" +
            "  imports private  A\n" +
            "\n" +
            "  syntax C ::= B \n" +
            "             | A\n" +
            "  syntax B ::= \"b\"\n" +
            "\n" +
            "  // this is the ffunction function\n" +
            "  syntax B ::= affunction(C)  [function, total]\n" +
            "\n" +
            "endmodule\n" +
            "\n" +
            "module TEST \n" +
            "  imports private B \n" +
            "  imports INT \n" +
            "\n" +
            "  rule  .asdfasdf adsf  asdf  123454 \n" +
            "//  rule f(_) => \"a\" [owise] \n" +
            "endmodule\n";
    String uri = LSPTests.class.toString();

    @Test
    public void testGetContext() {
        KTextDocument doc = new KTextDocument();
        doc.updateText(def);
        Assert.assertEquals("require", doc.getContextAt(new KPos(2, 2)));
        Assert.assertEquals("module", doc.getContextAt(new KPos(4, 8)));
        Assert.assertEquals("imports", doc.getContextAt(new KPos(9, 21)));
        Assert.assertEquals("syntax", doc.getContextAt(new KPos(11, 18)));
        Assert.assertEquals("endmodule", doc.getContextAt(new KPos(19, 1)));
        Assert.assertEquals("rule", doc.getContextAt(new KPos(24, 30)));
    }

    @Test
    public void isPositionOverLocation() {
        Assert.assertTrue(TextDocumentSyncHandler.isPositionOverLocation(
                new KPos(9, 3),
                new Location(9, 3, 12, 17)));
        Assert.assertTrue(TextDocumentSyncHandler.isPositionOverLocation(
                new KPos(10, 16),
                new Location(9, 3, 12, 17)));
        Assert.assertFalse(TextDocumentSyncHandler.isPositionOverLocation(
                new KPos(9, 2),
                new Location(9, 3, 12, 17)));
        Assert.assertFalse(TextDocumentSyncHandler.isPositionOverLocation(
                new KPos(12, 18),
                new Location(9, 3, 12, 17)));
    }

    @Test
    public void testKLS() throws ExecutionException, InterruptedException {
        KLanguageServer kls = new KLanguageServer();
        KTextDocumentService.DELAY_EXECUTION_MS = 0;
        kls.getTextDocumentService().didOpen(new DidOpenTextDocumentParams(new TextDocumentItem(uri, "kframework", 1, def)));

        CompletableFuture<DocumentDiagnosticReport> diags = kls.getTextDocumentService().diagnostic(new DocumentDiagnosticParams(new TextDocumentIdentifier(uri)));
        RelatedFullDocumentDiagnosticReport z = diags.get().getLeft();
        Assert.assertEquals(0, z.getItems().size());
        //System.out.println("Diags: " + z);

        CompletableFuture<Either<List<CompletionItem>, CompletionList>> x = kls.getTextDocumentService().completion(new CompletionParams(new TextDocumentIdentifier(uri), new Position(10, 17)));
        List<CompletionItem> y = x.get().getLeft();
        Assert.assertNotEquals(y.size(), 0);
        //System.out.println("Completion: " + y.size());

        CompletableFuture<Either<List<? extends org.eclipse.lsp4j.Location>, List<? extends LocationLink>>> defin = kls.getTextDocumentService().definition(new DefinitionParams(new TextDocumentIdentifier(uri), new Position(21, 6)));
        List<? extends LocationLink> defRez = defin.get().getRight();
        Assert.assertNotEquals(defRez.size(), 0);
        //System.out.println("GoToDef: " + defRez);
    }

    @Test
    public void testKLSPath() throws IOException {
        Path workspaceFolder = Path.of("/home/radu/work/test");
        BinaryLoader loader = new BinaryLoader(new KExceptionManager(new GlobalOptions()));
        Map<String, ParseCache> caches = null;

        Optional<Path> cacheFile = Files.walk(workspaceFolder).filter(p -> p.endsWith("cache.bin")).findFirst();
        if (cacheFile.isPresent())
            caches = loader.loadCache(Map.class, cacheFile.get().toFile());

        System.out.println(caches);
    }
}
