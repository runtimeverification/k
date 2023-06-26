// Copyright (c) K Team. All Rights Reserved.
package org.kframework.parser.inner.kernel;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ListMultimap;
import org.apache.commons.io.FileUtils;
import org.apache.commons.io.IOUtils;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.SyntaxLexical;
import org.kframework.definition.Terminal;
import org.kframework.definition.TerminalLike;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.inner.ParseInModule;
import org.kframework.utils.OS;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import scala.Tuple2;

import java.io.File;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.file.StandardCopyOption;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.Semaphore;
import java.util.function.BiConsumer;
import java.util.stream.Collectors;

import static org.kframework.kore.KORE.*;
import static org.kframework.Collections.*;

/**
 * Created by dwightguth on 7/21/16.
 */
public class Scanner implements AutoCloseable {

    private final Map<TerminalLike, Tuple2<Integer, Integer>> tokens;
    private final File scanner;
    private final Module module;
    private GlobalOptions go = new GlobalOptions();

    public static final String COMPILER = OS.current().equals(OS.OSX) ? "clang" : "gcc";

    public static Map<TerminalLike, Tuple2<Integer, Integer>> getTokens(Module module) {
        Map<TerminalLike, Integer> tokens = new TreeMap<>();
        Set<String> terminals = new HashSet<>();
        for (Production p : iterable(module.productions())) {
            for (ProductionItem pi : iterable(p.items())) {
                if (pi instanceof TerminalLike) {
                    TerminalLike lx = (TerminalLike) pi;
                    if (tokens.containsKey(lx)) {
                        int prec;
                        if (p.att().contains(Att.PREC())) {
                            prec = Integer.valueOf(p.att().getOptional(Att.PREC()).get());
                        } else if (lx instanceof Terminal) {
                            prec = Integer.MAX_VALUE;
                        } else {
                            prec = 0;
                        }
                        if (prec != tokens.get(lx)) {
                            throw KEMException.compilerError("Inconsistent token precedence detected.", p);
                        }
                    } else if (lx instanceof Terminal && terminals.contains(((Terminal) lx).value())) {
                        tokens.put(lx, Integer.MAX_VALUE);
                    } else {
                        if (lx instanceof Terminal) {
                            terminals.add(((Terminal) lx).value());
                            tokens.put(lx, Integer.MAX_VALUE);
                        } else {
                            int prec;
                            if (p.att().contains(Att.PREC())) {
                                prec = Integer.valueOf(p.att().getOptional(Att.PREC()).get());
                            } else {
                                prec = 0;
                            }
                            tokens.put(lx, prec);
                        }
                    }
                }
            }
        }

        Map<TerminalLike, Tuple2<Integer, Integer>> finalTokens = new HashMap<>();
        // token 0 is EOF, so start at index 1
        int idx = 1;
        for (TerminalLike t : tokens.keySet()) {
            finalTokens.put(t, Tuple2.apply(idx++, tokens.get(t)));
        }

        return finalTokens;
    }


    public Scanner(ParseInModule module, GlobalOptions go) {
        this.go = go;
        this.tokens  = getTokens(module.getParsingModule());
        this.module  = module.seedModule();
        this.scanner = getScanner();
    }

    public Scanner(ParseInModule module) {
        this.tokens  = getTokens(module.getParsingModule());
        this.module  = module.seedModule();
        this.scanner = getScanner();
    }

    public Scanner(ParseInModule module, GlobalOptions go, File scanner) {
        this.go = go;
        this.tokens  = getTokens(module.getParsingModule());
        this.module  = module.seedModule();
        this.scanner = scanner;
    }

    public void serialize(File output) {
        try {
            Files.copy(scanner.toPath(), output.toPath(), StandardCopyOption.REPLACE_EXISTING);
        } catch (IOException e) {
            throw KEMException.criticalError("Could not write to " + output, e);
        }
    }

    public Module getModule() {
        return module;
    }

    public Set<Integer> kinds() {
        return tokens.values().stream().map(v -> v._1()).collect(Collectors.toSet());
    }

    // debugging method
    public TerminalLike getTokenByKind(int kind) {
        return tokens.entrySet().stream().filter(e -> e.getValue()._1() == kind).findAny().get().getKey();
    }

    public void appendScanner(StringBuilder flex, BiConsumer<StringBuilder, TerminalLike> writeAction) {
        if (this.module.allSorts().contains(Sorts.Layout())) {
            flex.append(this.module.layout() + " ;\n");
        }
        List<TerminalLike> ordered = tokens.keySet().stream().sorted((t1, t2) -> tokens.get(t2)._2() - tokens.get(t1)._2()).collect(Collectors.toList());
        for (TerminalLike key : ordered) {
            if (key instanceof Terminal) {
                Terminal t = (Terminal) key;
                flex.append(StringUtil.enquoteCString(t.value()));
            } else {
                RegexTerminal t = (RegexTerminal) key;
                flex.append(t.regex());
            }
            writeAction.accept(flex, key);
        }
    }

    public void writeStandaloneScanner(File path) {
        StringBuilder flex  = new StringBuilder();
        flex.append("%{\n" +
            "#include \"node.h\"\n" +
            "#include \"parser.tab.h\"\n" +
            "char *filename;\n" +
            "#define YY_USER_ACTION yylloc->first_line = yylloc->last_line = yylineno; \\\n" +
            "    yylloc->first_column = yycolumn; yylloc->last_column = yycolumn + yyleng - 1; \\\n" +
            "   yycolumn += yyleng; \\\n" +
            "   yylloc->filename = filename;\n" +
            "#define ECHO do {\\\n" +
            "  fprintf (stderr, \"%d:%d:%d:%d:syntax error: unexpected %s\\n\", yylloc->first_line, yylloc->first_column, yylloc->last_line, yylloc->last_column, yytext);\\\n" +
            "  exit(1);\\\n" +
            "} while (0)\n" +
            "void line_marker(char *, void *);\n" +
            "%}\n\n" +
            "%option reentrant bison-bridge\n" +
            "%option bison-locations\n" +
            "%option noyywrap\n" +
            "%option yylineno\n");
        for (SyntaxLexical ident : iterable(module.lexicalIdentifiers())) {
          flex.append(ident.name());
          flex.append(" ");
          flex.append(ident.regex());
          flex.append("\n");
        }
        flex.append("%%\n\n");
        if (module.productionsForSort().contains(Sorts.LineMarker().head())) {
          stream(module.productionsForSort().apply(Sorts.LineMarker().head())).forEach(prod -> {
            if (prod.items().size() != 1 || !(prod.items().apply(0) instanceof RegexTerminal)) {
              throw KEMException.compilerError("Productions of sort `#LineMarker` must be exactly one `RegexTerminal`.", prod);
            }
            RegexTerminal terminal = (RegexTerminal)prod.items().apply(0);
            String regex = terminal.regex();
            flex.append(regex).append(" line_marker(yytext, yyscanner);\n");
          });
        }
        appendScanner(flex, this::writeStandaloneAction);
        try {
            FileUtils.write(path, flex);
        } catch (IOException e) {
            throw KEMException.internalError("Failed to write file for scanner", e);
        }
    }

    public File getScanner() {
        Stopwatch sw = new Stopwatch(go);
        File scanner;
        // tokenization
        try {
            File scannerSource = File.createTempFile("tmp-kompile-", ".l");
            scannerSource.deleteOnExit();
            StringBuilder flex = new StringBuilder();
            flex.append("%{\n" +
                    "#include<stdio.h>\n" +
                    "#include<stddef.h>\n" +
                    "#include <fcntl.h>\n" +
                    "#define ECHO do " +
                    " {" +
                    "   long long start_pos = yytext - buffer;" +
                    "   long long end_pos = start_pos + yyleng;" +
                    "   fwrite(&start_pos, sizeof(start_pos), 1, stdout);" +
                    "   fwrite(&end_pos, sizeof(end_pos), 1, stdout);" +
                    "   int kind = -1;" +
                    "   fwrite(&kind, sizeof(kind), 1, stdout);" +
                    "   int len = strlen(yytext);" +
                    "   fwrite(&len, sizeof(len), 1, stdout);" +
                    "   fwrite(yytext, 1, len, stdout);" +
                    " } while (0) \n" +
                    "char *buffer;\n" +
                    "%}\n\n");
            for (SyntaxLexical ident : iterable(module.lexicalIdentifiers())) {
              flex.append(ident.name());
              flex.append(" ");
              flex.append(ident.regex());
              flex.append("\n");
            }
            flex.append("%%\n\n");
            appendScanner(flex, this::writeAction);
            //WIN32 fix for line terminator issue: https://sourceforge.net/p/mingw/mailman/message/11374534/
            flex.append("\n\n%%\n\n" +
                    "int main(int argc, char **argv) {\n" +
                    "  freopen(NULL, \"rb\", stdin);\n" +
                    "  freopen(NULL, \"wb\", stdout);\n" +
                    "# ifdef WIN32\n" +
                    "    if ( -1 == _setmode( _fileno( stdout ), _O_BINARY ) ) {\n" +
                    "        perror ( \"generated scanner: Cannot set BINARY mode for stdout\" );\n" +
                    "        exit(1);\n" +
                    "    }\n" +
                    "    if ( -1 == _setmode( _fileno( stdin ), _O_BINARY ) ) {\n" +
                    "        perror ( \"generated scanner: Cannot set BINARY mode for stdin\" );\n" +
                    "        exit(1);\n" +
                    "    }\n" +
                    "# endif  /* WIN32 */\n" +
                    "\n" +
                    "  while(1) {\n" +
                    "    int length;\n" +
                    "    size_t nread = fread(&length, sizeof(length), 1, stdin);\n" +
                    "    if (nread < 1) exit(0);\n" +
                    "    buffer = malloc(length + 2);\n" +
                    "    buffer[length] = 0;\n" +
                    "    buffer[length+1] = 0;\n" +
                    "    fread(buffer, length, 1, stdin);\n" +
                    "    YY_BUFFER_STATE bs = yy_scan_buffer(buffer, length + 2);\n" +
                    "    yy_switch_to_buffer(bs);\n" +
                    "    yylex();\n" +
                    "    long long exit = -1;\n" +
                    "    fwrite(&exit, sizeof(exit), 1, stdout);\n" +
                    "    fwrite(&exit, sizeof(exit), 1, stdout);\n" +
                    "    fwrite(&exit, sizeof(exit), 1, stdout);\n" +
                    "    fflush(stdout);\n" +
                    "  }\n" +
                    "}");
            FileUtils.write(scannerSource, flex);
            File scannerCSource = File.createTempFile("tmp-kompile-", ".c");
            scannerCSource.deleteOnExit();
            ProcessBuilder pb = new ProcessBuilder("flex", "--nowarn", "--noyywrap", "-Ca", "-o",
                    scannerCSource.getAbsolutePath(), scannerSource.getAbsolutePath());
            pb.inheritIO();
            int exit = pb.start().waitFor();
            if (exit != 0) {
                System.err.println(pb.command());
                throw KEMException.internalError(
                        "Flex returned nonzero exit code. See output for details. flex command: " + pb.command());
            }
            scanner = File.createTempFile("tmp-kompile-", "");
            scanner.deleteOnExit();
            //Option -lfl unnecessary. Same effect achieved by --noyywrap above.
            pb = new ProcessBuilder(COMPILER, scannerCSource.getAbsolutePath(), "-o", scanner.getAbsolutePath(), "-Wno-unused-result");
            pb.inheritIO();
            exit = pb.start().waitFor();
            scanner.setExecutable(true);
            if (exit != 0) {
                throw KEMException.internalError(
                        COMPILER + " returned nonzero exit code. See output for details. " + COMPILER + " command: " + pb.command());
            }
        } catch (IOException | InterruptedException e) {
            throw KEMException.internalError("Failed to write file for scanner", e);
        }
        sw.printIntermediate("  New scanner: " + module.name());
        return scanner;
    }

    private void writeAction(StringBuilder flex, TerminalLike key) {
        flex.append(" {\n" +
                "   long long start_pos = yytext - buffer;\n" +
                "   long long end_pos = start_pos + yyleng;\n" +
                "   fwrite(&start_pos, sizeof(start_pos), 1, stdout);\n" +
                "   fwrite(&end_pos, sizeof(end_pos), 1, stdout);\n" +
                "   int kind = ").append(tokens.get(key)._1()).append(";\n" +
                "   fwrite(&kind, sizeof(kind), 1, stdout);\n" +
                "   int len = strlen(yytext);\n" +
                "   fwrite(&len, sizeof(len), 1, stdout);\n" +
                "   fwrite(yytext, 1, len, stdout);\n" +
                " }\n");
    }

    private void writeStandaloneAction(StringBuilder flex, TerminalLike key) {
        flex.append(" {\n" +
            "  int kind = ").append(tokens.get(key)._1()+1).append(";\n" +
            "  *((char **)yylval) = malloc(strlen(yytext) + 1);\n" +
            "  strcpy(*((char **)yylval), yytext);\n" +
            "  return kind;\n" +
            " }\n");
    }

    private int maxToken = -1;

    public int getMaxToken() {
        int max = maxToken;
        if (max == -1) {
            for (Tuple2<Integer, Integer> val : tokens.values()) {
                max = Integer.max(max, val._1());
            }
            maxToken = max;
        }
        return max;
    }

    public int resolve(TerminalLike terminal) {
        return tokens.get(terminal)._1();
    }

    public static class Token {
        final int kind;
        final String value;
        final int startLoc;
        final int endLoc;

        public Token(int kind, String value, long startLoc, long endLoc) {
            this.kind = kind;
            this.value = value;
            assert startLoc < Integer.MAX_VALUE;
            assert endLoc < Integer.MAX_VALUE;
            this.startLoc = (int)startLoc;
            this.endLoc = (int)endLoc;
        }

        @Override
        public String toString() {
            return kind + ":" + value;
        }
    }

    @Override
    public void close() {
        synchronized(idleProcesses) {
            for (Process p : idleProcesses.get(this)) {
                p.destroy();
                cache.remove(p);
                activeProcceses--;
            }
            idleProcesses.removeAll(this);
        }
    }

    private static final int N_CPUS = Runtime.getRuntime().availableProcessors();
    private static final int N_PROCS = 512;
    private static int activeProcceses = 0;
    private static final Semaphore runningScanners = new Semaphore(N_PROCS);
    private static final ListMultimap<Scanner, Process> idleProcesses = ArrayListMultimap.create();
    private static final Map<Process, Scanner> cache = new LinkedHashMap<Process, Scanner>() {
        @Override
        protected boolean removeEldestEntry(Map.Entry<Process, Scanner> entry) {
            if (activeProcceses > N_PROCS) {
                entry.getKey().destroy();
                idleProcesses.get(entry.getValue()).remove(entry.getKey());
                activeProcceses--;
                return true;
            }
            return false;
        }
    };

    public Token[] tokenize(String input, Source source, int[] lines, int[] columns) {
        try {
            runningScanners.acquire();

            Process process;
            synchronized (idleProcesses) {
                if (idleProcesses.get(this).size() > 0) {
                    List<Process> idleForThisScanner = idleProcesses.get(this);
                    process = idleForThisScanner.remove(idleForThisScanner.size() - 1);
                    cache.remove(process);
                } else {
                    process = new ProcessBuilder(scanner.getAbsolutePath()).start();
                    activeProcceses++;
                    // temporarily add it so that LinkedHashMap evicts the old entry
                    cache.put(process, this);
                    cache.remove(process);
                }
            }

            byte[] buf = input.getBytes("UTF-8");
            ByteBuffer size = ByteBuffer.allocate(4);
            size.order(ByteOrder.nativeOrder());
            size.putInt(buf.length);
            process.getOutputStream().write(size.array());
            process.getOutputStream().write(buf);
            process.getOutputStream().flush();
            return readTokenizedOutput(process, source, lines, columns, input.length());
        } catch (IOException | InterruptedException e) {
            throw KEMException.internalError("Failed to invoke scanner", e);
        } finally {
            runningScanners.release();
        }
    }

    private Token[] readTokenizedOutput(Process process, Source source, int[] lines, int[] columns, int length) throws IOException {
        List<Token> result = new ArrayList<>();
        boolean success = false;
        try {
            while (true) {
                byte[] buf = new byte[24];
                IOUtils.readFully(process.getInputStream(), buf);
                ByteBuffer byteBuf = ByteBuffer.wrap(buf);
                byteBuf.order(ByteOrder.nativeOrder());
                long startLoc = byteBuf.getLong();
                if (startLoc < 0) {
                    break;
                }
                long endLoc = byteBuf.getLong();
                int kind = byteBuf.getInt();
                int len = byteBuf.getInt();
                byte[] bytes = new byte[len];
                IOUtils.readFully(process.getInputStream(), bytes);
                String value = new String(bytes, "UTF-8");
                Token t = new Token(kind, value, startLoc, endLoc);
                if (kind == -1) {
                    String msg = "Scanner error: unexpected character sequence '" + value + "'.";
                    Location loc = new Location(lines[t.startLoc], columns[t.startLoc],
                            lines[t.endLoc], columns[t.endLoc]);
                    throw KEMException.innerParserError(msg, source, loc);
                }
                result.add(t);
            }
            success = true;
            // add EOF token at end of token sequence
            result.add(new Token(0, "", length, length));
            return result.toArray(new Token[result.size()]);
        } finally {
            if (success) {
                synchronized (idleProcesses) {
                    cache.put(process, this);
                    idleProcesses.put(this, process);
                }
            } else {
                // we aren't returning this process to the pool since something went wrong with it,
                // so we have to clean up here and then make sure that the pool knows it can allocate a new process.
                synchronized (idleProcesses) {
                    process.destroy();
                    activeProcceses--;
                }
            }
        }
    }

}
