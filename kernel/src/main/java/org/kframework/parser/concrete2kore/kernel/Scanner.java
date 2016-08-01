package org.kframework.parser.concrete2kore.kernel;

import org.apache.commons.io.FileUtils;
import org.apache.commons.io.IOUtils;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.Terminal;
import org.kframework.definition.TerminalLike;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.ParseFailedException;
import scala.Tuple2;

import java.io.File;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;

/**
 * Created by dwightguth on 7/21/16.
 */
public class Scanner implements AutoCloseable {

    private final Map<TerminalLike, Tuple2<Integer, Integer>> tokens;
    private final File scanner;

    public Scanner(Module parsingModule) {
        tokens = KSyntax2GrammarStatesFilter.getTokens(parsingModule);
        scanner = getScanner();
    }

    // debugging method
    private TerminalLike getTokenByKind(int kind) {
        return tokens.entrySet().stream().filter(e -> e.getValue()._1() == kind).findAny().get().getKey();
    }

    static final String multiLine = "(\\/\\*([^\\*]|(\\*+([^\\*\\/])))*\\*+\\/)";
    static final String singleLine = "(\\/\\/[^\\n\\r]*)";
    static final String whites = "([\\ \\n\\r\\t])";

    public File getScanner() {
        File scanner;
        // tokenization
        try {
            File scannerSource = File.createTempFile("tmp-kompile-", ".l");
            scannerSource.deleteOnExit();
            StringBuilder flex = new StringBuilder();
            flex.append("%{\n" +
                    "#include<stdio.h>\n" +
                    "#include<stddef.h>\n" +
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
                    "%}\n" +
                    "%%\n" +
                    "("+ multiLine +"|"+ singleLine +"|"+ whites +")" + " ;\n");
            List<TerminalLike> ordered = tokens.keySet().stream().sorted((t1, t2) -> tokens.get(t2)._2() - tokens.get(t1)._2()).collect(Collectors.toList());
            for (TerminalLike key : ordered) {
                if (key instanceof Terminal) {
                    Terminal t = (Terminal) key;
                    flex.append(StringUtil.enquoteCString(t.value()));
                } else {
                    RegexTerminal t = (RegexTerminal) key;
                    flex.append(t.regex());
                }
                writeAction(flex, key);
            }
            flex.append("%%\n" +
                    "int main(int argc, char **argv) {\n" +
                    "  freopen(NULL, \"rb\", stdin);\n" +
                    "  freopen(NULL, \"wb\", stdout);\n" +
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
            ProcessBuilder pb = new ProcessBuilder("flex", "-Ca", "-o", scannerCSource.getAbsolutePath(), scannerSource.getAbsolutePath()).inheritIO();
            int exit = pb.start().waitFor();
            if (exit != 0) {
                throw KEMException.internalError("Flex returned nonzero exit code. See output for details.");
            }
            scanner = File.createTempFile("tmp-kompile-", "");
            scanner.deleteOnExit();
            pb = new ProcessBuilder("gcc", scannerCSource.getAbsolutePath(), "-o", scanner.getAbsolutePath(), "-lfl");
            exit = pb.start().waitFor();
            scanner.setExecutable(true);
            if (exit != 0) {
                throw KEMException.internalError("gcc returned nonzero exit code. See output for details.");
            }
        } catch (IOException | InterruptedException e) {
            throw KEMException.internalError("Failed to write file for scanner", e);
        }
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
        for (Process p : pool) {
            p.destroy();
        }
    }

    AtomicInteger sizeofPool = new AtomicInteger(0);

    static int N_CPUS = Runtime.getRuntime().availableProcessors();

    private ArrayBlockingQueue<Process> pool = new ArrayBlockingQueue<>(N_CPUS);

    public Token[] tokenize(String input, Source source, int[] lines, int[] columns) {
        try {
            Process process;
            if (sizeofPool.getAndUpdate(i -> i < N_CPUS ? i + 1 : i) < N_CPUS) {
                process = new ProcessBuilder(scanner.getAbsolutePath()).start();
            } else {
                process = pool.take();
            }
            byte[] buf = input.getBytes("UTF-8");
            ByteBuffer size = ByteBuffer.allocate(4);
            size.order(ByteOrder.nativeOrder());
            size.putInt(buf.length + 1);
            process.getOutputStream().write(size.array());
            process.getOutputStream().write(buf);
            process.getOutputStream().write('\n');
            process.getOutputStream().flush();
            return readTokenizedOutput(process, source, lines, columns);
        } catch (IOException | InterruptedException e) {
            throw KEMException.internalError("Failed to invoke scanner", e);
        }
    }

    private Token[] readTokenizedOutput(Process process, Source source, int[] lines, int[] columns) throws IOException {
        List<Token> result = new ArrayList<>();
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
                // we aren't returning this process to the pool since it still has some input tokens in it left,
                // so we have to clean up here and then make sure that the pool knows it can allocate a new process.
                process.destroy();
                sizeofPool.decrementAndGet();
                throw new ParseFailedException(new KException(
                        KException.ExceptionType.ERROR, KException.KExceptionGroup.INNER_PARSER, msg, source, loc));
            }
            result.add(t);
        }
        pool.add(process);
        return result.toArray(new Token[result.size()]);
    }

}
