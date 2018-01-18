package org.kframework.unparser;

import org.kframework.definition.NonTerminal;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Terminal;
import org.kframework.parser.Constant;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KEMException;

import static org.kframework.Collections.*;

public class Formatter {

    public static String format(Term term) {
        Indenter indenter = new Indenter(2);
        format(term, indenter);
        return indenter.toString();
    }

    public static void format(Term term, Indenter indenter) {
        int indent = 0;
        if (term instanceof Constant) {
            indenter.append(((Constant) term).value());
        } else if (term instanceof TermCons) {
            TermCons tc = (TermCons) term;
            String format = tc.production().att().getOptional("format").orElse(defaultFormat(tc.production().items().size()));
            for (int i = 0; i < format.length(); i++) {
                char c = format.charAt(i);
                if (c == '%') {
                    char c2 = format.charAt(i + 1);
                    i++;
                    switch(c2) {
                    case 'n':
                        indenter.newline();
                        break;
                    case 'i':
                        indenter.indent();
                        indent++;
                        break;
                    case 'd':
                        indenter.dedent();
                        indent--;
                        break;
                    case '0':
                    case '1':
                    case '2':
                    case '3':
                    case '4':
                    case '5':
                    case '6':
                    case '7':
                    case '8':
                    case '9':
                        StringBuilder sb = new StringBuilder();
                        for(; i < format.length() && format.charAt(i) >= '0' && format.charAt(i) <= '9';i++) {
                            sb.append(format.charAt(i));
                        }
                        i--;
                        int idx = Integer.parseInt(sb.toString());
                        if (idx == 0 || idx > tc.production().items().size()) {
                            throw KEMException.compilerError("Invalid format attribute; index must be in range 1-N for a production with N items.", tc.production());
                        }
                        ProductionItem item = tc.production().items().apply(idx - 1);
                        if (item instanceof Terminal) {
                            indenter.append(((Terminal) item).value());
                        } else if (item instanceof NonTerminal) {
                            int nt = 0;
                            for (ProductionItem pi : iterable(tc.production().items())) {
                                if (pi instanceof NonTerminal) {
                                    if (pi == item) {
                                        break;
                                    }
                                    nt++;
                                }
                            }
                            assert tc.production().nonterminal(nt) == item;
                            Term inner = tc.get(nt);
                            boolean assoc = false;
                            if (inner instanceof TermCons) {
                                TermCons innerTc = (TermCons)inner;
                                if (innerTc.production().equals(tc.production()) && tc.production().att().contains("assoc")) {
                                    assoc = true;
                                }
                            }
                            if (assoc) {
                                for (int j = 0; j < indent; j++) {
                                    indenter.dedent();
                                }
                            }
                            format(tc.get(nt), indenter);
                            if (assoc) {
                                for (int j = 0; j < indent; j++) {
                                    indenter.indent();
                                }
                            }
                        } else {
                            throw KEMException.internalError("Cannot currently format productions with regex terminals which are not tokens.", tc.production());
                        }
                        break;
                    default:
                        indenter.append(c2);
                    }
                } else {
                    indenter.append(c);
                }
            }
        }
    }

    private static String defaultFormat(int size) {
        StringBuilder sb = new StringBuilder();
        for (int i = 1; i <= size; i++) {
            sb.append("%").append(i).append(" ");
        }
        sb.deleteCharAt(sb.length() - 1);
        return sb.toString();
    }
}
