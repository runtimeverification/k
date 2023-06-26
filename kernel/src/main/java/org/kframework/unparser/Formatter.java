// Copyright (c) K Team. All Rights Reserved.

package org.kframework.unparser;

import org.kframework.attributes.Att;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Terminal;
import org.kframework.parser.Constant;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.ColorUtil;

import static org.kframework.Collections.*;
import static org.fusesource.jansi.Ansi.*;

public class Formatter {

    public static String format(Term term) {
        Indenter indenter = new Indenter(2);
        format(term, indenter, ColorSetting.OFF);
        return indenter.toString();
    }

    public static String format(Term term, ColorSetting colorize) {
        Indenter indenter = new Indenter(2);
        format(term, indenter, colorize);
        return indenter.toString();
    }

    public static void format(Term term, Indenter indenter, ColorSetting colorize) {
        int indent = 0;
        int localColor = 0;
        if (term instanceof Constant) {
            Constant c = (Constant) term;
            color(indenter, c.production(), 0, colorize);
            indenter.append(c.value());
            resetColor(indenter, c.production(), colorize);
        } else if (term instanceof TermCons) {
            TermCons tc = (TermCons) term;
            String format = tc.production().att().getOptional(Att.FORMAT()).orElse(defaultFormat(tc.production().items().size()));
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
                            color(indenter, tc.production(), localColor++, colorize);
                            indenter.append(((Terminal) item).value());
                            resetColor(indenter, tc.production(), colorize);
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
                                Production origProd = tc.production().att().getOptional(Att.ORIGINAL_PRD(), Production.class).orElse(tc.production());
                                Production innerOrigProd = innerTc.production().att().getOptional(Att.ORIGINAL_PRD(), Production.class).orElse(innerTc.production());
                                if (innerOrigProd.equals(origProd) && origProd.att().contains(Att.ASSOC())) {
                                    assoc = true;
                                }
                            }
                            if (assoc) {
                                for (int j = 0; j < indent; j++) {
                                    indenter.dedent();
                                }
                            }
                            format(tc.get(nt), indenter, colorize);
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

    public static String defaultFormat(int size) {
        StringBuilder sb = new StringBuilder();
        for (int i = 1; i <= size; i++) {
            sb.append("%").append(i).append(" ");
        }
        sb.deleteCharAt(sb.length() - 1);
        return sb.toString();
    }

    private static void color(Indenter indenter, Production p, int offset, ColorSetting colorize) {
        if (p.att().contains(Att.COLOR())) {
            indenter.append(ColorUtil.RgbToAnsi(p.att().get(Att.COLOR()), colorize));
        }
        if (p.att().contains(Att.COLORS())) {
            try {
                String color = p.att().get(Att.COLORS()).split(",")[offset].trim();
                indenter.append(ColorUtil.RgbToAnsi(color, colorize));
            } catch (ArrayIndexOutOfBoundsException e) {
                throw KEMException.compilerError("Invalid colors attribute. Must be a comma separated list with exactly one element per terminal.", e, p);
            }
        }
    }

    private static void resetColor(Indenter indenter, Production p, ColorSetting colorize) {
        if ((p.att().contains(Att.COLOR()) || p.att().contains(Att.COLORS()))  && colorize != ColorSetting.OFF) {
            indenter.append(ColorUtil.ANSI_NORMAL);
        }
    }
}
