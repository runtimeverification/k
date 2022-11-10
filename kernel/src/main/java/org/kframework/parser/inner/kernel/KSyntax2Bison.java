// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.parser.inner.kernel;

import org.apache.commons.io.FileUtils;
import org.apache.commons.lang3.mutable.MutableInt;
import org.kframework.Collections;
import org.kframework.TopologicalSort;
import org.kframework.attributes.Att;
import org.kframework.backend.kore.ModuleToKORE;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.Sentence;
import org.kframework.definition.Tag;
import org.kframework.definition.Terminal;
import org.kframework.definition.TerminalLike;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;
import org.kframework.parser.inner.RuleGrammarGenerator;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.io.File;
import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import scala.Tuple2;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class KSyntax2Bison {

  private static void computeSide(int idx, Production prod, List<ProductionItem> items, Module module, scala.collection.Set<Tuple2<Tag, Tag>> assoc, Map<Set<Tag>, Integer> ordinals, Set<Tuple2<Sort, Set<Tag>>> nts, MutableInt nextOrdinal) {
    NonTerminal nt = (NonTerminal) items.get(idx);
    Tag parent = new Tag(prod.klabel().get().name());
    Set<Tag> prods = new HashSet<>();
    for (Tag child : iterable(module.priorities().relations().get(parent).getOrElse(() -> Collections.<Tag>Set()))) {
      prods.add(child);
    }
    for (Tuple2<Tag, Tag> entry : iterable(assoc)) {
      if (entry._1().equals(parent)) {
        prods.add(entry._2());
      }
    }
    if (prods.isEmpty()) {
      return;
    }
    int ordinal;
    if (ordinals.containsKey(prods)) {
      ordinal = ordinals.get(prods);
    } else {
      ordinal = nextOrdinal.intValue();
      ordinals.put(prods, nextOrdinal.intValue());
      nextOrdinal.increment();
    }
    items.set(idx, NonTerminal(Sort(nt.sort().name() + "#" + ordinal, nt.sort().params()), nt.name()));
    nts.add(Tuple2.apply(nt.sort(), prods));
  }

  public static Module transformByPriorityAndAssociativity(Module module) {
    Map<Set<Tag>, Integer> ordinals = new HashMap<>();
    MutableInt nextOrdinal = new MutableInt(0);
    Set<Sentence> sentences = new HashSet<>();
    Set<Tuple2<Sort, Set<Tag>>> nts = new HashSet<>();
    for (Sentence s : iterable(module.sentences())) {
      if (s instanceof Production) {
        Production prod = (Production)s;
        if (prod.klabel().isDefined() && prod.params().isEmpty()) {
          List<ProductionItem> items = new ArrayList<>(mutable(prod.items()));
          if (items.get(0) instanceof NonTerminal) {
            computeSide(0, prod, items, module, module.rightAssoc(), ordinals, nts, nextOrdinal);
          }
          if (items.size() > 1 && items.get(items.size() - 1) instanceof NonTerminal) {
            computeSide(items.size()-1, prod, items, module, module.leftAssoc(), ordinals, nts, nextOrdinal);
          }
          sentences.add(Production(prod.klabel(), prod.params(), prod.sort(), immutable(items), prod.att().add(Att.ORIGINAL_PRD(), Production.class, prod)));
        } else {
          sentences.add(prod.withAtt(prod.att().add(Att.ORIGINAL_PRD(), Production.class, prod)));
        }
      } else {
        sentences.add(s);
      }
    }
    module = Module(module.name(), module.imports(), immutable(sentences), module.att());
    Deque<Tuple2<Sort, Set<Tag>>> worklist = new ArrayDeque<>(nts);
    worklist.addAll(nts);
    while (!worklist.isEmpty()) {
      Tuple2<Sort, Set<Tag>> item = worklist.poll();
      for (Production prod : iterable(module.productionsForSort().apply(item._1().head()))) {
        int ordinal = ordinals.get(item._2());
        Sort newNT = Sort(item._1().name() + "#" + ordinal, item._1().params());
        if (prod.isSubsort()) {
          worklist.offer(Tuple2.apply(prod.getSubsortSort(), item._2()));
          sentences.add(Production(prod.klabel(), prod.params(), newNT, Seq(NonTerminal(prod.getSubsortSort(), prod.nonterminals().apply(0).name())), prod.att()));
        } else if (prod.klabel().isEmpty() || !item._2().contains(new Tag(prod.klabel().get().name()))) {
          sentences.add(Production(prod.klabel(), prod.params(), newNT, prod.items(), prod.att()));
        }
      }
    }
    return Module(module.name(), module.imports(), immutable(sentences), module.att());
  }

  public static void writeParser(Module module, Module disambModule, Scanner scanner, Sort start, File path, boolean glr, long stackDepth, KExceptionManager kem) {
    if (module.att().contains("not-lr1")) {
        kem.registerInnerParserWarning(ExceptionType.NON_LR_GRAMMAR, "Skipping modules " + module.att().get("not-lr1") + " tagged as not-lr1 which are not supported by Bison.");
    }
    module = transformByPriorityAndAssociativity(module);
    StringBuilder bison = new StringBuilder();
    bison.append("%{\n" +
        "#include <stdio.h>\n" +
        "#include <string.h>\n" +
        "#include \"node.h\"\n" +
        "#include \"parser.tab.h\"\n" +
        "int yylex(YYSTYPE *, YYLTYPE *, void *);\n" +
        "void yyerror(YYLTYPE *, void *, const char *);\n" +
        "char *enquote(char *);\n" +
        "char *injSymbol(char *, char *);\n" +
        "YYSTYPE mergeAmb(YYSTYPE x0, YYSTYPE x1);\n" +
        "node *result;\n" +
        "extern char *filename;\n" +
        "# define YYMAXDEPTH " + stackDepth + "\n" +
        "# define YYLLOC_DEFAULT(Cur, Rhs, N)                      \\\n" +
        "do                                                        \\\n" +
        "  if (N)                                                  \\\n" +
        "    {                                                     \\\n" +
        "      (Cur).filename     = YYRHSLOC(Rhs, 1).filename;     \\\n" +
        "      (Cur).first_line   = YYRHSLOC(Rhs, 1).first_line;   \\\n" +
        "      (Cur).first_column = YYRHSLOC(Rhs, 1).first_column; \\\n" +
        "      (Cur).last_line    = YYRHSLOC(Rhs, N).last_line;    \\\n" +
        "      (Cur).last_column  = YYRHSLOC(Rhs, N).last_column;  \\\n" +
        "    }                                                     \\\n" +
        "  else                                                    \\\n" +
        "    {                                                     \\\n" +
        "      (Cur).filename     = YYRHSLOC(Rhs, 0).filename;     \\\n" +
        "      (Cur).first_line   = (Cur).last_line   =            \\\n" +
        "        YYRHSLOC(Rhs, 0).last_line;                       \\\n" +
        "      (Cur).first_column = (Cur).last_column =            \\\n" +
        "        YYRHSLOC(Rhs, 0).last_column;                     \\\n" +
        "    }                                                     \\\n" +
        "while (0)\n" +
        "%}\n\n");
    bison.append("%define api.value.type {union value_type}\n");
    bison.append("%define api.pure\n");
    bison.append("%define lr.type ielr\n");
    bison.append("%lex-param {void *scanner} \n");
    bison.append("%parse-param {void *scanner} \n");
    bison.append("%locations\n");
    bison.append("%initial-action {\n" +
        "  @$.filename = filename;\n" +
        "  @$.first_line = @$.first_column = @$.last_line = @$.last_column = 1;\n" +
        "}\n");
    if (glr) {
      bison.append("%glr-parser\n");
    }
    bison.append("%define parse.error verbose\n");
    for (int kind : scanner.kinds()) {
      TerminalLike tok = scanner.getTokenByKind(kind);
      String val;
      if (tok instanceof Terminal) {
        val = ((Terminal)tok).value();
      } else {
        val = ((RegexTerminal)tok).regex();
      }
      bison.append("%token TOK_" + kind + " " + (kind+1) + " " + StringUtil.enquoteCString(val) + "\n");
    }

    //compute sorts reachable from start symbol
    Map<Sort, List<Production>> prods = stream(module.productions()).collect(Collectors.groupingBy(p -> p.sort()));
    Set<Sort> reachableSorts = new HashSet<>();
    Deque<Sort> workList = new ArrayDeque<>();
    workList.offer(start);
    do {
      Sort s = workList.poll();
      if (reachableSorts.add(s)) {
        List<Production> prodsForSort = prods.getOrDefault(s, java.util.Collections.<Production>emptyList());
        for (Production prod : prodsForSort) {
          for (NonTerminal nt : iterable(prod.nonterminals())) {
            workList.offer(nt.sort());
          }
        }
      }
    } while (!workList.isEmpty());

    for (Sort sort : reachableSorts) {
      bison.append("%nterm ");
      encode(sort, bison);
      bison.append("\n");
    }
    bison.append("%start top");
    bison.append("\n");
    bison.append("\n%%\n");
    bison.append("top: ");
    encode(start, bison);
    bison.append(" { result = $1.nterm; } ;\n");
    for (Sort sort : reachableSorts) {
      List<Production> prodsForSort = Optional.ofNullable(prods.get(sort)).orElse(java.util.Collections.emptyList());
      if (!prodsForSort.isEmpty()) {
        encode(sort, bison);
        bison.append(":\n");
        String conn = "";
        for (Production prod : prodsForSort) {
          bison.append("  " + conn);
          processProduction(prod, module, disambModule, scanner, bison, glr);
          conn = "|";
        }
        bison.append(";\n");
      }
    }
    bison.append("\n%%\n");
    bison.append("\n" +
        "void yyerror (YYLTYPE *loc, void *scanner, const char *s) {\n" +
        "    fprintf (stderr, \"%s:%d:%d:%d:%d:%s\\n\", loc->filename, loc->first_line, loc->first_column, loc->last_line, loc->last_column, s);\n" +
        "}\n");
    try {
      FileUtils.write(path, bison);
    } catch (IOException e) {
      throw KEMException.internalError("Failed to write file for parser", e);
    }
  }

  private static final Pattern identChar = Pattern.compile("[A-Za-z0-9]");

  private static void encode(Sort sort, StringBuilder sb) {
    sb.append("Sort");
    StringUtil.encodeStringToAlphanumeric(sb, sort.name(), StringUtil.asciiReadableEncodingDefault, identChar, "_");
    sb.append("_");
    String conn = "";
    for (Sort param : iterable(sort.params())) {
      sb.append(conn);
      encode(param, sb);
      conn = "_";
    }
    sb.append("_");
  }

  private static void appendOverloadCondition(StringBuilder bison, Module module, Production greater, Production lesser, List<Integer> nts) {
    bison.append("true");
    for (int i = 0; i < nts.size(); i++) {
      boolean hasSameSort = lesser.nonterminals().apply(i).sort().equals(greater.nonterminals().apply(i).sort());
      if (!hasSameSort) {
        bison.append(" && strncmp($").append(nts.get(i)).append(".nterm->symbol, \"inj{\", 4) == 0 && (false");
        Sort greaterSort = lesser.nonterminals().apply(i).sort();
        for (Sort lesserSort : iterable(module.subsorts().elements())) {
          if (module.subsorts().lessThanEq(lesserSort, greaterSort)) {
            bison.append(" || strcmp($").append(nts.get(i)).append(".nterm->children[0]->sort, \"");
            encodeKore(lesserSort, bison);
            bison.append("\") == 0");
          }
        }
        bison.append(")");
      }
    }
  }

  private static void appendOverloadChecks(StringBuilder bison, Module module, Module disambModule, Production greater, List<Integer> nts, boolean hasLocation) {
    for (Production lesser : iterable(disambModule.overloads().sortedElements())) {
      if (disambModule.overloads().lessThan(lesser, greater)) {
        bison.append("  if (");
        appendOverloadCondition(bison, module, greater, lesser, nts);
        bison.append(") {\n" +
            "    n->symbol =\"");
        encodeKore(lesser.klabel().get(), bison);
        bison.append("\";\n" +
            "    n->sort = \"");
        encodeKore(lesser.sort(), bison);
        boolean hasLesserLocation = module.sortAttributesFor().get(lesser.sort().head()).getOrElse(() -> Att.empty()).contains("locations");
        bison.append("\";\n" +
            "    n->hasLocation = " + (hasLesserLocation ? "1" : "0") + ";\n");
        for (int i = 0; i < nts.size(); i++) {
          boolean hasSameSort = lesser.nonterminals().apply(i).sort().equals(greater.nonterminals().apply(i).sort());
          if (hasSameSort) {
            bison.append(
                "    n->children[").append(i).append("] = $").append(nts.get(i)).append(".nterm;\n");
          } else {
            bison.append(
                "    {\n" +
                "      node *origChild = $").append(nts.get(i)).append(".nterm;\n" +
                "      char *lesserSort = \"");
            encodeKore(lesser.nonterminals().apply(i).sort(), bison);
            bison.append("\";\n" +
                "      if (strcmp(origChild->children[0]->sort, lesserSort) == 0) {\n" +
                "        n->children[").append(i).append("] = origChild->children[0];\n" +
                "      } else {\n" +
                "        node *inj = malloc(sizeof(node) + sizeof(node *));\n" +
                "        inj->symbol = injSymbol(origChild->children[0]->sort, lesserSort);\n" +
                "        inj->str = false;\n" +
                "        inj->location = origChild->location;\n" +
                "        inj->nchildren = 1;\n" +
                "        inj->sort = lesserSort;\n" +
                "        inj->hasLocation = origChild->hasLocation;\n" +
                "        inj->children[0] = origChild->children[0];\n" +
                "        n->children[").append(i).append("] = inj;\n" +
                "      }\n" +
                "    }\n");
          }
        }
        bison.append(
            "    node *n2 = malloc(sizeof(node) + sizeof(node *));\n" +
            "    n2->str = false;\n" +
            "    n2->location = @$;\n" +
            "    n2->nchildren = 1;\n" +
            "    n2->sort = \"");
        encodeKore(greater.sort(), bison);
        bison.append("\";\n" +
            "    n2->hasLocation = " + (hasLocation ? "1" : "0") + ";\n" +
            "    n2->symbol = injSymbol(n->sort, n2->sort);\n" +
            "    n2->children[0] = n;\n" +
            "    value_type result = {.nterm = n2};\n" +
            "    $$ = result;\n" +
            "  } else");
      }
    }
  }

  private static void processProduction(Production prod, Module module, Module disambModule, Scanner scanner, StringBuilder bison, boolean glr) {
    int i = 1;
    List<Integer> nts = new ArrayList<>();
    for (ProductionItem item : iterable(prod.items())) {
      if (item instanceof NonTerminal) {
        NonTerminal nt = (NonTerminal)item;
        encode(nt.sort(), bison);
        bison.append(" ");
        nts.add(i);
      } else {
        TerminalLike t = (TerminalLike)item;
        if (!(t instanceof Terminal && ((Terminal)t).value().equals(""))) {
          bison.append("TOK_" + scanner.resolve(t) + " ");
        } else {
          i--;
        }
      }
      i++;
    }
    prod = prod.att().getOptional(Att.ORIGINAL_PRD(), Production.class).orElse(prod);
    if (!prod.att().contains("userListTerminator")) {
      // further adjustment to get back original production in case of user lists.
      // don't apply this adjustment to the production that handles the last element of the
      // list
      prod = prod.att().getOptional(Att.ORIGINAL_PRD(), Production.class).orElse(prod);
    }
    boolean hasLocation = module.sortAttributesFor().get(prod.sort().head()).getOrElse(() -> Att.empty()).contains("locations");
    if (prod.att().contains("token") && !prod.isSubsort()) {
      bison.append("{\n" +
          "  node *n = malloc(sizeof(node));\n" +
          "  n->symbol = ");
      boolean isString = module.sortAttributesFor().get(prod.sort().head()).getOrElse(() -> Att.empty()).getOptional("hook").orElse("").equals("STRING.String");
      boolean isBytes  = module.sortAttributesFor().get(prod.sort().head()).getOrElse(() -> Att.empty()).getOptional("hook").orElse("").equals("BYTES.Bytes");
      if (!isString && !isBytes) {
        bison.append("enquote(");
      }
      bison.append("$1.token");
      if (isBytes) {
        bison.append("+1"); // skip the first 'b' char
      }
      if (!isString && !isBytes) {
        bison.append(")");
      }
      bison.append(";\n" +
          "  n->str = true;\n" +
          "  n->location = @$;\n" +
          "  n->hasLocation = 0;\n" +
          "  n->nchildren = 0;\n" +
          "  node *n2 = malloc(sizeof(node) + sizeof(node *));\n" +
          "  n2->symbol = \"\\\\dv{");
      encodeKore(prod.sort(), bison);
      bison.append("}\";\n" +
          "  n2->sort = \"");
      encodeKore(prod.sort(), bison);
      bison.append("\";\n" +
          "  n2->str = false;\n" +
          "  n2->location = @$;\n" +
          "  n2->hasLocation = " + (hasLocation ? "1" : "0") + ";\n" +
          "  n2->nchildren = 1;\n" +
          "  n2->children[0] = n;\n" +
          "  value_type result = {.nterm = n2};\n" +
          "  $$ = result;\n" +
          "}\n");
    } else if (!prod.att().contains("token") && prod.isSubsort() && !prod.att().contains(RuleGrammarGenerator.NOT_INJECTION)) {
      bison.append("{\n" +
          "  node *n = malloc(sizeof(node) + sizeof(node *));\n" +
          "  n->str = false;\n" +
          "  n->location = @$;\n" +
          "  n->hasLocation = " + (hasLocation ? "1" : "0") + ";\n" +
          "  n->nchildren = 1;\n" +
          "  n->sort = \"");
      encodeKore(prod.sort(), bison);
      bison.append("\";\n" +
          "  if (!$1.nterm->str && strncmp($1.nterm->symbol, \"inj{\", 4) == 0) {\n" +
          "    char *childSort = $1.nterm->children[0]->sort;\n" +
          "    n->symbol = injSymbol(childSort, n->sort);\n" +
          "    n->children[0] = $1.nterm->children[0];\n" +
          "  } else {\n" +
          "    n->symbol = \"inj{");
      encodeKore(prod.getSubsortSort(), bison);
      bison.append(", ");
      encodeKore(prod.sort(), bison);
      bison.append("}\";\n" +
          "    n->children[0] = $1.nterm;\n" +
          "  }\n");
      if (prod.att().contains("userListTerminator")) {
        KLabel nil = KLabel(prod.att().get("userListTerminator"));
        KLabel cons = KLabel(prod.att().get("userList"));
        bison.append(
          "  node *n2 = malloc(sizeof(node));\n" +
          "  n2->symbol = \"");
        encodeKore(nil, bison);
        bison.append("\";\n" +
          "  n2->str = false;\n" +
          "  n2->location = @$;\n" +
          "  n2->hasLocation = 0;\n" +
          "  n2->nchildren = 0;\n" +
          "  n2->sort = \"");
        encodeKore(prod.sort(), bison);
        bison.append("\";\n" +
          "  node *n3 = malloc(sizeof(node) + 2*sizeof(node *));\n" +
          "  n3->symbol = \"");
        encodeKore(cons, bison);
        bison.append("\";\n" +
          "  n3->str = false;\n" +
          "  n3->location = @$;\n" +
          "  n3->hasLocation = " + (hasLocation ? "1" : "0") + ";\n" +
          "  n3->nchildren = 2;\n" +
          "  n3->children[0] = n2;\n" +
          "  n3->children[1] = $1.nterm;\n" +
          "  n3->sort = \"");
        encodeKore(prod.sort(), bison);
        bison.append("\";\n" +
          "  value_type result = {.nterm = n3};\n" +
          "  $$ = result;\n" +
          "}\n");
      } else {
        bison.append("  value_type result = {.nterm = n};\n" +
          "  $$ = result;\n" +
          "}\n");
      }

    } else if (prod.att().contains("token") && prod.isSubsort()) {
      bison.append("{\n" +
          "  node *n = malloc(sizeof(node) + sizeof(node *));\n" +
          "  n->symbol = \"\\\\dv{");
      encodeKore(prod.sort(), bison);
      bison.append("}\";\n" +
          "  n->sort = \"");
      encodeKore(prod.sort(), bison);
      bison.append("\";\n" +
          "  n->str = false;\n" +
          "  n->location = @$;\n" +
          "  n->hasLocation = " + (hasLocation ? "1" : "0") + ";\n" +
          "  n->nchildren = 1;\n" +
          "  n->children[0] = $1.nterm->children[0];\n" +
          "  value_type result = {.nterm = n};\n" +
          "  $$ = result;\n" +
          "}\n");
    } else if (prod.klabel().isDefined()) {
      bison.append("{\n" +
          "  node *n = malloc(sizeof(node) + sizeof(node *)*").append(nts.size()).append(");\n" +
          "  n->str = false;\n" +
          "  n->location = @$;\n" +
          "  n->nchildren = ").append(nts.size()).append(";\n");
      appendOverloadChecks(bison, module, disambModule, prod, nts, hasLocation);
      bison.append("{\n" +
          "    n->symbol = \"");
      encodeKore(prod.klabel().get(), bison);
      bison.append("\";\n" +
          "    n->sort = \"");
      encodeKore(prod.sort(), bison);
      bison.append("\";\n" +
          "    n->hasLocation = " + (hasLocation ? "1" : "0") + ";\n");
      for (i = 0; i < nts.size(); i++) {
        bison.append(
          "    n->children[").append(i).append("] = $").append(nts.get(i)).append(".nterm;\n");
      }
      bison.append(
          "    value_type result = {.nterm = n};\n" +
          "    $$ = result;\n" +
          "  }\n" +
          "}\n");
    } else if (prod.att().contains(Att.BRACKET())) {
      bison.append("{\n" +
          "  $$ = $").append(nts.get(0)).append(";\n" +
          "}\n");
    }
    if (glr) {
      bison.append("%merge <mergeAmb> ");
      if (prod.att().contains("prefer")) {
        bison.append("%dprec 3\n");
      } else if (prod.att().contains("avoid")) {
        bison.append("%dprec 1\n");
      } else {
        bison.append("%dprec 2\n");
      }
    }
    bison.append("\n");
  }

  private static void encodeKore(KLabel klabel, StringBuilder bison) {
    StringBuilder sb = new StringBuilder();
    ModuleToKORE.convert(klabel, sb);
    String quoted = StringUtil.enquoteCString(sb.toString());
    bison.append(quoted.substring(1, quoted.length() - 1));
  }

  private static void encodeKore(Sort sort, StringBuilder bison) {
    StringBuilder sb = new StringBuilder();
    ModuleToKORE.convert(sort, sb);
    String quoted = StringUtil.enquoteCString(sb.toString());
    bison.append(quoted.substring(1, quoted.length() - 1));
  }
}
