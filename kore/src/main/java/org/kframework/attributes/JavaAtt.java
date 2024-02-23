// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.attributes;

import com.google.common.collect.ImmutableSet;
import java.util.Arrays;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import org.kframework.utils.errorsystem.KEMException;
import scala.util.Either;
import scala.util.Left;

public class JavaAtt {
  public record Key<T>(
      Class<T> type,
      String key,
      Function<Optional<String>, Either<ParseError, Attribute>> parser) {}

  public class MyAtt {}
  ;

  public static class Whitelist {
    public static final Key<MyAtt> FOO_1 = new Key<>(MyAtt.class, "foo", s -> null);
    public static final Key<MyAtt> FOO_2 = new Key<>(MyAtt.class, "foo", s -> null);
  }

  public static final ImmutableSet<Key<?>> whitelist =
      Arrays.stream(JavaAtt.Whitelist.class.getDeclaredFields())
          .map(
              f -> {
                try {
                  return (Key<?>) f.get(null);
                } catch (IllegalAccessException e) {
                  throw KEMException.internalError(
                      "Malformed Att.Whitelist field: "
                          + f.getName()
                          + "\nExpected `public static final Key<MyAtt> MY_ATT = new Key<>(...)`");
                }
              })
          .collect(ImmutableSet.toImmutableSet());

  static {
    String dupKeysErr =
        whitelist.stream().collect(Collectors.groupingBy(Key::key)).entrySet().stream()
            .filter(e -> e.getValue().size() > 1)
            .map(
                e ->
                    "\""
                        + e.getKey()
                        + "\": "
                        + e.getValue().stream().map(k -> k.type.getSimpleName()).toList())
            .collect(Collectors.joining("\n"));
    if (!dupKeysErr.isEmpty()) {
      throw KEMException.internalError("Found duplicate keys in Att.Whitelist!\n" + dupKeysErr);
    }
  }

  public sealed interface ParseError {
    record UnrecognizedKey(String key) implements ParseError {}

    record BadValue(KEMException e) implements ParseError {}
  }

  public static Either<ParseError, Attribute> parse(String key, Optional<String> value) {
    Set<Key<?>> keys =
        whitelist.stream().filter(k -> k.key.equals(key)).collect(Collectors.toSet());
    if (keys.size() > 1) {
      throw new AssertionError(
          "Attribute "
              + key
              + value.map(v -> "(" + v + ")").orElse("")
              + " parsed by multiple Att.Whitelist keys: "
              + keys.stream().map(p -> p.type.getSimpleName()).toList());
    }
    if (keys.isEmpty()) {
      return Left.apply(new ParseError.UnrecognizedKey(key));
    }
    return null;
  }

  //  public static Either<AttParsingError, Attribute<?>> parse(String key, String value) {
  //    Attribute<?> foo =
  //        switch (key) {
  //          case "alias" -> TaggedData.ALIAS;
  //          case "alias-rec" -> TaggedData.ALIAS_REC;
  //          case "all-path" -> TaggedData.ALL_PATH;
  //          case "anywhere" -> TaggedData.ANYWHERE;
  //          case "applyPriority" -> new ApplyPriority();
  //          case "assoc" -> TaggedData.ASSOC;
  //          case "avoid" -> TaggedData.AVOID;
  //          case "bag" -> TaggedData.BAG;
  //          case "binder" -> TaggedData.BINDER;
  //          case "bracket" -> TaggedData.BRACKET;
  //          case "cell" -> TaggedData.CELL;
  //          case "cellCollection" -> TaggedData.CELL_COLLECTION;
  //          case "cellName" -> new CellName();
  //          case "circularity" -> TaggedData.CIRCULARITY;
  //          case "color" -> new Color();
  //          case "colors" -> new Colors();
  //          case "comm" -> TaggedData.COMM;
  //          case "concrete" -> new Concrete();
  //          case "constructor" -> TaggedData.CONSTRUCTOR;
  //          case "context" -> new Context();
  //          case "cool" -> TaggedData.COOL;
  //          case "depends" -> new Depends();
  //          case "deprecated" -> TaggedData.DEPRECATED;
  //          case "element" -> new Element();
  //          case "exit" -> TaggedData.EXIT;
  //          case "format" -> new Format();
  //          case "freshGenerator" -> TaggedData.FRESH_GENERATOR;
  //          case "function" -> TaggedData.FUNCTION;
  //          case "functional" -> TaggedData.FUNCTIONAL;
  //          case "group" -> new Group();
  //          case "haskell" -> TaggedData.HASKELL;
  //          case "heat" -> TaggedData.HEAT;
  //          case "hook" -> new Hook();
  //          case "hybrid" -> new Hybrid();
  //          case "idem" -> TaggedData.IDEM;
  //          case "impure" -> TaggedData.IMPURE;
  //          case "index" -> new Index();
  //          case "initial" -> TaggedData.INITIAL;
  //          case "initializer" -> TaggedData.INITIALIZER;
  //          case "injective" -> TaggedData.INJECTIVE;
  //          case "internal" -> TaggedData.INTERNAL;
  //          case "klabel" -> new Klabel();
  //          case "terminator-klabel" -> new TerminatorKlabel();
  //          case "label" -> new Label();
  //          case "latex" -> new Latex();
  //          case "left" -> TaggedData.LEFT;
  //          case "locations" -> TaggedData.LOCATIONS;
  //          case "macro" -> TaggedData.MACRO;
  //          case "macro-rec" -> TaggedData.MACRO_REC;
  //          case "maincell" -> TaggedData.MAINCELL;
  //          case "memo" -> TaggedData.MEMO;
  //          case "mlBinder" -> TaggedData.ML_BINDER;
  //          case "mlOp" -> TaggedData.ML_OP;
  //          case "multiplicity" -> new Multiplicity();
  //          case "non-assoc" -> TaggedData.NON_ASSOC;
  //          case "non-executable" -> TaggedData.NON_EXECUTABLE;
  //          case "not-lr1" -> TaggedData.NOT_LR1;
  //          case "no-evaluators" -> TaggedData.NO_EVALUATORS;
  //          case "one-path" -> TaggedData.ONE_PATH;
  //          case "owise" -> TaggedData.OWISE;
  //          case "parser" -> new Parser();
  //          case "prec" -> new Prec();
  //          case "prefer" -> TaggedData.PREFER;
  //          case "preserves-definedness" -> TaggedData.PRESERVES_DEFINEDNESS;
  //          case "priority" -> new Priority();
  //          case "private" -> TaggedData.PRIVATE;
  //          case "public" -> TaggedData.PUBLIC;
  //          case "result" -> new Result();
  //          case "returnsUnit" -> TaggedData.RETURNS_UNIT;
  //          case "right" -> TaggedData.RIGHT;
  //          case "seqstrict" -> new Seqstrict();
  //          case "simplification" -> new Simplification();
  //          case "smtlib" -> new SMTlib();
  //          case "smt-hook" -> new SMTHook();
  //          case "smt-lemma" -> TaggedData.SMT_LEMMA;
  //          case "stream" -> new Stream();
  //          case "strict" -> new Strict();
  //          case "symbol" -> new Symbol();
  //          case "symbolic" -> new Symbolic();
  //          case "tag" -> new Tag();
  //          case "token" -> TaggedData.TOKEN;
  //          case "total" -> TaggedData.TOTAL;
  //          case "trusted" -> TaggedData.TRUSTED;
  //          case "type" -> new Type();
  //          case "unboundVariables" -> new UnboundVariables();
  //          case "unit" -> new Unit();
  //          case "unparseAvoid" -> TaggedData.UNPARSE_AVOID;
  //          case "unused" -> TaggedData.UNUSED;
  //          case "wrapElement" -> new WrapElement();
  //          case "anonymous" -> new Anonymous();
  //          case "bracketLabel" -> new BracketLabel();
  //          case "cellFragment" -> new CellFragment();
  //          case "cellOptAbsent" -> new CellOptAbsent();
  //          case "cellSort" -> new CellSort();
  //          case "concat" -> new Concat();
  //          case "contentStartColumn" -> new ContentStartColumn();
  //          case "contentStartLine" -> new ContentStartLine();
  //          case "cool-like" -> new CoolLike();
  //          case "denormal" -> new Denormal();
  //          case "digest" -> new Digest();
  //          case "dummy_cell" -> new DummyCell();
  //          case "filterElement" -> new FilterElement();
  //          case "fresh" -> new Fresh();
  //          case "hasDomainValues" -> new HasDomainValues();
  //          case "left" -> new LeftInternal();
  //          case "nat" -> new Nat();
  //          case "notInjection" -> new NotInjection();
  //          case "not-lr1-modules" -> new NotLr1Modules();
  //          case "originalPrd" -> new OriginalPrd();
  //          case "overload" -> new Overload();
  //          case "predicate" -> new Predicate();
  //          case "prettyPrintWithSortAnnotation" -> new PrettyPrintWithSortAnnotation();
  //          case "priorities" -> new Priorities();
  //          case "projection" -> new Projection();
  //          case "recordPrd" -> new RecordPrd();
  //          case "recordPrd-zero" -> new RecordPrdZero();
  //          case "recordPrd-one" -> new RecordPrdOne();
  //          case "recordPrd-main" -> new RecordPrdMain();
  //          case "recordPrd-empty" -> new RecordPrdEmpty();
  //          case "recordPrd-subsort" -> new RecordPrdSubsort();
  //          case "recordPrd-repeat" -> new RecordPrdRepeat();
  //          case "recordPrd-item" -> new RecordPrdItem();
  //          case "refreshed" -> new Refreshed();
  //          case "right" -> new RightInternal();
  //          case "smt-prelude" -> new SMTPrelude();
  //          case "sortParams" -> new SortParams();
  //          case "symbol-overload" -> new SymbolOverload();
  //          case "syntaxModule" -> new SyntaxModule();
  //          case "temporary-cell-sort-decl" -> new TemporaryCellSortDecl();
  //          case "terminals" -> new Terminals();
  //          case "UNIQUE_ID" -> new UniqueId();
  //          case "userList" -> new UserList();
  //          case "userListTerminator" -> new UserListTerminator();
  //          case "withConfig" -> new WithConfig();
  //          default -> null;
  //        };
  //  }

  //  public static final class Alias extends MarkerAttribute<Alias> {
  //    private Alias() {
  //      super(new Key<>(Alias.class), "alias", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class AliasRec extends MarkerAttribute<AliasRec> {
  //    private AliasRec() {
  //      super(new Key<>(AliasRec.class), "alias-rec", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class AllPath extends MarkerAttribute<AllPath> {
  //    private AllPath() {
  //      super(new Key<>(AllPath.class), "all-path", new Visibility.User(Syntax.CLAIM,
  // Syntax.MODULE));
  //    }
  //  }
  //
  //  public static final class Anywhere extends MarkerAttribute<Anywhere> {
  //    private Anywhere() {
  //      super(new Key<>(Anywhere.class), "anywhere", new Visibility.User(Syntax.RULE));
  //    }
  //  }
  //
  //  public static final class Assoc extends MarkerAttribute<Assoc> {
  //    private Assoc() {
  //      super(new Key<>(Assoc.class), "assoc", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Avoid extends MarkerAttribute<Avoid> {
  //    private Avoid() {
  //      super(new Key<>(Avoid.class), "avoid", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Bag extends MarkerAttribute<Bag> {
  //    private Bag() {
  //      super(new Key<>(Bag.class), "bag", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Binder extends MarkerAttribute<Binder> {
  //    private Binder() {
  //      super(new Key<>(Binder.class), "binder", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Bracket extends MarkerAttribute<Bracket> {
  //    private Bracket() {
  //      super(new Key<>(Bracket.class), "bracket", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Cell extends MarkerAttribute<Cell> {
  //    private Cell() {
  //      super(new Key<>(Cell.class), "cell", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class CellCollection extends MarkerAttribute<CellCollection> {
  //    private CellCollection() {
  //      super(
  //          new Key<>(CellCollection.class),
  //          "cellCollection",
  //          new Visibility.User(Syntax.PRODUCTION, Syntax.SYNTAX_SORT));
  //    }
  //  }
  //
  //  public static final class Circularity extends MarkerAttribute<Circularity> {
  //    private Circularity() {
  //      super(new Key<>(Circularity.class), "circularity", new Visibility.User(Syntax.CLAIM));
  //    }
  //  }
  //
  //  public static final class Comm extends MarkerAttribute<Comm> {
  //    private Comm() {
  //      super(new Key<>(Comm.class), "comm", new Visibility.User(Syntax.PRODUCTION, Syntax.RULE));
  //    }
  //  }
  //
  //  public static final class Constructor extends MarkerAttribute<Constructor> {
  //    private Constructor() {
  //      super(new Key<>(Constructor.class), "constructor", new
  // Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Cool extends MarkerAttribute<Cool> {
  //    private Cool() {
  //      super(new Key<>(Cool.class), "cool", new Visibility.User(Syntax.RULE));
  //    }
  //  }
  //
  //  public static final class Deprecated extends MarkerAttribute<Deprecated> {
  //    private Deprecated() {
  //      super(new Key<>(Deprecated.class), "deprecated", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Exit extends MarkerAttribute<Exit> {
  //    private Exit() {
  //      super(new Key<>(Exit.class), "exit", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class FreshGenerator extends MarkerAttribute<FreshGenerator> {
  //    private FreshGenerator() {
  //      super(
  //          new Key<>(FreshGenerator.class),
  //          "freshGenerator",
  //          new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Function extends MarkerAttribute<Function> {
  //    private Function() {
  //      super(new Key<>(Function.class), "function", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Functional extends MarkerAttribute<Functional> {
  //    private Functional() {
  //      super(new Key<>(Functional.class), "functional", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Haskell extends MarkerAttribute<Haskell> {
  //    private Haskell() {
  //      super(new Key<>(Haskell.class), "haskell", new Visibility.User(Syntax.MODULE));
  //    }
  //  }
  //
  //  public static final class Heat extends MarkerAttribute<Heat> {
  //    private Heat() {
  //      super(new Key<>(Heat.class), "heat", new Visibility.User(Syntax.RULE));
  //    }
  //  }
  //
  //  public static final class Idem extends MarkerAttribute<Idem> {
  //    private Idem() {
  //      super(new Key<>(Idem.class), "idem", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Impure extends MarkerAttribute<Impure> {
  //    private Impure() {
  //      super(new Key<>(Impure.class), "impure", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Initial extends MarkerAttribute<Initial> {
  //    private Initial() {
  //      super(new Key<>(Initial.class), "initial", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Initializer extends MarkerAttribute<Initializer> {
  //    private Initializer() {
  //      super(
  //          new Key<>(Initializer.class),
  //          "initializer",
  //          new Visibility.User(Syntax.PRODUCTION, Syntax.RULE));
  //    }
  //  }
  //
  //  public static final class Injective extends MarkerAttribute<Injective> {
  //    private Injective() {
  //      super(new Key<>(Injective.class), "injective", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Internal extends MarkerAttribute<Internal> {
  //    private Internal() {
  //      super(new Key<>(Internal.class), "internal", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Left extends MarkerAttribute<Left> {
  //    private Left() {
  //      super(new Key<>(Left.class), "left", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Locations extends MarkerAttribute<Locations> {
  //    private Locations() {
  //      super(new Key<>(Locations.class), "locations", new Visibility.User(Syntax.SYNTAX_SORT));
  //    }
  //  }
  //
  //  public static final class Macro extends MarkerAttribute<Macro> {
  //    private Macro() {
  //      super(new Key<>(Macro.class), "macro", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class MacroRec extends MarkerAttribute<MacroRec> {
  //    private MacroRec() {
  //      super(new Key<>(MacroRec.class), "macro-rec", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Maincell extends MarkerAttribute<Maincell> {
  //    private Maincell() {
  //      super(new Key<>(Maincell.class), "maincell", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Memo extends MarkerAttribute<Memo> {
  //    private Memo() {
  //      super(new Key<>(Memo.class), "memo", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class MLBinder extends MarkerAttribute<MLBinder> {
  //    private MLBinder() {
  //      super(new Key<>(MLBinder.class), "mlBinder", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class MLOp extends MarkerAttribute<MLOp> {
  //    private MLOp() {
  //      super(new Key<>(MLOp.class), "mlOp", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class NonAssoc extends MarkerAttribute<NonAssoc> {
  //    private NonAssoc() {
  //      super(new Key<>(NonAssoc.class), "non-assoc", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class NonExecutable extends MarkerAttribute<NonExecutable> {
  //    private NonExecutable() {
  //      super(new Key<>(NonExecutable.class), "non-executable", new Visibility.User(Syntax.RULE));
  //    }
  //  }
  //
  //  public static final class NotLR1 extends MarkerAttribute<NotLR1> {
  //    private NotLR1() {
  //      super(new Key<>(NotLR1.class), "not-lr1", new Visibility.User(Syntax.MODULE));
  //    }
  //  }
  //
  //  public static final class NoEvaluators extends MarkerAttribute<NoEvaluators> {
  //    private NoEvaluators() {
  //      super(new Key<>(NoEvaluators.class), "no-evaluators", new
  // Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class OnePath extends MarkerAttribute<OnePath> {
  //    private OnePath() {
  //      super(new Key<>(OnePath.class), "one-path", new Visibility.User(Syntax.CLAIM,
  // Syntax.MODULE));
  //    }
  //  }
  //
  //  public static final class Owise extends MarkerAttribute<Owise> {
  //    private Owise() {
  //      super(new Key<>(Owise.class), "owise", new Visibility.User(Syntax.RULE));
  //    }
  //  }
  //
  //  public static final class Prefer extends MarkerAttribute<Prefer> {
  //    private Prefer() {
  //      super(new Key<>(Prefer.class), "prefer", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class PreservesDefinedness extends MarkerAttribute<PreservesDefinedness> {
  //    private PreservesDefinedness() {
  //      super(
  //          new Key<>(PreservesDefinedness.class),
  //          "preserves-definedness",
  //          new Visibility.User(Syntax.RULE));
  //    }
  //  }
  //
  //  public static final class Private extends MarkerAttribute<Private> {
  //    private Private() {
  //      super(
  //          new Key<>(Private.class),
  //          "private",
  //          new Visibility.User(Syntax.MODULE, Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Public extends MarkerAttribute<Public> {
  //    private Public() {
  //      super(
  //          new Key<>(Public.class), "public", new Visibility.User(Syntax.MODULE,
  // Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class ReturnsUnit extends MarkerAttribute<ReturnsUnit> {
  //    private ReturnsUnit() {
  //      super(new Key<>(ReturnsUnit.class), "returnsUnit", new
  // Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Right extends MarkerAttribute<Right> {
  //    private Right() {
  //      super(new Key<>(Right.class), "right", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class SMTLemma extends MarkerAttribute<SMTLemma> {
  //    private SMTLemma() {
  //      super(new Key<>(SMTLemma.class), "smt-lemma", new Visibility.User(Syntax.RULE));
  //    }
  //  }
  //
  //  public static final class Token extends MarkerAttribute<Token> {
  //    private Token() {
  //      super(
  //          new Key<>(Token.class),
  //          "token",
  //          new Visibility.User(Syntax.SYNTAX_SORT, Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Total extends MarkerAttribute<Total> {
  //    private Total() {
  //      super(new Key<>(Total.class), "total", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Trusted extends MarkerAttribute<Trusted> {
  //    private Trusted() {
  //      super(new Key<>(Trusted.class), "trusted", new Visibility.User(Syntax.CLAIM));
  //    }
  //  }
  //
  //  public static final class UnparseAvoid extends MarkerAttribute<UnparseAvoid> {
  //    private UnparseAvoid() {
  //      super(new Key<>(UnparseAvoid.class), "unparseAvoid", new
  // Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Unused extends MarkerAttribute<Unused> {
  //    private Unused() {
  //      super(new Key<>(Unused.class), "unused", new Visibility.User(Syntax.PRODUCTION));
  //    }
  //  }
  //
  //  public static final class Anonymous extends MarkerAttribute<Anonymous> {
  //    private Anonymous() {
  //      super(new Key<>(Anonymous.class), "anonymous", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class BracketLabel extends MarkerAttribute<BracketLabel> {
  //    private BracketLabel() {
  //      super(new Key<>(BracketLabel.class), "bracketLabel", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class CellFragment extends MarkerAttribute<CellFragment> {
  //    private CellFragment() {
  //      super(new Key<>(CellFragment.class), "cellFragment", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class CellOptAbsent extends MarkerAttribute<CellOptAbsent> {
  //    private CellOptAbsent() {
  //      super(new Key<>(CellOptAbsent.class), "cellOptAbsent", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class CellSort extends MarkerAttribute<CellSort> {
  //    private CellSort() {
  //      super(new Key<>(CellSort.class), "cellSort", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class Concat extends MarkerAttribute<Concat> {
  //    private Concat() {
  //      super(new Key<>(Concat.class), "concat", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class ContentStartColumn extends MarkerAttribute<ContentStartColumn> {
  //    private ContentStartColumn() {
  //      super(new Key<>(ContentStartColumn.class), "contentStartColumn", new
  // Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class ContentStartLine extends MarkerAttribute<ContentStartLine> {
  //    private ContentStartLine() {
  //      super(new Key<>(ContentStartLine.class), "contentStartLine", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class CoolLike extends MarkerAttribute<CoolLike> {
  //    private CoolLike() {
  //      super(new Key<>(CoolLike.class), "cool-like", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class Denormal extends MarkerAttribute<Denormal> {
  //    private Denormal() {
  //      super(new Key<>(Denormal.class), "denormal", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class Digest extends MarkerAttribute<Digest> {
  //    private Digest() {
  //      super(new Key<>(Digest.class), "digest", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class DummyCell extends MarkerAttribute<DummyCell> {
  //    private DummyCell() {
  //      super(new Key<>(DummyCell.class), "dummy_cell", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class FilterElement extends MarkerAttribute<FilterElement> {
  //    private FilterElement() {
  //      super(new Key<>(FilterElement.class), "filterElement", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class Fresh extends MarkerAttribute<Fresh> {
  //    private Fresh() {
  //      super(new Key<>(Fresh.class), "fresh", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class HasDomainValues extends MarkerAttribute<HasDomainValues> {
  //    private HasDomainValues() {
  //      super(new Key<>(HasDomainValues.class), "hasDomainValues", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class LeftInternal extends MarkerAttribute<LeftInternal> {
  //    private LeftInternal() {
  //      super(new Key<>(LeftInternal.class), "left", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class Nat extends MarkerAttribute<Nat> {
  //    private Nat() {
  //      super(new Key<>(Nat.class), "nat", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class NotInjection extends MarkerAttribute<NotInjection> {
  //    private NotInjection() {
  //      super(new Key<>(NotInjection.class), "notInjection", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class NotLR1Modules extends MarkerAttribute<NotLR1Modules> {
  //    private NotLR1Modules() {
  //      super(new Key<>(NotLR1Modules.class), "not-lr1-modules", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class OriginalPrd extends MarkerAttribute<OriginalPrd> {
  //    private OriginalPrd() {
  //      super(new Key<>(OriginalPrd.class), "originalPrd", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class Overload extends MarkerAttribute<Overload> {
  //    private Overload() {
  //      super(new Key<>(Overload.class), "overload", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class Predicate extends MarkerAttribute<Predicate> {
  //    private Predicate() {
  //      super(new Key<>(Predicate.class), "predicate", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class PrettyPrintWithSortAnnotation
  //      extends MarkerAttribute<PrettyPrintWithSortAnnotation> {
  //    private PrettyPrintWithSortAnnotation() {
  //      super(
  //          new Key<>(PrettyPrintWithSortAnnotation.class),
  //          "prettyPrintWithSortAnnotation",
  //          new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class Priorities extends MarkerAttribute<Priorities> {
  //    private Priorities() {
  //      super(new Key<>(Priorities.class), "priorities", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class Projection extends MarkerAttribute<Projection> {
  //    private Projection() {
  //      super(new Key<>(Projection.class), "projection", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class RecordPrd extends MarkerAttribute<RecordPrd> {
  //    private RecordPrd() {
  //      super(new Key<>(RecordPrd.class), "recordPrd", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class RecordPrdZero extends MarkerAttribute<RecordPrdZero> {
  //    private RecordPrdZero() {
  //      super(new Key<>(RecordPrdZero.class), "recordPrd-zero", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class RecordPrdOne extends MarkerAttribute<RecordPrdOne> {
  //    private RecordPrdOne() {
  //      super(new Key<>(RecordPrdOne.class), "recordPrd-one", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class RecordPrdMain extends MarkerAttribute<RecordPrdMain> {
  //    private RecordPrdMain() {
  //      super(new Key<>(RecordPrdMain.class), "recordPrd-main", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class RecordPrdEmpty extends MarkerAttribute<RecordPrdEmpty> {
  //    private RecordPrdEmpty() {
  //      super(new Key<>(RecordPrdEmpty.class), "recordPrd-empty", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class RecordPrdSubsort extends MarkerAttribute<RecordPrdSubsort> {
  //    private RecordPrdSubsort() {
  //      super(new Key<>(RecordPrdSubsort.class), "recordPrd-subsort", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class RecordPrdRepeat extends MarkerAttribute<RecordPrdRepeat> {
  //    private RecordPrdRepeat() {
  //      super(new Key<>(RecordPrdRepeat.class), "recordPrd-repeat", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class RecordPrdItem extends MarkerAttribute<RecordPrdItem> {
  //    private RecordPrdItem() {
  //      super(new Key<>(RecordPrdItem.class), "recordPrd-item", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class Refreshed extends MarkerAttribute<Refreshed> {
  //    private Refreshed() {
  //      super(new Key<>(Refreshed.class), "refreshed", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class RightInternal extends MarkerAttribute<RightInternal> {
  //    private RightInternal() {
  //      super(new Key<>(RightInternal.class), "right", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class SMTPrelude extends MarkerAttribute<SMTPrelude> {
  //    private SMTPrelude() {
  //      super(new Key<>(SMTPrelude.class), "smt-prelude", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class SortParams extends MarkerAttribute<SortParams> {
  //    private SortParams() {
  //      super(new Key<>(SortParams.class), "sortParams", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class SyntaxModule extends MarkerAttribute<SyntaxModule> {
  //    private SyntaxModule() {
  //      super(new Key<>(SyntaxModule.class), "syntaxModule", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class TemporaryCellSortDecl extends MarkerAttribute<TemporaryCellSortDecl>
  // {
  //    private TemporaryCellSortDecl() {
  //      super(
  //          new Key<>(TemporaryCellSortDecl.class),
  //          "temporary-cell-sort-decl",
  //          new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class UserList extends MarkerAttribute<UserList> {
  //    private UserList() {
  //      super(new Key<>(UserList.class), "userList", new Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class UserListTerminator extends MarkerAttribute<UserListTerminator> {
  //    private UserListTerminator() {
  //      super(new Key<>(UserListTerminator.class), "userListTerminator", new
  // Visibility.Internal());
  //    }
  //  }
  //
  //  public static final class WithConfig extends MarkerAttribute<WithConfig> {
  //    private WithConfig() {
  //      super(new Key<>(WithConfig.class), "withConfig", new Visibility.Internal());
  //    }
  //  }
}
