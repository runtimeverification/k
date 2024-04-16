// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.json;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

import java.io.IOException;
import java.io.StringReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import javax.json.*;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.definition.Associativity;
import org.kframework.definition.Bubble;
import org.kframework.definition.Claim;
import org.kframework.definition.Configuration;
import org.kframework.definition.Constructors;
import org.kframework.definition.Context;
import org.kframework.definition.Definition;
import org.kframework.definition.FlatImport;
import org.kframework.definition.FlatModule;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.definition.SortSynonym;
import org.kframework.definition.SyntaxAssociativity;
import org.kframework.definition.SyntaxLexical;
import org.kframework.definition.SyntaxPriority;
import org.kframework.definition.SyntaxSort;
import org.kframework.definition.Tag;
import org.kframework.definition.Terminal;
import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.kore.KORE;
import org.kframework.kore.Sort;
import org.kframework.parser.outer.Outer;
import org.kframework.unparser.ToJson;
import org.kframework.utils.errorsystem.KEMException;
import scala.Option;

/** Parses a Json term into the KORE data structures. */
public class JsonParser {

  public static final String INJECTEDKLABEL = "InjectedKLabel";
  public static final String KAPPLY = "KApply";
  public static final String KAS = "KAs";
  public static final String KATT = "KAtt";
  public static final String KBUBBLE = "KBubble";
  public static final String KCONFIGURATION = "KConfiguration";
  public static final String KCONTEXT = "KContext";
  public static final String KDEFINITION = "KDefinition";
  public static final String KNONTERMINAL = "KNonTerminal";
  public static final String KFLATMODULE = "KFlatModule";
  public static final String KFLATMODULELIST = "KFlatModuleList";
  public static final String KIMPORT = "KImport";
  public static final String KPRODUCTION = "KProduction";
  public static final String KREGEXTERMINAL = "KRegexTerminal";
  public static final String KREWRITE = "KRewrite";
  public static final String KRULE = "KRule";
  public static final String KCLAIM = "KClaim";
  public static final String KSEQUENCE = "KSequence";
  public static final String KSORT = "KSort";
  public static final String KSORTSYNONYM = "KSortSynonym";
  public static final String KSYNTAXLEXICAL = "KSyntaxLexical";
  public static final String KSYNTAXASSOCIATIVITY = "KSyntaxAssociativity";
  public static final String KSYNTAXPRIORITY = "KSyntaxPriority";
  public static final String KSYNTAXSORT = "KSyntaxSort";
  public static final String KTERMINAL = "KTerminal";
  public static final String KTOKEN = "KToken";
  public static final String KVARIABLE = "KVariable";

  /////////////////////////////
  // Parsing Definition Json //
  /////////////////////////////

  public static Definition parseDefinition(byte[] data) {
    return parseDefinition(new String(data, StandardCharsets.UTF_8));
  }

  public static Definition parseDefinition(String data) {
    JsonReader reader = Json.createReader(new StringReader(data));
    return parseJsonDef(reader.readObject());
  }

  public static Definition parseJsonDef(JsonObject data) {
    try {
      if (!(data.containsKey("format")
          && data.containsKey("version")
          && data.containsKey("term"))) {
        throw KEMException.criticalError(
            "Must have `format`, `version`, and `term` fields in serialized Json!");
      }
      if (!data.getString("format").equals("KAST")) {
        throw KEMException.criticalError(
            "Only can deserialize 'KAST' format Json! Found: " + data.getString("format"));
      }
      if (data.getInt("version") != ToJson.version) {
        throw KEMException.criticalError(
            "Only can deserialize KAST version '"
                + ToJson.version
                + "'! Found: "
                + data.getInt("version"));
      }
      return toDefinition(data.getJsonObject("term"));
    } catch (IOException e) {
      throw KEMException.criticalError("Could not read Definition term from json", e);
    }
  }

  public static Definition toDefinition(JsonObject data) throws IOException {
    if (!data.getString("node").equals(KDEFINITION))
      throw KEMException.criticalError(
          "Unexpected node found in KAST Json term: " + data.getString("node"));

    String mainModuleName = data.getString("mainModule");
    JsonArray mods = data.getJsonArray("modules");
    List<FlatModule> flatModules = new ArrayList<>();
    for (JsonObject m : mods.getValuesAs(JsonObject.class)) {
      flatModules.add(toFlatModule(m));
    }

    scala.collection.immutable.Set<Module> koreModules =
        FlatModule.toModules(immutable(flatModules), Set());
    return Constructors.Definition(
        koreModules
            .find(x -> x.name().equals(mainModuleName))
            .getOrElse(
                () -> {
                  throw new AssertionError(
                      "Could not find main module name "
                          + mainModuleName
                          + " when loading from JSON.");
                }),
        koreModules,
        toAtt(data.getJsonObject("att")));
  }

  /////////////////////////
  // Parsing Module Json //
  /////////////////////////

  public static FlatModule toFlatModule(JsonObject data) {
    if (!data.getString("node").equals(KFLATMODULE))
      throw KEMException.criticalError(
          "Unexpected node found in KAST Json term: " + data.getString("node"));

    String name = data.getString("name");

    JsonArray jsonimports = data.getJsonArray("imports");
    Set<FlatImport> imports = new HashSet<>();
    jsonimports
        .getValuesAs(JsonObject.class)
        .forEach(
            i ->
                imports.add(
                    FlatImport.apply(i.getString("name"), i.getBoolean("isPublic"), Att.empty())));

    JsonArray sentences = data.getJsonArray("localSentences");
    Set<Sentence> localSentences = new HashSet<>();
    for (JsonObject j : sentences.getValuesAs(JsonObject.class)) {
      localSentences.add(toSentence(j));
    }

    return new FlatModule(
        name, immutable(imports), immutable(localSentences), toAtt(data.getJsonObject("att")));
  }

  ///////////////////////////
  // Parsing Sentence Json //
  ///////////////////////////

  public static Sentence toSentence(JsonObject data) {
    switch (data.getString("node")) {
      case KCONTEXT -> {
        K body = toK(data.getJsonObject("body"));
        K requires = toK(data.getJsonObject("requires"));
        Att att = toAtt(data.getJsonObject("att"));
        return new Context(body, requires, att);
      }
      case KRULE -> {
        K body = toK(data.getJsonObject("body"));
        K requires = toK(data.getJsonObject("requires"));
        K ensures = toK(data.getJsonObject("ensures"));
        Att att = toAtt(data.getJsonObject("att"));
        return new Rule(body, requires, ensures, att);
      }
      case KCLAIM -> {
        K body = toK(data.getJsonObject("body"));
        K requires = toK(data.getJsonObject("requires"));
        K ensures = toK(data.getJsonObject("ensures"));
        Att att = toAtt(data.getJsonObject("att"));
        return new Claim(body, requires, ensures, att);
      }
      case KSYNTAXPRIORITY -> {
        JsonArray priorities = data.getJsonArray("priorities");
        Att att = toAtt(data.getJsonObject("att"));
        List<scala.collection.immutable.Set<Tag>> syntaxPriorities = new ArrayList<>();
        priorities.getValuesAs(JsonArray.class).forEach(tags -> syntaxPriorities.add(toTags(tags)));
        return new SyntaxPriority(immutable(syntaxPriorities), att);
      }
      case KSYNTAXASSOCIATIVITY -> {
        String assocString = data.getString("assoc");
        Associativity assoc =
            "Left".equals(assocString)
                ? Associativity.Left
                : "Right".equals(assocString)
                    ? Associativity.Right
                    : "NonAssoc".equals(assocString)
                        ? Associativity.NonAssoc
                        : Associativity.Unspecified;
        scala.collection.immutable.Set<Tag> tags = toTags(data.getJsonArray("tags"));
        Att att = toAtt(data.getJsonObject("att"));
        return new SyntaxAssociativity(assoc, tags, att);
      }
      case KCONFIGURATION -> {
        K body = toK(data.getJsonObject("body"));
        K ensures = toK(data.getJsonObject("ensures"));
        Att att = toAtt(data.getJsonObject("att"));
        return new Configuration(body, ensures, att);
      }
      case KSYNTAXSORT -> {
        Sort sort = toSort(data.getJsonObject("sort"));
        Att att = toAtt(data.getJsonObject("att"));
        List<Sort> params = new ArrayList<>();
        for (JsonObject s : data.getJsonArray("params").getValuesAs(JsonObject.class)) {
          params.add(toSort(s));
        }
        return new SyntaxSort(immutable(params), sort, att);
      }
      case KSORTSYNONYM -> {
        Sort newSort = toSort(data.getJsonObject("newSort"));
        Sort oldSort = toSort(data.getJsonObject("oldSort"));
        Att att = toAtt(data.getJsonObject("att"));
        return new SortSynonym(newSort, oldSort, att);
      }
      case KSYNTAXLEXICAL -> {
        String name = data.getString("name");
        String regex = data.getString("regex");
        Att att = toAtt(data.getJsonObject("att"));
        return new SyntaxLexical(name, regex, att);
      }
      case KBUBBLE -> {
        String sentenceType = data.getString("sentenceType");
        String contents = data.getString("contents");
        Att att = toAtt(data.getJsonObject("att"));
        return new Bubble(sentenceType, contents, att);
      }
      case KPRODUCTION -> {
        Option<KLabel> klabel =
            Option.apply(
                data.containsKey("klabel") ? toKLabel(data.getJsonObject("klabel")) : null);
        Sort sort = toSort(data.getJsonObject("sort"));
        Att att = toAtt(data.getJsonObject("att"));

        List<ProductionItem> pItems = new ArrayList<>();
        for (JsonObject pi : data.getJsonArray("productionItems").getValuesAs(JsonObject.class)) {
          pItems.add(toProductionItem(pi));
        }
        List<Sort> params = new ArrayList<>();
        for (JsonObject s : data.getJsonArray("params").getValuesAs(JsonObject.class)) {
          params.add(toSort(s));
        }
        return new Production(klabel, immutable(params), sort, immutable(pItems), att);
      }
      default -> throw KEMException.criticalError(
          "Unexpected node found in KAST Json term: " + data.getString("node"));
    }
  }

  private static scala.collection.immutable.Set<Tag> toTags(JsonArray data) {
    Set<Tag> tags = new HashSet<>();
    data.getValuesAs(JsonString.class).forEach(s -> tags.add(new Tag(s.getString())));
    return immutable(tags);
  }

  private static Sort toSort(JsonObject data) {
    if (!data.getString("node").equals(KSORT))
      throw KEMException.criticalError(
          "Unexpected node found in KAST Json term: " + data.getString("node"));
    return Outer.parseSort(data.getString("name"));
  }

  private static ProductionItem toProductionItem(JsonObject data) {
    switch (data.getString("node")) {
      case KNONTERMINAL -> {
        Sort sort = toSort(data.getJsonObject("sort"));
        Option<String> name =
            Option.apply(data.containsKey("name") ? data.getString("name") : null);
        return new NonTerminal(sort, name);
      }
      case KREGEXTERMINAL -> {
        String precedeRegex = data.getString("precedeRegex");
        String regex = data.getString("regex");
        String followRegex = data.getString("followRegex");
        return new RegexTerminal(precedeRegex, regex, followRegex);
      }
      case KTERMINAL -> {
        String value = data.getString("value");
        return new Terminal(value);
      }
      default -> throw KEMException.criticalError(
          "Unexpected node found in ProductionItem Json term: " + data.getString("node"));
    }
  }

  //////////////////////
  // Parsing Att Json //
  //////////////////////

  public static Att toAtt(JsonObject data) {
    if (!(data.getString("node").equals(KATT) && data.containsKey("att")))
      throw KEMException.criticalError(
          "Unexpected node found in KAST Json term when unparsing KATT: " + data.getString("node"));
    JsonObject attMap = data.getJsonObject("att");
    Att newAtt = Att.empty();
    for (String key : attMap.keySet()) {
      if (key.equals(Att.LOCATION().key())) {
        JsonArray locarr = attMap.getJsonArray(Location.class.getName());
        newAtt =
            newAtt.add(
                Att.LOCATION(),
                Location.class,
                Location(locarr.getInt(0), locarr.getInt(1), locarr.getInt(2), locarr.getInt(3)));
      } else if (key.equals(Att.SOURCE().key())) {
        newAtt = newAtt.add(Att.SOURCE(), Source.class, Source.apply(attMap.getString(key)));
      } else if (key.equals(Att.PRODUCTION().key())) {
        newAtt =
            newAtt.add(
                Att.PRODUCTION(),
                Production.class,
                (Production) toSentence(attMap.getJsonObject(key)));
      } else if (key.equals(Att.SORT().key())) {
        newAtt = newAtt.add(Att.SORT(), Sort.class, toSort(attMap.getJsonObject(key)));
      } else if (key.equals(Att.BRACKET_LABEL().key())) {
        newAtt = newAtt.add(Att.BRACKET_LABEL(), KLabel.class, toKLabel(attMap.getJsonObject(key)));
      } else if (key.equals(Att.PREDICATE().key())) {
        newAtt = newAtt.add(Att.PREDICATE(), Sort.class, toSort(attMap.getJsonObject(key)));
      } else if (key.equals(Att.CELL_OPT_ABSENT().key())) {
        newAtt = newAtt.add(Att.CELL_OPT_ABSENT(), Sort.class, toSort(attMap.getJsonObject(key)));
      } else if (key.equals(Att.CELL_FRAGMENT().key())) {
        newAtt = newAtt.add(Att.CELL_FRAGMENT(), Sort.class, toSort(attMap.getJsonObject(key)));
      } else if (key.equals(Att.SORT_PARAMS().key())) {
        newAtt = newAtt.add(Att.SORT_PARAMS(), Sort.class, toSort(attMap.getJsonObject(key)));
      } else {
        Att.Key attKey =
            Att.getBuiltinKeyOptional(key)
                // The JSON is emitted after we may have added internal attributes
                .or(() -> Att.getInternalKeyOptional(key))
                .orElseThrow(
                    () ->
                        KEMException.criticalError(
                            "Unrecognized attribute "
                                + key
                                + " found in KAST Json term when unparsing KATT: "
                                + attMap));
        newAtt = newAtt.add(attKey, attMap.getString(key));
      }
    }
    return newAtt;
  }

  ////////////////////
  // Parsing K Json //
  ////////////////////

  public static K parse(byte[] data) {
    return parse(new String(data, StandardCharsets.UTF_8));
  }

  public static K parse(String data) {
    JsonReader reader = Json.createReader(new StringReader(data));
    return parseJson(reader.readObject());
  }

  public static K parseJson(JsonObject data) {
    if (!(data.containsKey("format") && data.containsKey("version") && data.containsKey("term"))) {
      throw KEMException.criticalError(
          "Must have `format`, `version`, and `term` fields in serialized Json!");
    }
    if (!data.getString("format").equals("KAST")) {
      throw KEMException.criticalError(
          "Only can deserialize 'KAST' format Json! Found: " + data.getString("format"));
    }
    if (data.getInt("version") != ToJson.version) {
      throw KEMException.criticalError(
          "Only can deserialize KAST version '"
              + ToJson.version
              + "'! Found: "
              + data.getInt("version"));
    }
    return toK(data.getJsonObject("term"));
  }

  private static K toK(JsonObject data) {
    KLabel klabel;

    switch (data.getString("node")) {
      case KTOKEN:
        return KToken(data.getString("token"), toSort(data.getJsonObject("sort")));

      case KAPPLY:
        int arity = data.getInt("arity");
        K[] args = toKs(arity, data.getJsonArray("args"));
        klabel = toKLabel(data.getJsonObject("label"));
        return KApply(klabel, args);

      case KSEQUENCE:
        int seqLen = data.getInt("arity");
        K[] items = toKs(seqLen, data.getJsonArray("items"));
        return KSequence(items);

      case KVARIABLE:
        Att varAtt = Att.empty();
        if (data.containsKey("sort")) {
          varAtt = varAtt.add(Att.SORT(), Sort.class, toSort(data.getJsonObject("sort")));
        }
        return KVariable(data.getString("name"), varAtt);

      case KREWRITE:
        K lhs = toK(data.getJsonObject("lhs"));
        K rhs = toK(data.getJsonObject("rhs"));
        return KRewrite(lhs, rhs, Att.empty());

      case KAS:
        K pattern = toK(data.getJsonObject("pattern"));
        K alias = toK(data.getJsonObject("alias"));
        return KORE.KAs(pattern, alias, Att.empty());

      case INJECTEDKLABEL:
        klabel = toKLabel(data.getJsonObject("label"));
        return InjectedKLabel(klabel);

      default:
        throw KEMException.criticalError(
            "Unexpected node found in KAST Json term: " + data.getString("node"));
    }
  }

  private static KLabel toKLabel(JsonObject data) {
    JsonArray jparams = data.getJsonArray("params");
    List<Sort> params = new ArrayList<>();
    for (JsonValue p : jparams) {
      params.add(toSort((JsonObject) p));
    }
    Sort[] sarray = params.toArray(new Sort[0]);
    return KLabel(data.getString("name"), sarray);
  }

  private static K[] toKs(int arity, JsonArray data) {
    K[] items = new K[arity];
    for (int i = 0; i < arity; i++) {
      items[i] = toK(data.getValuesAs(JsonObject.class).get(i));
    }
    return items;
  }
}
