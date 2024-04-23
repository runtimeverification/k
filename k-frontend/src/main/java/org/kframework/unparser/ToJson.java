// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.unparser;

import static org.kframework.Collections.*;

import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Collections;
import javax.json.*;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.definition.Bubble;
import org.kframework.definition.Configuration;
import org.kframework.definition.Context;
import org.kframework.definition.Definition;
import org.kframework.definition.FlatModule;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.Rule;
import org.kframework.definition.RuleOrClaim;
import org.kframework.definition.Sentence;
import org.kframework.definition.SortSynonym;
import org.kframework.definition.SyntaxAssociativity;
import org.kframework.definition.SyntaxLexical;
import org.kframework.definition.SyntaxPriority;
import org.kframework.definition.SyntaxSort;
import org.kframework.definition.Tag;
import org.kframework.definition.Terminal;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.parser.json.JsonParser;
import org.kframework.utils.errorsystem.KEMException;
import scala.Option;
import scala.Tuple2;
import scala.collection.JavaConverters;
import scala.collection.Set;

/** Writes a KAST term to the KAST Json format. */
public class ToJson {

  public static final int version = 3;

  ///////////////////////////////
  // ToJson Definition Objects //
  ///////////////////////////////

  private static final JsonBuilderFactory factory =
      Json.createBuilderFactory(Collections.emptyMap());

  public static byte[] apply(Definition def) {
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    try {
      DataOutputStream data = new DataOutputStream(out);
      JsonWriter jsonWriter = Json.createWriter(data);

      JsonObjectBuilder term = factory.createObjectBuilder();
      term.add("format", "KAST");
      term.add("version", version);
      term.add("term", toJson(def));

      jsonWriter.write(term.build());
      jsonWriter.close();
      data.close();
    } catch (IOException e) {
      throw KEMException.criticalError("Could not write Definition to Json", e);
    }
    return out.toByteArray();
  }

  public static byte[] apply(java.util.Set<Module> mods, String mainSpecModule) {
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    try {
      DataOutputStream data = new DataOutputStream(out);
      JsonWriter jsonWriter = Json.createWriter(data);

      JsonObjectBuilder term = factory.createObjectBuilder();
      term.add("format", "KAST");
      term.add("version", version);
      JsonObjectBuilder jmodlist = factory.createObjectBuilder();

      jmodlist.add("node", JsonParser.KFLATMODULELIST);
      jmodlist.add("mainModule", mainSpecModule);

      JsonArrayBuilder jmods = factory.createArrayBuilder();
      for (Module m : mods) {
        jmods.add(toJson(m));
      }
      jmodlist.add("term", jmods);
      term.add("term", jmodlist);

      jsonWriter.write(term.build());
      jsonWriter.close();
      data.close();
    } catch (IOException e) {
      throw KEMException.criticalError("Could not write Module to Json", e);
    }
    return out.toByteArray();
  }

  public static JsonStructure toJson(Definition def) {
    JsonObjectBuilder jdef = factory.createObjectBuilder();

    JsonArrayBuilder mods = factory.createArrayBuilder();
    for (Module m : JavaConverters.setAsJavaSet(def.modules())) {
      mods.add(toJson(m));
    }

    jdef.add("node", JsonParser.KDEFINITION);
    jdef.add("mainModule", def.mainModule().name());
    jdef.add("modules", mods);
    jdef.add("att", toJson(def.att()));

    return jdef.build();
  }

  public static JsonStructure toJson(Att att) {
    JsonObjectBuilder jatt = factory.createObjectBuilder();
    jatt.add("node", JsonParser.KATT);

    JsonObjectBuilder jattKeys = factory.createObjectBuilder();
    for (Tuple2<Att.Key, String> attKeyPair : iterable(att.att().keys())) {
      if (attKeyPair._1().key().equals(Location.class.getName())) {
        JsonArrayBuilder locarr = factory.createArrayBuilder();
        Location loc = att.get(Att.LOCATION(), Location.class);
        locarr.add(loc.startLine());
        locarr.add(loc.startColumn());
        locarr.add(loc.endLine());
        locarr.add(loc.endColumn());
        jattKeys.add(attKeyPair._1().key(), locarr.build());
      } else if (attKeyPair._1().key().equals(Source.class.getName())) {
        jattKeys.add(attKeyPair._1().key(), att.get(Att.SOURCE(), Source.class).source());
      } else if (attKeyPair._1().key().equals(Production.class.getName())) {
        jattKeys.add(attKeyPair._1().key(), toJson(att.get(Att.PRODUCTION(), Production.class)));
      } else if (attKeyPair._1().key().equals(Sort.class.getName())) {
        jattKeys.add(attKeyPair._1().key(), toJson(att.get(Att.SORT(), Sort.class)));
      } else if (attKeyPair._1().equals(Att.BRACKET_LABEL())) {
        jattKeys.add(attKeyPair._1().key(), toJson(att.get(Att.BRACKET_LABEL(), KLabel.class)));
      } else if (attKeyPair._1().equals(Att.PREDICATE())) {
        jattKeys.add(attKeyPair._1().key(), toJson(att.get(Att.PREDICATE(), Sort.class)));
      } else if (attKeyPair._1().equals(Att.CELL_OPT_ABSENT())) {
        jattKeys.add(attKeyPair._1().key(), toJson(att.get(Att.CELL_OPT_ABSENT(), Sort.class)));
      } else if (attKeyPair._1().equals(Att.CELL_FRAGMENT())) {
        jattKeys.add(attKeyPair._1().key(), toJson(att.get(Att.CELL_FRAGMENT(), Sort.class)));
      } else if (attKeyPair._1().equals(Att.SORT_PARAMS())) {
        jattKeys.add(attKeyPair._1().key(), toJson(att.get(Att.SORT_PARAMS(), Sort.class)));
      } else jattKeys.add(attKeyPair._1().key(), att.att().get(attKeyPair).get().toString());
    }
    jatt.add("att", jattKeys.build());

    return jatt.build();
  }

  ///////////////////////////
  // ToJson Module Objects //
  ///////////////////////////

  public static JsonStructure toJson(Module mod) {
    return toJson(mod.flattened());
  }

  public static JsonStructure toJson(FlatModule mod) {
    JsonObjectBuilder jmod = factory.createObjectBuilder();

    jmod.add("node", JsonParser.KFLATMODULE);

    JsonArrayBuilder imports = factory.createArrayBuilder();
    stream(mod.imports())
        .forEach(
            i -> {
              JsonObjectBuilder jimp = factory.createObjectBuilder();
              jimp.add("node", JsonParser.KIMPORT);
              jimp.add("name", i.name());
              jimp.add("isPublic", i.isPublic());
              imports.add(jimp.build());
            });

    JsonArrayBuilder sentences = factory.createArrayBuilder();
    mod.localSentences().foreach(s -> sentences.add(toJson(s)));

    jmod.add("name", mod.name());
    jmod.add("imports", imports);
    jmod.add("localSentences", sentences);
    jmod.add("att", toJson(mod.att()));

    return jmod.build();
  }

  /////////////////////////////
  // ToJSon Sentence Objects //
  /////////////////////////////

  public static JsonStructure toJson(Sentence sen) {
    if (sen instanceof Context) return toJson((Context) sen);
    if (sen instanceof RuleOrClaim) return toJson((RuleOrClaim) sen);
    if (sen instanceof SyntaxPriority) return toJson((SyntaxPriority) sen);
    if (sen instanceof SyntaxAssociativity) return toJson((SyntaxAssociativity) sen);
    if (sen instanceof Configuration) return toJson((Configuration) sen);
    if (sen instanceof Bubble) return toJson((Bubble) sen);
    if (sen instanceof SyntaxSort) return toJson((SyntaxSort) sen);
    if (sen instanceof SortSynonym) return toJson((SortSynonym) sen);
    if (sen instanceof SyntaxLexical) return toJson((SyntaxLexical) sen);
    if (sen instanceof Production) return toJson((Production) sen);

    JsonObjectBuilder jsen = factory.createObjectBuilder();
    jsen.add("node", "badsentence");
    return jsen.build();
  }

  public static JsonStructure toJson(Context con) {
    JsonObjectBuilder jcon = factory.createObjectBuilder();

    jcon.add("node", JsonParser.KCONTEXT);
    jcon.add("body", toJson(con.body()));
    jcon.add("requires", toJson(con.requires()));
    jcon.add("att", toJson(con.att()));

    return jcon.build();
  }

  public static JsonStructure toJson(RuleOrClaim rule) {
    JsonObjectBuilder jrule = factory.createObjectBuilder();

    jrule.add("node", rule instanceof Rule ? JsonParser.KRULE : JsonParser.KCLAIM);
    jrule.add("body", toJson(rule.body()));
    jrule.add("requires", toJson(rule.requires()));
    jrule.add("ensures", toJson(rule.ensures()));
    jrule.add("att", toJson(rule.att()));

    return jrule.build();
  }

  public static JsonStructure toJson(SyntaxPriority syn) {
    JsonObjectBuilder jsyn = factory.createObjectBuilder();

    jsyn.add("node", JsonParser.KSYNTAXPRIORITY);

    JsonArrayBuilder priArray = factory.createArrayBuilder();
    for (Set<Tag> pri : JavaConverters.seqAsJavaList(syn.priorities())) {
      JsonArrayBuilder tagArray = factory.createArrayBuilder();
      pri.foreach(t -> tagArray.add(t.name()));
      priArray.add(tagArray);
    }
    jsyn.add("priorities", priArray);

    jsyn.add("att", toJson(syn.att()));

    return jsyn.build();
  }

  public static JsonStructure toJson(SyntaxAssociativity syn) {
    JsonObjectBuilder jsyn = factory.createObjectBuilder();

    jsyn.add("node", JsonParser.KSYNTAXASSOCIATIVITY);
    jsyn.add("assoc", syn.assoc().toString());

    JsonArrayBuilder tagArray = factory.createArrayBuilder();
    syn.tags().foreach(t -> tagArray.add(t.name()));
    jsyn.add("tags", tagArray);

    jsyn.add("att", toJson(syn.att()));

    return jsyn.build();
  }

  public static JsonStructure toJson(Configuration con) {
    JsonObjectBuilder jcon = factory.createObjectBuilder();

    jcon.add("node", JsonParser.KCONFIGURATION);
    jcon.add("body", toJson(con.body()));
    jcon.add("ensures", toJson(con.ensures()));
    jcon.add("att", toJson(con.att()));

    return jcon.build();
  }

  public static JsonStructure toJson(Bubble bub) {
    JsonObjectBuilder jbub = factory.createObjectBuilder();

    jbub.add("node", JsonParser.KBUBBLE);
    jbub.add("sentenceType", bub.sentenceType());
    jbub.add("contents", bub.contents());
    jbub.add("att", toJson(bub.att()));

    return jbub.build();
  }

  public static JsonStructure toJson(SyntaxSort syn) {
    JsonObjectBuilder jsyn = factory.createObjectBuilder();

    jsyn.add("node", JsonParser.KSYNTAXSORT);
    jsyn.add("sort", toJson(syn.sort()));

    JsonArrayBuilder params = factory.createArrayBuilder();
    JavaConverters.seqAsJavaList(syn.params()).forEach(p -> params.add(toJson(p)));
    jsyn.add("params", params.build());

    jsyn.add("att", toJson(syn.att()));

    return jsyn.build();
  }

  public static JsonStructure toJson(SortSynonym syn) {
    JsonObjectBuilder jsyn = factory.createObjectBuilder();

    jsyn.add("node", JsonParser.KSORTSYNONYM);
    jsyn.add("newSort", toJson(syn.newSort()));
    jsyn.add("oldSort", toJson(syn.oldSort()));
    jsyn.add("att", toJson(syn.att()));

    return jsyn.build();
  }

  public static JsonStructure toJson(SyntaxLexical syn) {
    JsonObjectBuilder jsyn = factory.createObjectBuilder();

    jsyn.add("node", JsonParser.KSYNTAXLEXICAL);
    jsyn.add("name", syn.name());
    jsyn.add("regex", syn.regex());
    jsyn.add("att", toJson(syn.att()));

    return jsyn.build();
  }

  public static JsonStructure toJson(Production pro) {
    JsonObjectBuilder jpro = factory.createObjectBuilder();

    jpro.add("node", JsonParser.KPRODUCTION);

    Option<KLabel> klabel = pro.klabel();
    if (!klabel.isEmpty()) {
      jpro.add("klabel", toJson(klabel.get()));
    }

    JsonArrayBuilder productionItems = factory.createArrayBuilder();
    JavaConverters.seqAsJavaList(pro.items()).forEach(p -> productionItems.add(toJson(p)));
    jpro.add("productionItems", productionItems.build());

    JsonArrayBuilder params = factory.createArrayBuilder();
    JavaConverters.seqAsJavaList(pro.params()).forEach(p -> params.add(toJson(p)));
    jpro.add("params", params.build());

    jpro.add("sort", toJson(pro.sort()));
    jpro.add("att", toJson(pro.att()));

    return jpro.build();
  }

  public static JsonObject toJson(ProductionItem prod) {
    JsonObjectBuilder jsonProduction = factory.createObjectBuilder();

    if (prod instanceof NonTerminal t) {
      jsonProduction.add("node", JsonParser.KNONTERMINAL);
      jsonProduction.add("sort", toJson(t.sort()));
      Option<String> name = t.name();
      if (!name.isEmpty()) jsonProduction.add("name", name.get());
    } else if (prod instanceof RegexTerminal t) {
      jsonProduction.add("node", JsonParser.KREGEXTERMINAL);
      jsonProduction.add("precedeRegex", t.precedeRegex());
      jsonProduction.add("regex", t.regex());
      jsonProduction.add("followRegex", t.followRegex());
    } else if (prod instanceof Terminal t) {
      jsonProduction.add("node", JsonParser.KTERMINAL);
      jsonProduction.add("value", t.value());
    }

    return jsonProduction.build();
  }

  public static JsonStructure toJson(Sort sort) {
    JsonObjectBuilder jsort = factory.createObjectBuilder();

    jsort.add("node", JsonParser.KSORT);
    // store sort and its parameters as a flat string
    jsort.add("name", sort.toString());

    return jsort.build();
  }

  //////////////////////
  // ToJson K Objects //
  //////////////////////

  public static void apply(OutputStream out, K k) {
    try {
      DataOutputStream data = new DataOutputStream(out);
      JsonWriter jsonWriter = Json.createWriter(data);

      JsonObjectBuilder kterm = factory.createObjectBuilder();
      kterm.add("format", "KAST");
      kterm.add("version", version);
      kterm.add("term", toJson(k));

      jsonWriter.write(kterm.build());
      jsonWriter.close();
      data.close();
    } catch (IOException e) {
      throw KEMException.criticalError("Could not write K term to Json", e, k);
    }
  }

  public static byte[] apply(K k) {
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    apply(out, k);
    return out.toByteArray();
  }

  public static JsonStructure toJson(K k) {
    JsonObjectBuilder knode = factory.createObjectBuilder();
    if (k instanceof KToken tok) {

      knode.add("node", JsonParser.KTOKEN);
      knode.add("sort", toJson(tok.sort()));
      knode.add("token", tok.s());

    } else if (k instanceof KApply app) {

      knode.add("node", JsonParser.KAPPLY);
      knode.add("label", toJson(((KApply) k).klabel()));

      JsonArrayBuilder args = factory.createArrayBuilder();
      for (K item : app.klist().asIterable()) {
        args.add(toJson(item));
      }

      knode.add("arity", app.klist().size());
      knode.add("args", args.build());

    } else if (k instanceof KSequence seq) {

      knode.add("node", JsonParser.KSEQUENCE);

      JsonArrayBuilder items = factory.createArrayBuilder();
      for (K item : seq.asIterable()) {
        items.add(toJson(item));
      }

      knode.add("arity", seq.size());
      knode.add("items", items.build());

    } else if (k instanceof KVariable var) {

      knode.add("node", JsonParser.KVARIABLE);
      knode.add("name", var.name());
      if (k.att().contains(Att.SORT(), Sort.class)) {
        knode.add("sort", toJson(k.att().get(Att.SORT(), Sort.class)));
      }

    } else if (k instanceof KRewrite rew) {

      knode.add("node", JsonParser.KREWRITE);
      knode.add("lhs", toJson(rew.left()));
      knode.add("rhs", toJson(rew.right()));

    } else if (k instanceof KAs alias) {

      knode.add("node", JsonParser.KAS);
      knode.add("pattern", toJson(alias.pattern()));
      knode.add("alias", toJson(alias.alias()));

    } else if (k instanceof InjectedKLabel inj) {

      knode.add("node", JsonParser.INJECTEDKLABEL);
      knode.add("label", toJson(inj.klabel()));

    } else {
      throw KEMException.criticalError("Unimplemented for JSON serialization: ", k);
    }
    return knode.build();
  }

  public static JsonStructure toJson(KLabel kl) {
    JsonObjectBuilder jkl = factory.createObjectBuilder();
    jkl.add("node", "KLabel");
    jkl.add("name", kl.name());
    JsonArrayBuilder params = factory.createArrayBuilder();
    for (Sort s : mutable(kl.params())) params.add(toJson(s));
    jkl.add("params", params.build());
    return jkl.build();
  }
}
