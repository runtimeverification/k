// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.unparser;

import org.kframework.attributes.Att;
import org.kframework.definition.Associativity;
import org.kframework.definition.Bubble;
import org.kframework.definition.Context;
import org.kframework.definition.Configuration;
import org.kframework.definition.Definition;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Module;
import org.kframework.definition.FlatModule;
import org.kframework.definition.ModuleComment;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.definition.SortSynonym;
import org.kframework.definition.SyntaxAssociativity;
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

import java.io.IOException;
import java.io.OutputStream;
import java.io.DataOutputStream;
import java.io.ByteArrayOutputStream;

import java.util.Map;
import java.util.HashMap;
import java.util.Optional;

import javax.json.Json;
import javax.json.stream.JsonGenerator;
import javax.json.JsonWriterFactory;
import javax.json.JsonArrayBuilder;
import javax.json.JsonObject;
import javax.json.JsonObjectBuilder;
import javax.json.JsonWriter;
import javax.json.JsonStructure;

import scala.Enumeration;
import scala.Option;
import scala.Tuple2;
import scala.collection.JavaConverters;
import scala.collection.Seq;
import scala.collection.Set;

/**
 * Writes a KAST term to the KAST Json format.
 */
public class ToJson {

    private DataOutputStream data;
    private ToJson(DataOutputStream data) {
        this.data = data;
    }

///////////////////////////////
// ToJson Definition Objects //
///////////////////////////////

    public static byte[] apply(Definition def) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        try {
            DataOutputStream data = new DataOutputStream(out);
            JsonWriter jsonWriter = Json.createWriter(data);

            JsonObjectBuilder term = Json.createObjectBuilder();
            term.add("format", "KAST");
            term.add("version", 1);
            term.add("term", toJson(def));

            jsonWriter.write(term.build());
            jsonWriter.close();
            data.close();
        } catch (IOException e) {
            throw KEMException.criticalError("Could not write Definition to Json", e);
        }
        return out.toByteArray();
    }

    public static JsonStructure toJson(Definition def) {
        JsonObjectBuilder jdef = Json.createObjectBuilder();

        JsonArrayBuilder mods = Json.createArrayBuilder();
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
        JsonObjectBuilder jatt = Json.createObjectBuilder();
        jatt.add("node", JsonParser.KATT);

        JsonObjectBuilder jattKeys = Json.createObjectBuilder();
        for (Tuple2<String,String> key: JavaConverters.seqAsJavaList(att.att().keys().toSeq())) {
            jattKeys.add(key._1(), att.att().get(key).get().toString());
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
        JsonObjectBuilder jmod = Json.createObjectBuilder();

        jmod.add("node", JsonParser.KFLATMODULE);

        JsonArrayBuilder imports = Json.createArrayBuilder();
        mod.imports().foreach(i -> imports.add(i));

        JsonArrayBuilder sentences = Json.createArrayBuilder();
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
        if (sen instanceof Context)             return toJson((Context) sen);
        if (sen instanceof Rule)                return toJson((Rule) sen);
        if (sen instanceof ModuleComment)       return toJson((ModuleComment) sen);
        if (sen instanceof SyntaxPriority)      return toJson((SyntaxPriority) sen);
        if (sen instanceof SyntaxAssociativity) return toJson((SyntaxAssociativity) sen);
        if (sen instanceof Configuration)       return toJson((Configuration) sen);
        if (sen instanceof Bubble)              return toJson((Bubble) sen);
        if (sen instanceof SyntaxSort)          return toJson((SyntaxSort) sen);
        if (sen instanceof SortSynonym)         return toJson((SortSynonym) sen);
        if (sen instanceof Production)          return toJson((Production) sen);

        JsonObjectBuilder jsen = Json.createObjectBuilder();
        jsen.add("node", "badsentence");
        return jsen.build();
    }

    public static JsonStructure toJson(Context con) {
        JsonObjectBuilder jcon = Json.createObjectBuilder();

        jcon.add("node", JsonParser.KCONTEXT);
        jcon.add("body", toJson(con.body()));
        jcon.add("requires", toJson(con.requires()));
        jcon.add("att", toJson(con.att()));

        return jcon.build();
    }

    public static JsonStructure toJson(Rule rule) {
        JsonObjectBuilder jrule = Json.createObjectBuilder();

        jrule.add("node", JsonParser.KRULE);
        jrule.add("body", toJson(rule.body()));
        jrule.add("requires", toJson(rule.requires()));
        jrule.add("ensures", toJson(rule.ensures()));
        jrule.add("att", toJson(rule.att()));

        return jrule.build();
    }

    public static JsonStructure toJson(ModuleComment mcom) {
        JsonObjectBuilder jmcom = Json.createObjectBuilder();

        jmcom.add("node", JsonParser.KMODULECOMMENT);
        jmcom.add("comment", mcom.comment());
        jmcom.add("att", toJson(mcom.att()));

        return jmcom.build();
    }

    public static JsonStructure toJson(SyntaxPriority syn) {
        JsonObjectBuilder jsyn = Json.createObjectBuilder();

        jsyn.add("node", JsonParser.KSYNTAXPRIORITY);

        JsonArrayBuilder priArray = Json.createArrayBuilder();
        for (Set<Tag> pri : JavaConverters.seqAsJavaList(syn.priorities())) {
            JsonArrayBuilder tagArray = Json.createArrayBuilder();
            pri.foreach(t -> tagArray.add(t.name()));
            priArray.add(tagArray);
        }
        jsyn.add("priorities", priArray);

        jsyn.add("att", toJson(syn.att()));

        return jsyn.build();
    }

    public static JsonStructure toJson(SyntaxAssociativity syn) {
        JsonObjectBuilder jsyn = Json.createObjectBuilder();

        jsyn.add("node", JsonParser.KSYNTAXASSOCIATIVITY);
        jsyn.add("assoc", syn.assoc().toString());

        JsonArrayBuilder tagArray = Json.createArrayBuilder();
        syn.tags().foreach(t -> tagArray.add(t.name()));
        jsyn.add("tags", tagArray);

        jsyn.add("att", toJson(syn.att()));

        return jsyn.build();
    }

    public static JsonStructure toJson(Configuration con) {
        JsonObjectBuilder jcon = Json.createObjectBuilder();

        jcon.add("node", JsonParser.KCONFIGURATION);
        jcon.add("body", toJson(con.body()));
        jcon.add("ensures", toJson(con.ensures()));
        jcon.add("att", toJson(con.att()));

        return jcon.build();
    }

    public static JsonStructure toJson(Bubble bub) {
        JsonObjectBuilder jbub = Json.createObjectBuilder();

        jbub.add("node", JsonParser.KBUBBLE);
        jbub.add("sentenceType", bub.sentenceType());
        jbub.add("contents", bub.contents());
        jbub.add("att", toJson(bub.att()));

        return jbub.build();
    }

    public static JsonStructure toJson(SyntaxSort syn) {
        JsonObjectBuilder jsyn = Json.createObjectBuilder();

        jsyn.add("node", JsonParser.KSYNTAXSORT);
        jsyn.add("sort", toJson(syn.sort()));
        jsyn.add("att", toJson(syn.att()));

        return jsyn.build();
    }

    public static JsonStructure toJson(SortSynonym syn) {
        JsonObjectBuilder jsyn = Json.createObjectBuilder();

        jsyn.add("node", JsonParser.KSORTSYNONYM);
        jsyn.add("newSort", toJson(syn.newSort()));
        jsyn.add("oldSort", toJson(syn.oldSort()));
        jsyn.add("att", toJson(syn.att()));

        return jsyn.build();
    }

    public static JsonStructure toJson(Production pro) {
        JsonObjectBuilder jpro = Json.createObjectBuilder();

        jpro.add("node", JsonParser.KPRODUCTION);

        Option<KLabel> klabel = pro.klabel();
        if (! klabel.isEmpty()) {
            jpro.add("klabel", klabel.get().name());
        }

        JsonArrayBuilder productionItems = Json.createArrayBuilder();
        JavaConverters.seqAsJavaList(pro.items()).forEach(p -> productionItems.add(toJson(p)));
        jpro.add("productionItems", productionItems.build());

        JsonArrayBuilder params = Json.createArrayBuilder();
        JavaConverters.seqAsJavaList(pro.params()).forEach(p -> params.add(toJson(p)));
        jpro.add("params", params.build());

        jpro.add("sort", toJson(pro.sort()));
        jpro.add("att", toJson(pro.att()));

        return jpro.build();
    }

    public static JsonObject toJson(ProductionItem prod) {
        JsonObjectBuilder jsonProduction = Json.createObjectBuilder();

        if (prod instanceof NonTerminal) {
            NonTerminal t = (NonTerminal) prod;
            jsonProduction.add("node", JsonParser.KNONTERMINAL);
            jsonProduction.add("sort", toJson(t.sort()));
            Option<String> name = t.name();
            if (! name.isEmpty())
                jsonProduction.add("name", name.get());
        } else if (prod instanceof RegexTerminal) {
            RegexTerminal t = (RegexTerminal) prod;
            jsonProduction.add("node", JsonParser.KREGEXTERMINAL);
            jsonProduction.add("precedeRegex", t.precedeRegex());
            jsonProduction.add("regex", t.regex());
            jsonProduction.add("followRegex", t.followRegex());
        } else if (prod instanceof Terminal) {
            Terminal t = (Terminal) prod;
            jsonProduction.add("node", JsonParser.KTERMINAL);
            jsonProduction.add("value", t.value());
        }

        return jsonProduction.build();
    }

    public static JsonStructure toJson(Sort sort) {
        JsonObjectBuilder jsort = Json.createObjectBuilder();

        jsort.add("node", JsonParser.KSORT);
        jsort.add("name", sort.name());

        return jsort.build();
    }

//////////////////////
// ToJson K Objects //
//////////////////////

    public static void apply(OutputStream out, K k) {
        try {
            DataOutputStream data = new DataOutputStream(out);
            JsonWriter jsonWriter = Json.createWriter(data);

            JsonObjectBuilder kterm = Json.createObjectBuilder();
            kterm.add("format", "KAST");
            kterm.add("version", 1);
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

    private static JsonStructure toJson(K k) {
        JsonObjectBuilder knode = Json.createObjectBuilder();
        if (k instanceof KToken) {
            KToken tok = (KToken) k;

            knode.add("node", JsonParser.KTOKEN);
            knode.add("sort", tok.sort().toString());
            knode.add("token", tok.s());

        } else if (k instanceof KApply) {
            KApply app = (KApply) k;

            knode.add("node", JsonParser.KAPPLY);
            knode.add("label", app.klabel().name());
            knode.add("variable", app.klabel() instanceof KVariable);

            JsonArrayBuilder args = Json.createArrayBuilder();
            for (K item : app.klist().asIterable()) {
                args.add(toJson(item));
            }

            knode.add("arity", app.klist().size());
            knode.add("args", args.build());

        } else if (k instanceof KSequence) {
            KSequence seq = (KSequence) k;

            knode.add("node", JsonParser.KSEQUENCE);

            JsonArrayBuilder items = Json.createArrayBuilder();
            for (K item : seq.asIterable()) {
                items.add(toJson(item));
            }

            knode.add("arity", seq.size());
            knode.add("items", items.build());

        } else if (k instanceof KVariable) {
            KVariable var = (KVariable) k;

            knode.add("node", JsonParser.KVARIABLE);
            knode.add("name", var.name());
            Optional<String> origName = var.att().getOptional("originalName");
            if (origName.isPresent()) {
                knode.add("originalName", origName.get());
            } else {
                knode.add("originalName", var.name());
            }

        } else if (k instanceof KRewrite) {
            KRewrite rew = (KRewrite) k;

            knode.add("node", JsonParser.KREWRITE);
            knode.add("lhs", toJson(rew.left()));
            knode.add("rhs", toJson(rew.right()));
            knode.add("att", rew.att().toString());

        } else if (k instanceof KAs) {
            KAs alias = (KAs) k;

            knode.add("node", JsonParser.KAS);
            knode.add("pattern", toJson(alias.pattern()));
            knode.add("alias",   toJson(alias.alias()));
            knode.add("att", alias.att().toString());

        } else if (k instanceof InjectedKLabel) {
            InjectedKLabel inj = (InjectedKLabel) k;

            knode.add("node", JsonParser.INJECTEDKLABEL);
            knode.add("name", inj.klabel().name());
            knode.add("variable", inj.klabel() instanceof KVariable);

        } else {
            throw KEMException.criticalError("Unimplemented for JSON serialization: ", k);
        }
        return knode.build();
    }
}
