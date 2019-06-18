// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.parser.json;

import org.kframework.attributes.Att;
import org.kframework.definition.Context;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleComment;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import static org.kframework.kore.KORE.KLabel;
import org.kframework.kore.KORE;
import org.kframework.kore.mini.InjectedKLabel;
import org.kframework.kore.mini.KApply;
import org.kframework.kore.mini.KRewrite;
import org.kframework.kore.mini.KSequence;
import org.kframework.kore.mini.KToken;
import org.kframework.kore.mini.KVariable;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;

import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.io.StringReader;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import javax.json.Json;
import javax.json.JsonArray;
import javax.json.JsonObject;
import javax.json.JsonReader;

import scala.collection.JavaConverters;

/**
 * Parses a Json term into the KORE data structures.
 */
public class JsonParser {

    public static final String KDEFINITION          = "KDefinition"
                             , KATT                 = "KAtt"
                             , KCONFIGURATION       = "KConfiguration"
                             , KBUBBLE              = "KBubble"
                             , KMODULE              = "KModule"
                             , KCONTEXT             = "KContext"
                             , KRULE                = "KRule"
                             , KMODULECOMMENT       = "KModuleComment"
                             , KSYNTAXPRIORITY      = "KSyntaxPriority"
                             , KSYNTAXASSOCIATIVITY = "KSyntaxAssociativity"
                             , KTOKEN               = "KToken"
                             , KSYNTAXSORT          = "KSyntaxSort"
                             , KPRODUCTION          = "KProduction"
                             , KAPPLY               = "KApply"
                             , KSEQUENCE            = "KSequence"
                             , KVARIABLE            = "KVariable"
                             , KREWRITE             = "KRewrite"
                             , KAS                  = "KAs"
                             , INJECTEDKLABEL       = "InjectedKLabel"
                             ;

/////////////////////////////
// Parsing Definition Json //
/////////////////////////////

    public static Definition parseDef(byte[] data) {
        try {
            return parseDef(new String(data, "UTF-8"));
        } catch (UnsupportedEncodingException e) {
            throw new AssertionError("UTF-8 encoding not supported");
        }
    }

    public static Definition parseDef(String data) {
        JsonReader reader = Json.createReader(new StringReader(data));
        return parseJsonDef(reader.readObject());
    }

    public static Definition parseJsonDef(JsonObject data) {
        try {
            if (! (data.containsKey("format") && data.containsKey("version") && data.containsKey("term"))) {
                throw KEMException.criticalError("Must have `format`, `version`, and `term` fields in serialized Json!");
            }
            if (! data.getString("format").equals("KAST")) {
                throw KEMException.criticalError("Only can deserialize 'KAST' format Json! Found: " + data.getString("format"));
            }
            if (data.getInt("version") != 1) {
                throw KEMException.criticalError("Only can deserialize KAST version '1'! Found: " + data.getInt("version"));
            }
            return toDef(data.getJsonObject("term"));
        } catch (IOException e) {
            throw KEMException.criticalError("Could not read Definition term from json", e);
        }
    }

    public static Definition toDef(JsonObject data) throws IOException {
        if (! data.getString("node").equals(KDEFINITION))
            throw KEMException.criticalError("Unexpected node found in KAST Json term: " + data.getString("node"));

        Module mainModule = toMod(data.getJsonObject("mainModule"));
        JsonArray mods = data.getJsonArray("entryModules");
        Module[] modArray = toMods(mods.size(), mods);
        Set<Module> entryModules = new HashSet<>(Arrays.asList(modArray));
        return new Definition(mainModule, JavaConverters.asScalaSet(entryModules), toAtt(data.getJsonObject("att")));
    }

/////////////////////////
// Parsing Module Json //
/////////////////////////

    public static Module toMod(JsonObject data) throws IOException {
        if (! data.getString("node").equals(KMODULE))
            throw KEMException.criticalError("Unexpected node found in KAST Json term: " + data.getString("node"));

        String name = data.getString("name");

        JsonArray mods = data.getJsonArray("imports");
        Module[] modArray = toMods(mods.size(), mods);
        Set<Module> modImports = new HashSet<>(Arrays.asList(modArray));

        JsonArray sens = data.getJsonArray("localSentences");
        Sentence[] senArray = toSens(sens.size(), sens);
        Set<Sentence> localSentences = new HashSet<>(Arrays.asList(senArray));

        return new Module(name, JavaConverters.asScalaSet(modImports), JavaConverters.asScalaSet(localSentences), toAtt(data.getJsonObject("att")));
    }

    private static Module[] toMods(int arity, JsonArray data) throws IOException {
        Module[] items = new Module[arity];
        for (int i = 0; i < arity; i++) {
            items[i] = toMod(data.getValuesAs(JsonObject.class).get(i));
        }
        return items;
    }

///////////////////////////
// Parsing Sentence Json //
///////////////////////////

    public static Sentence toSen(JsonObject data) throws IOException {
        switch(data.getString("node")) {
            case KCONTEXT: {
                K body = toK(data.getJsonObject("body"));
                K requires = toK(data.getJsonObject("requires"));
                Att att = toAtt(data.getJsonObject("att"));
                return new Context(body, requires, att);
            }
            case KRULE: {
                K body = toK(data.getJsonObject("body"));
                K requires = toK(data.getJsonObject("requires"));
                K ensures = toK(data.getJsonObject("ensures"));
                Att att = toAtt(data.getJsonObject("att"));
                return new Rule(body, requires, ensures, att);
            }
            case KMODULECOMMENT:{
                String comment = data.getString("comment");
                Att att = toAtt(data.getJsonObject("att"));
                return new ModuleComment(comment, att);
            }
            case KSYNTAXPRIORITY: {
                
            }
            case KSYNTAXASSOCIATIVITY: {
                
            }
            default:
                throw KEMException.criticalError("Unexpected node found in KAST Json term: " + data.getString("node"));
        }
    }

    private static Sentence[] toSens(int arity, JsonArray data) throws IOException {
        Sentence[] items = new Sentence[arity];
        for (int i = 0; i < arity; i++) {
            items[i] = toSen(data.getValuesAs(JsonObject.class).get(i));
        }
        return items;
    }

//////////////////////
// Parsing Att Json //
//////////////////////

    public static Att toAtt(JsonObject data) throws IOException {
        if (! data.getString("node").equals(KATT))
            throw KEMException.criticalError("Unexpected node found in KAST Json term: " + data.getString("node"));

        return Att.empty();
    }

////////////////////
// Parsing K Json //
////////////////////

    public static K parse(byte[] data) {
        try {
            return parse(new String(data, "UTF-8"));
        } catch (UnsupportedEncodingException e) {
            throw new AssertionError("UTF-8 encoding not supported");
        }
    }

    public static K parse(String data) {
        JsonReader reader = Json.createReader(new StringReader(data));
        return parseJson(reader.readObject());
    }

    public static K parseJson(JsonObject data) {
        try {
            if (! (data.containsKey("format") && data.containsKey("version") && data.containsKey("term"))) {
                throw KEMException.criticalError("Must have `format`, `version`, and `term` fields in serialized Json!");
            }
            if (! data.getString("format").equals("KAST")) {
                throw KEMException.criticalError("Only can deserialize 'KAST' format Json! Found: " + data.getString("format"));
            }
            if (data.getInt("version") != 1) {
                throw KEMException.criticalError("Only can deserialize KAST version '1'! Found: " + data.getInt("version"));
            }
            return toK(data.getJsonObject("term"));
        } catch (IOException e) {
            throw KEMException.criticalError("Could not read K term from json", e);
        }
    }

    private static K toK(JsonObject data) throws IOException {
        String label;
        KLabel klabel;

        switch (data.getString("node")) {

            case KTOKEN:
                return new KToken(data.getString("token"), Outer.parseSort(data.getString("sort")));

            case KAPPLY:
                int arity = data.getInt("arity");
                K[] args  = toKs(arity, data.getJsonArray("args"));
                label     = data.getString("label");
                klabel    = data.getBoolean("variable")
                          ? new KVariable(label)
                          : KLabel(label);
                return KApply.of(klabel, args);

            case KSEQUENCE:
                int seqLen = data.getInt("arity");
                K[] items  = toKs(seqLen, data.getJsonArray("items"));
                return new KSequence(items);

            case KVARIABLE:
                return new KVariable(data.getString("name"));

            case KREWRITE:
                K lhs = toK(data.getJsonObject("lhs"));
                K rhs = toK(data.getJsonObject("rhs"));
                return new KRewrite(lhs, rhs);

            case KAS:
                K pattern = toK(data.getJsonObject("pattern"));
                K alias   = toK(data.getJsonObject("alias"));
                return KORE.KAs(pattern, alias);

            case INJECTEDKLABEL:
                label  = data.getString("name");
                klabel = data.getBoolean("variable")
                       ? new KVariable(label)
                       : KLabel(label);
                return new InjectedKLabel(klabel);

            default:
                throw KEMException.criticalError("Unexpected node found in KAST Json term: " + data.getString("node"));
        }
    }

    private static K[] toKs(int arity, JsonArray data) throws IOException {
        K[] items = new K[arity];
        for (int i = 0; i < arity; i++) {
            items[i] = toK(data.getValuesAs(JsonObject.class).get(i));
        }
        return items;
    }
}
