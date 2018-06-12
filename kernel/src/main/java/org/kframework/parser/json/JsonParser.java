// Copyright (c) 2018 K Team. All Rights Reserved.
package org.kframework.parser.json;

import org.kframework.kore.K;
import static org.kframework.kore.KORE.KLabel;
import org.kframework.kore.mini.InjectedKLabel;
import org.kframework.kore.mini.KApply;
import org.kframework.kore.mini.KRewrite;
import org.kframework.kore.mini.KSequence;
import org.kframework.kore.mini.KToken;
import org.kframework.kore.mini.KVariable;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;

import java.io.IOException;
import java.util.Arrays;

import javax.json.Json;
import javax.json.JsonObject;
import javax.json.JsonArray;

/**
 * Parses a Json term into the KORE data structures.
 */
public class JsonParser {

    public static final String KTOKEN         = "KToken"
                             , KAPPLY         = "KApply"
                             , KSEQUENCE      = "KSequence"
                             , KVARIABLE      = "KVariable"
                             , KREWRITE       = "KRewrite"
                             , INJECTEDKLABEL = "InjectedKLabel"
                             ;

    public static K parseJson(JsonObject data) {
        try {
            if (! (data.containsKey("format") && data.containsKey("version") && data.containsKey("term"))) {
                throw KEMException.criticalError("Must have `format`, `version`, and `term` fields in serialized Json!");
            }
            if (data.getString("format") != "KAST") {
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
        switch (data.getString("node")) {

            case KTOKEN:
                return new KToken(data.getString("name"), Outer.parseSort(data.getString("sort")));

            case KAPPLY:
                int arity = data.getInt("arity");
                K[] args  = toKs(arity, data.getJsonArray("args"));
                return KApply.of(KLabel(data.getString("label")), args);

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

            case INJECTEDKLABEL:
                return new InjectedKLabel(KLabel(data.getString("name")));

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
