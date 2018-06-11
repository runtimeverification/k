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
