// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.unparser;

import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.parser.json.JsonParser;
import org.kframework.utils.errorsystem.KEMException;

import java.io.IOException;
import java.io.OutputStream;
import java.io.DataOutputStream;
import java.io.ByteArrayOutputStream;

import java.util.Map;
import java.util.HashMap;

import javax.json.Json;
import javax.json.stream.JsonGenerator;
import javax.json.JsonWriterFactory;
import javax.json.JsonArrayBuilder;
import javax.json.JsonObject;
import javax.json.JsonObjectBuilder;
import javax.json.JsonWriter;
import javax.json.JsonStructure;

/**
 * Writes a KAST term to the KAST Json format.
 */
public class ToJson {

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

    private DataOutputStream data;
    private ToJson(DataOutputStream data) {
        this.data = data;
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

        } else if (k instanceof KRewrite) {
            KRewrite rew = (KRewrite) k;

            knode.add("node", JsonParser.KREWRITE);
            knode.add("lhs", toJson(rew.left()));
            knode.add("rhs", toJson(rew.right()));
            knode.add("att", rew.att().toString());

        } else if (k instanceof InjectedKLabel) {
            InjectedKLabel inj = (InjectedKLabel) k;

            knode.add("node", JsonParser.INJECTEDKLABEL);
            knode.add("name", inj.klabel().name());

        }
        return knode.build();
    }
}
