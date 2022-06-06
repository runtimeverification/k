// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.parser.json;

import junit.framework.Assert;
import org.junit.Test;
import org.kframework.kore.K;
import org.kframework.unparser.ToJson;

import javax.json.Json;
import javax.json.JsonObjectBuilder;
import javax.json.JsonStructure;

import static org.kframework.kore.KORE.*;

public class JsonSerializationTests {

    @Test
    public void test1() {
        K k = KApply(KLabel("#ruleNoConditions"),KApply(KLabel("#KRewrite"),
                KApply(KLabel("tuplee"),
                        KApply(KLabel("#SemanticCastToE"), KToken("A",Sort("#KVariable"))),
                        KApply(KLabel("#SemanticCastToE"), KToken("B",Sort("#KVariable"))),
                        KApply(KLabel("#SemanticCastToS"), KToken("C",Sort("#KVariable")))),
                KApply(KLabel("#SemanticCastToS"), KToken("C",Sort("#KVariable")))
        ));

        JsonStructure js = ToJson.toJson(k);
        JsonObjectBuilder term = Json.createObjectBuilder();
        term.add("format", "KAST");
        term.add("version", ToJson.version);
        term.add("term", js);
        K k2 = JsonParser.parseJson(term.build());
        Assert.assertEquals(k, k2);
    }

    @Test
    public void test2() {
        K k = KApply(KLabel("#ruleNoConditions", Sort("X", Sort("6"), Sort("Z"))),KApply(KLabel("#KRewrite", Sort("P")),
                KApply(KLabel("tuplee"),
                        KApply(KLabel("#SemanticCastToE"), KToken("A",Sort("#KVariable"))),
                        KApply(KLabel("#SemanticCastToE"), KToken("B",Sort("#KVariable"))),
                        KApply(KLabel("#SemanticCastToS"), KToken("C",Sort("#KVariable")))),
                KApply(KLabel("#SemanticCastToS"), KToken("C",Sort("#KVariable")))
        ));

        JsonStructure js = ToJson.toJson(k);
        JsonObjectBuilder term = Json.createObjectBuilder();
        term.add("format", "KAST");
        term.add("version", ToJson.version);
        term.add("term", js);
        K k2 = JsonParser.parseJson(term.build());
        Assert.assertEquals(k, k2);
    }
}
