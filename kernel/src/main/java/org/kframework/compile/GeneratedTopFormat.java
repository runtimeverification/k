// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Sentence;
import scala.collection.Set;
import scala.collection.JavaConverters;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;

public class GeneratedTopFormat {

    private static Production resolve(Production prod) {
        if (prod.klabel().isDefined() && prod.klabel().get().equals(KLabels.GENERATED_TOP_CELL)) {
            List<Integer> cellPositions = new ArrayList<Integer>();
            int i = 1;
            for (ProductionItem p: JavaConverters.seqAsJavaList(prod.items())) {
                if (p instanceof NonTerminal) {
                    NonTerminal nt = (NonTerminal) p;
                    if (! nt.sort().equals(Sorts.GeneratedCounterCell())) {
                        cellPositions.add(i);
                    }
                }
                i++;
            }
            StringBuilder format = new StringBuilder();
            if (cellPositions.size() == 1) {
                format.append("%").append(cellPositions.get(0));
            } else {
                format.append("%1%i");
                int j;
                for (j = 0; j < cellPositions.size(); j++) {
                    format.append("%n%").append(cellPositions.get(j));
                }
                format.append("%d%n%").append(cellPositions.get(j - 1) + 1);
            }
            return prod.withAtt(prod.att().add("format", format.toString()));
        }
        return prod;
    }

    public static Module resolve(Module m) {
        Set<Sentence> newSentences = JavaConverters.asScalaSet(stream(m.localSentences()).map(s -> s instanceof Production ? resolve((Production) s) : s).collect(Collectors.toSet()));
        return Module(m.name(), m.imports(), newSentences, m.att());
    }

}
