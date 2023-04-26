// Copyright (c) K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.definition.Definition;
import scala.Function1;

import javax.annotation.Nullable;
import java.util.List;
import java.util.function.Function;

/**
 * @author Denis Bogdanas
 * Created on 09-Jan-20.
 */
public abstract class AbstractBackend implements Backend {

    @Override
    public Function<Definition, Definition> proofDefinitionNonCachedSteps(
            @Nullable List<String> extraConcreteRuleLabels) {
        Function1<Definition, Definition> markExtraConcrete =
                def -> MarkExtraConcreteRules.mark(def, extraConcreteRuleLabels);
        return markExtraConcrete::apply;
    }
}
