package org.kframework;

import org.kframework.attributes.Att;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.ExistsK;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import scala.Function1;

import java.util.function.UnaryOperator;

/**
 * Created by cos on 12/7/15.
 */
public class AddRefersThisConfiguration implements UnaryOperator<Sentence> {
    /**
     * Puts a {@link Att#refers_THIS_CONFIGURATION()} marker on rules that do.
     */
    public Sentence apply(Sentence s) {
        if (s instanceof Rule) {
            Rule r = (Rule) s;
            boolean has_THIS_CONFIGURATION = new ExistsK() {
                @Override
                public Boolean apply(KVariable v) {
                    return v.name().equals("THIS_CONFIGURATION");
                }
            }.apply(r.body());

            boolean has_RESTORE_CONFIGURATION = new ExistsK() {
                @Override
                public Boolean apply(KApply k) {
                    return k.klabel().name().equals("#RESTORE_CONFIGURATION") || super.apply(k);
                }
            }.apply(r.body());

            Att newAtt = has_THIS_CONFIGURATION ? r.att().add(Att.refers_THIS_CONFIGURATION()) : r.att();
            newAtt = has_RESTORE_CONFIGURATION ? newAtt.add(Att.refers_RESTORE_CONFIGURATION()) : newAtt;

            return Rule.apply(r.body(), r.requires(), r.ensures(), newAtt);
        } else
            return s;
    }
}
