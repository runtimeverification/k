package org.kframework.backend.java.symbolic;

import java.util.HashMap;
import java.util.Map;

import org.kframework.backend.java.kil.KLabel;

/**
 * TODO
 * @author YilongL
 *
 */
public class KastStructureChecker extends PrePostVisitor {
    
    private Map<KLabel, Integer> kLabelCounter = new HashMap<KLabel, Integer>();
    
    public KastStructureChecker() {
        super();
        this.getPreVisitor().addVisitor(new IncKLabelCounter());
    }
    
    public String toString() {
        return "KastStructureChecker: " + kLabelCounter.toString();
    }

    private class IncKLabelCounter extends LocalVisitor {
        @Override
        public void visit(KLabel kLabel) {
            if (kLabelCounter.get(kLabel) == null) {
                kLabelCounter.put(kLabel, 0);
            }
            kLabelCounter.put(kLabel, kLabelCounter.get(kLabel) + 1);
        }
    }
    
    @SuppressWarnings("unused")
    private class DecKLabelCounter extends LocalVisitor {
        @Override
        public void visit(KLabel kLabel) {
            kLabelCounter.put(kLabel, kLabelCounter.get(kLabel) - 1);
        }
    }    
}
