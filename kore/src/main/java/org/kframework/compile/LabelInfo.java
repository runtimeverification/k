// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.Sort;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.kframework.kore.KORE.*;

/**
 * Basic label information for cell completion
 */
public class LabelInfo {
    private final Multimap<KLabel, Sort> codomain = HashMultimap.create();

    private final Map<KLabel, AssocInfo> assocInfo = Maps.newHashMap();

    private final Set<KLabel> functionLabels = new HashSet<>();

    private final Map<KLabel, String> polyInfo = Maps.newHashMap();

    protected void addLabel(Sort result, String label) {
        addLabel(result, label, false);
    }

    protected void addLabel(Sort result, String label, boolean isAssoc) {
        addLabel(result, label, isAssoc, false, false);
    }

    protected void addLabel(Sort result, String label, boolean isAssoc, boolean isComm, boolean isFunction) {
        addLabel(result, label, isAssoc, isComm, isFunction, Optional.empty());
    }

    protected void addLabel(Sort result, String label, boolean isAssoc, boolean isComm, boolean isFunction, Optional<String> polyLabel) {
        KLabel kLabel = KLabel(label);
        codomain.put(kLabel, result);
        AssocInfo info = new AssocInfo(isAssoc, isComm);
        if (assocInfo.containsKey(kLabel)) {
            assert assocInfo.get(kLabel).equals(info);
        } else {
            assocInfo.put(kLabel, new AssocInfo(isAssoc, isComm));
        }
        if (isFunction) {
            functionLabels.add(kLabel);
        }
        if (polyLabel.isPresent()) {
            if (polyInfo.containsKey(kLabel)){
                assert polyInfo.get(kLabel).equals(polyLabel.get());
            } else {
                polyInfo.put(kLabel, polyLabel.get());
            }
        }
    }

    public LabelInfo() {
    }

    /**
     * Get the sort for the KLabel. Could be moved to module eventually.
     */
    public Sort getCodomain(KLabel l) {
        Collection<Sort> sorts = codomain.get(l);
        return Iterables.getOnlyElement(sorts, null);
    }

    public boolean isFunction(KLabel l) {
        return functionLabels.contains(l);
    }

    public boolean isFunction(K term) {
        if (term instanceof KApply && isFunction(((KApply) term).klabel())) {
            return true;
        }
        if (term instanceof KRewrite && ((KRewrite) term).left() instanceof KApply
                && isFunction(((KApply) ((KRewrite) term).left()).klabel())) {
            return true;
        }
        return false;
    }

    /**
     * Get the AC status of the KLabel. Could be moved to module eventually.
     */
    public AssocInfo getAssocInfo(KLabel l) {
        return assocInfo.get(l);
    }

    public static class AssocInfo {
        public AssocInfo(boolean isAssoc, boolean isComm) {
            this.isAssoc = isAssoc;
            this.isComm = isComm;
        }

        private final boolean isAssoc;
        private final boolean isComm;

        public boolean isAssoc() {
            return isAssoc;
        }

        public boolean isComm() {
            return isComm;
        }
    }

    /**
     * Get the poly attribute for the KLabel.
     */
    public String getPolyInfo(KLabel l) {
        return polyInfo.get(l);
    }
}
