// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.compile;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;

import static org.kframework.kore.KORE.*;

import java.util.Collection;
import java.util.Map;

/**
 * Basic label information for cell completion
 */
public class LabelInfo {
    private final Multimap<KLabel, Sort> codomain = HashMultimap.create();

    private final Map<KLabel, AssocInfo> assocInfo = Maps.newHashMap();

    protected void addLabel(String result, String label) {
        addLabel(result, label, false);
    }

    protected void addLabel(String result, String label, boolean isAssoc) {
        addLabel(result, label, isAssoc, false);
    }

    protected void addLabel(String result, String label, boolean isAssoc, boolean isComm) {
        codomain.put(KLabel(label), Sort(result));
        AssocInfo info = new AssocInfo(isAssoc, isComm);
        if (assocInfo.containsKey(KLabel(label))) {
            assert assocInfo.get(KLabel(label)).equals(info);
        } else {
            assocInfo.put(KLabel(label), new AssocInfo(isAssoc, isComm));
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
}
