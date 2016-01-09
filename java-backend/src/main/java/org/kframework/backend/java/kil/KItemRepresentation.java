// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;


import org.kframework.kore.*;
import org.kframework.kore.KLabel;
import org.kframework.kore.KList;

import java.util.List;
import java.util.stream.Stream;

public interface KItemRepresentation extends KoreRepresentation, KApply {
    default Term kLabel() {
        return ((KItem) toKore()).kLabel();
    }

    default Term kList() {
        return ((KItem) toKore()).kList();
    }

    default Stream<K> stream() {
        throw new AssertionError("Unimplemented");
    }

    default List<K> items() { throw new AssertionError("Unimplemented"); }

    default int size() { throw new AssertionError("Unimplemented"); }

    default Iterable<K> asIterable() { throw new AssertionError("Unimplemented"); }

    @Override
    default org.kframework.kore.KLabel klabel() {
        if (kLabel() instanceof KLabelInjection) {
            return ((KApply) ((KLabelInjection) kLabel()).term()).klabel();
        } else {
            return (KLabel) kLabel();
        }
    }

    @Override
    default org.kframework.kore.KList klist() {
        if (kLabel() instanceof KLabelInjection) {
            return ((KApply) ((KLabelInjection) kLabel()).term()).klist();
        } else {
            return (KList) KCollection.upKind(kList(), Kind.KLIST);
        }
    }
}
