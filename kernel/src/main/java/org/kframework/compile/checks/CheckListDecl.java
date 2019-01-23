// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import com.google.common.collect.ImmutableSet;
import org.kframework.builtin.Sorts;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Syntax;
import org.kframework.kil.UserList;
import org.kframework.kore.Sort;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.Set;

/**
 * Checks user list declarations:
 * - Base sorts cannot be extended with list.
 * - Circular lists are not allowed.
 * - Inline lists are not allowed.
 */
public class CheckListDecl {

    public static void check(Module m) {
        m.getItems().stream().forEach(CheckListDecl::check); // i -> check(i)
    }

    private static Set<Sort> BASE_SORTS = ImmutableSet.of(Sorts.K(), Sorts.KResult(), Sorts.KItem(),
            Sorts.KList(), Sorts.Bag(), Sorts.KLabel());

    private static boolean isBaseSort(Sort sort) {
        return BASE_SORTS.contains(sort);
    }


    private static void check(ModuleItem i) {
        if (i instanceof Syntax) {
            Syntax s = (Syntax) i;
            for (PriorityBlock b : s.getPriorityBlocks()) {
                for (Production p : b.getProductions()) {
                    if (p.getItems().size() == 1 && p.getItems().get(0) instanceof UserList) { // Syntax Es ::= List{E,""}
                        Sort listSort = s.getDeclaredSort().getSort(); // Es
                        Sort elemSort = ((UserList) p.getItems().get(0)).getSort(); // E
                        if (isBaseSort(listSort)) {
                            throw KEMException.compilerError(listSort + " can not be extended to be a list sort.", p);
                        }
                        if (listSort.equals(elemSort)) {
                            throw KEMException.compilerError("Circular lists are not allowed.", p);
                        }
                    } else {
                        for (ProductionItem it : p.getItems()) {
                            if (it instanceof UserList) { // Syntax Es ::= ... List{E,""} ...
                                throw KEMException.compilerError("Inline list declarations are not allowed.", it);
                            }
                        }
                    }
                }
            }
        }
    }
}
