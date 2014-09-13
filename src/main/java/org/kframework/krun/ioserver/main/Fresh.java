// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.main;
/***
 * Generate Long fresh ids.
 * @author andrei.arusoaie
 *
 */
public class Fresh {
    private static Long id = (long) 0;

    /**
     * Increment the id and return it.
     * @return a fresh id.
     */
    public static Long getFreshId() {
        return id++;
    }
}
