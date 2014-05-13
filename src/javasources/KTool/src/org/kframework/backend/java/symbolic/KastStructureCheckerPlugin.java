// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

/**
 * An interface for the plugin of the pluggable KAST checker.
 * 
 * @author YilongL
 * 
 */
interface KastStructureCheckerPlugin {

    /**
     * Registers this plugin to a given checker. This method should only be
     * called from
     * {@code PluggableKastStructureChecker#register(KastStructureCheckerPlugin)}
     * .
     * 
     * @param checker
     *            the given checker
     */
    void registerTo(PluggableKastStructureChecker checker);

    /**
     * Resets the state of this plugin in order to check a new term.
     */
    void reset();
    
    LocalVisitor getPreVisitor();

    LocalVisitor getPostVisitor();
}
