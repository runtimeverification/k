// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.HashSet;
import java.util.Set;

import org.kframework.backend.java.kil.JavaSymbolicObject;

/**
 * Checks whether the structure of a K abstract syntax tree conforms to some
 * specified rules, e.g., the depth of an expression should not exceed a certain
 * number, etc.
 *
 * @author YilongL
 *
 */
public class PluggableKastStructureChecker extends PrePostVisitor {

    private final Set<KastStructureCheckerPlugin> plugins = new HashSet<KastStructureCheckerPlugin>();
    private boolean isSuccess = true;

    public PluggableKastStructureChecker() {
        super();
        this.getPreVisitor().addVisitor(new StopWhenFail());
    }

    /**
     * Registers a plugin to this checker.
     *
     * @param plugin
     *            the plugin to register
     */
    public void register(KastStructureCheckerPlugin plugin) {
        assert !plugins.contains(plugin);
        plugins.add(plugin);
        plugin.registerTo(this);

        if (plugin.getPreVisitor() != null) {
            this.getPreVisitor().addVisitor(plugin.getPreVisitor());
        }
        if (plugin.getPostVisitor() != null) {
            this.getPostVisitor().addVisitor(plugin.getPostVisitor());
        }
    }

    public boolean isSuccess() {
        return isSuccess;
    }

    public void reset() {
        isSuccess = true;
        for (KastStructureCheckerPlugin plugin : plugins) {
            plugin.reset();
        }
    }

    /**
     * Notifies this checker that some specified rule is violated. This method
     * should only be called from a registered plugin.
     *
     * @param plugin
     *            the plugin that detects the violation
     */
    public void flagFailure(KastStructureCheckerPlugin plugin) {
        assert plugins.contains(plugin) : "This method shall be called from a registered plugin only.";
        isSuccess = false;
    }

    /**
     * Stops this checker when one of the specified rules is violated.
     */
    private class StopWhenFail extends LocalVisitor {
        @Override
        protected void visit(JavaSymbolicObject object) {
            if (!isSuccess) {
                this.proceed = false;
            }
        }
    }
}
