// Copyright (c) K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.attributes.HasLocation;
import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.Syntax;
import org.kframework.utils.errorsystem.KEMException;

/**
 * Replace every attribute [group(att1,...,attN)] with the underlying attributes [att1,...,attN]
 */
public class ExpandGroupAttribute {

    private static Att expandGroup(Att att, HasLocation node) {
        if (!att.contains(Att.GROUP(), String.class)) {
            return att;
        }
        String groups = att.get(Att.GROUP()).trim();
        if (groups.isEmpty()) {
            throw KEMException.compilerError("group(_) attribute expects a comma-separated list of arguments.");
        }
        KEMException badCommaException =
                KEMException.compilerError("Extraneous ',' in group(_) attribute.", node);
        if (groups.startsWith(",") || groups.endsWith(",")) {
            throw badCommaException;
        }
        for (String group : groups.split("\\s*,\\s*")) {
            if (group.isEmpty()) {
                throw badCommaException;
            }
            if (Att.getWhitelistedOptional(group).isPresent()) {
                throw KEMException.compilerError("User-defined group '" + group +
                        "' conflicts with built-in attribute.");
            }
            if (!group.matches("[a-z][a-zA-Z0-9-]*")) {
                throw KEMException.compilerError("Invalid argument '" + group + "' in group(_) attribute. " +
                        "Expected a lower case letter followed by any number of alphanumeric or '-' characters.", node);
            }
            att = att.addGroup(group);
        }
        return att.remove(Att.GROUP());
    }

    public static void apply(Definition d) {
        d.getItems().stream()
                .filter((item) -> item instanceof Module)
                .flatMap((mod) -> ((Module) mod).getItems().stream())
                .filter((modItem) -> modItem instanceof Syntax)
                .flatMap((s) -> ((Syntax) s).getPriorityBlocks().stream())
                .flatMap((pb) -> pb.getProductions().stream())
                .forEach((p) -> p.setAttributes(expandGroup(p.getAttributes(), p)));
    }
}
