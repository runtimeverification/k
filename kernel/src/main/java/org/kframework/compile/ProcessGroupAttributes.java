// Copyright (c) K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.attributes.HasLocation;
import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.Syntax;
import org.kframework.utils.errorsystem.KEMException;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * A pass which handles all "user group" attributes. Specifically,
 *
 * - Replace every attribute [group(att1,...,attN)] with the underlying attributes [att1,...,attN].
 * - If --pedantic-attributes is disabled, then additionally convert every unrecognized attribute key to a user group.
 *
 */
public class ProcessGroupAttributes {

    private static Att processRawKeys(Att att, HasLocation node) {
        // During parsing, attributes my-att are inserted as either
        // - Key("my-att", KeyType.BuiltIn) if a recognized built-in
        // - Key("my-att", KeyType.RawKey) otherwise
        //
        // Thus, if --pedantic-attributes is disabled, we should replace every Key(..., KeyType.Raw) with
        // Key(..., KeyType.UserGroup), unless that raw key happens to conflict with an internal attribute.
        List<Att.Key> newGroups = Collections.stream(att.rawKeys())
                .map((k) -> {
                    Optional<Att.Key> groupKey = Att.getUserGroupOptional(k.key());
                    if (groupKey.isEmpty()) {
                        throw KEMException.compilerError(
                                "User-defined attribute '" + k.key() + "' conflicts with an " +
                                        "internal attribute.", node);
                    }
                    return groupKey.get();
                }).collect(Collectors.toList());
        for (Att.Key group : newGroups) {
            att = att.remove(Att.unsafeRawKey(group.key())).add(group);
        }
        if (!att.rawKeys().isEmpty()) {
            throw new AssertionError("Raw keys!");
        }
        return att;
    }

    private static Att expandGroupAttribute(Att att, HasLocation node) {
        if (!att.contains(Att.GROUP(), String.class)) {
            return att;
        }
        String groups = att.get(Att.GROUP()).trim();
        if (groups.isEmpty()) {
            throw KEMException.compilerError(
                    "group(_) attribute expects a comma-separated list of arguments.", node);
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
            Optional<Att.Key> groupKey = Att.getUserGroupOptional(group);
            if (groupKey.isEmpty()) {
                throw KEMException.compilerError("User-defined group '" + group +
                        "' conflicts with built-in or internal attribute.", node);
            }
            if (!group.matches("[a-z][a-zA-Z0-9-]*")) {
                throw KEMException.compilerError("Invalid argument '" + group + "' in group(_) attribute. " +
                        "Expected a lower case letter followed by any number of alphanumeric or '-' characters.", node);
            }
            att = att.add(groupKey.get());
        }
        return att.remove(Att.GROUP());
    }

    public static Att getProcessedAtt(Att att, HasLocation node, boolean pedanticAttributes) {
        Att newAtts = expandGroupAttribute(att, node);
        if (!pedanticAttributes) {
            newAtts = processRawKeys(newAtts, node);
        }
        return newAtts;
    }

    public static void apply(Module m, boolean pedanticAttributes) {
        m.getItems().stream()
                .filter((modItem) -> modItem instanceof Syntax)
                .flatMap((s) -> ((Syntax) s).getPriorityBlocks().stream())
                .flatMap((pb) -> pb.getProductions().stream())
                .forEach((p) -> {
                   p.setAttributes(getProcessedAtt(p.getAttributes(), p, pedanticAttributes));
                });
    }

    public static void apply(Definition d, boolean pedanticAttributes) {
        d.getItems().stream()
                .filter((item) -> item instanceof Module)
                .forEach((m) -> apply((Module) m, pedanticAttributes));
    }
}
