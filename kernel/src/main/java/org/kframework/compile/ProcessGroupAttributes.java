// Copyright (c) K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.attributes.HasLocation;
import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.Syntax;
import org.kframework.utils.errorsystem.KEMException;
import scala.util.Either;

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

    private static Att convertRawKeysToUserGroups(Att att, HasLocation node) {
        // During parsing, an attribute my-att is inserted as either
        // - Key("my-att", KeyType.BuiltIn) if a recognized built-in
        // - Key("my-att", KeyType.RawKey) otherwise
        //
        // Thus, if --pedantic-attributes is disabled, we should replace every Key(..., KeyType.Raw) with
        // Key(..., KeyType.UserGroup).
        List<Att.Key> newGroups = Collections.stream(att.rawKeys())
                .map((k) -> {
                    Optional<Att.Key> groupKey = Att.getUserGroupOptional(k.key());
                    if (groupKey.isEmpty()) {
                        throw new AssertionError("Found Att.Key(" + k.key() + ", KeyType.RawKey), " +
                                "but outer parsing should have produced Att.Key(" + k.key() + ", KeyType.BuiltIn) " +
                                "instead");
                    }
                    return groupKey.get();
                }).collect(Collectors.toList());
        for (Att.Key group : newGroups) {
            att = att.remove(Att.unsafeRawKey(group.key())).add(group);
        }
        return att;
    }

    public static Att getProcessedAtt(Att att, HasLocation node, boolean pedanticAttributes) {
        Either<String, Att> newAttOrError = att.withGroupAttAsUserGroups();
        if (newAttOrError.isLeft()) {
            throw KEMException.compilerError(newAttOrError.left().get(), node);
        }
        Att newAtt = newAttOrError.right().get();

        if (!pedanticAttributes) {
            newAtt = convertRawKeysToUserGroups(newAtt, node);
        }
        return newAtt;
    }

    public static void apply(Module m, boolean pedanticAttributes) {
        m.getItems().stream()
                .filter((modItem) -> modItem instanceof Syntax)
                .flatMap((s) -> ((Syntax) s).getPriorityBlocks().stream())
                .flatMap((pb) -> pb.getProductions().stream())
                .forEach((p) -> p.setAttributes(getProcessedAtt(p.getAttributes(), p, pedanticAttributes)));
    }

    public static void apply(Definition d, boolean pedanticAttributes) {
        d.getItems().stream()
                .filter((item) -> item instanceof Module)
                .forEach((m) -> apply((Module) m, pedanticAttributes));
    }
}
