// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.unparser;

import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.utils.errorsystem.KEMException;

import java.io.IOException;
import java.io.OutputStream;
import java.io.DataOutputStream;
import java.io.ByteArrayOutputStream;

import java.util.Map;
import java.util.HashMap;
import java.util.Optional;

/**
 * Writes a KAST term to the LaTeX format.
 */
public class ToLatex {

    public static byte[] apply(K k) {
        try {
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            apply(new DataOutputStream(out), k);
            return out.toByteArray();
        } catch (IOException e) {
            throw KEMException.criticalError("Could not write K term to LaTeX", e, k);
        }
    }

    public static void apply(DataOutputStream out, K k) throws IOException {
        if (k instanceof KToken) {
            KToken tok = (KToken) k;
            out.writeUTF(tok.s());

        } else if (k instanceof KApply) {
            KApply app = (KApply) k;

            out.writeUTF("\\" + app.klabel().name());

            for (K item : app.klist().asIterable()) {
                out.writeUTF("{");
                ToLatex.apply(out, item);
                out.writeUTF("}");
            }

        } else if (k instanceof KSequence) {
            KSequence kseq = (KSequence) k;

            out.writeUTF("KSequence unimplemented");

        } else if (k instanceof KVariable) {
            KVariable var = (KVariable) k;

            Optional<String> origName = var.att().getOptional("originalName");
            if (origName.isPresent()) {
                out.writeUTF(origName.get());
            } else {
                out.writeUTF(var.name());
            }

        } else if (k instanceof KRewrite) {
            KRewrite rew = (KRewrite) k;

            out.writeUTF("KRewrite unimplemented");

        } else if (k instanceof KAs) {
            KAs alias = (KAs) k;

            out.writeUTF("KAs unimplemented");

        } else if (k instanceof InjectedKLabel) {
            KAs alias = (KAs) k;

            out.writeUTF("InjectedKLabel unimplemented");

        }
    }
}
