// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.unparser;

import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.parser.binary.BinaryParser;
import org.kframework.utils.errorsystem.KEMException;

import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;

/**
 * Writes a KAST term to the KAST binary format. For details of that format, see {@link BinaryParser}.
 */
public class ToBinary {

    public static void apply(OutputStream out, K k) {
        try {
            DataOutputStream data = new DataOutputStream(out);
            //magic
            data.writeByte(0x7f);
            data.writeBytes("KAST");
            //version
            data.writeByte(4);
            data.writeByte(0);
            data.writeByte(1);
            new ToBinary(data).traverse(k);
            data.writeByte(BinaryParser.END);
        } catch (IOException e) {
            throw KEMException.criticalError("Could not write K term to binary", e, k);
        }

    }

    public static byte[] apply(K k) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        apply(out, k);
        return out.toByteArray();
    }

    private DataOutputStream data;
    private Map<String, Integer> interns = new HashMap<>();
    private Map<K, Integer> kInterns = new IdentityHashMap<>();
    private int numTermsWritten;

    private ToBinary(DataOutputStream data) {
        this.data = data;
    }

    private void traverse(K k) throws IOException {
        if (kInterns.containsKey(k)) {
            data.writeByte(BinaryParser.BACK_REFERENCE);
            data.writeInt(numTermsWritten - kInterns.get(k));
            add_intern(k);
            return;
        }
        if (k instanceof KToken) {
            KToken tok = (KToken) k;

            data.writeByte(BinaryParser.KTOKEN);
            add_intern(k);
            writeString(tok.s());
            writeString(tok.sort().toString());

        } else if (k instanceof KApply) {
            KApply app = (KApply) k;

            for (K item : app.asIterable()) {
                traverse(item);
            }
            data.writeByte(BinaryParser.KAPPLY);
            add_intern(k);
            writeString(app.klabel().name());
            data.writeBoolean(app.klabel() instanceof KVariable);
            data.writeInt(app.size());

        } else if (k instanceof KSequence) {
            KSequence seq = (KSequence) k;

            for (K item : seq.asIterable()) {
                traverse(item);
            }
            data.writeByte(BinaryParser.KSEQUENCE);
            add_intern(k);
            data.writeInt(seq.size());

        } else if (k instanceof KVariable) {
            KVariable var = (KVariable) k;

            data.writeByte(BinaryParser.KVARIABLE);
            add_intern(k);
            writeString(var.name());

        } else if (k instanceof KRewrite) {
            KRewrite rew = (KRewrite) k;

            traverse(rew.left());
            traverse(rew.right());
            data.writeByte(BinaryParser.KREWRITE);
            add_intern(k);

        } else if (k instanceof InjectedKLabel) {
            InjectedKLabel inj = (InjectedKLabel) k;

            data.writeByte(BinaryParser.INJECTEDKLABEL);
            add_intern(k);
            writeString(inj.klabel().name());
            data.writeBoolean(inj.klabel() instanceof KVariable);

        } else {
            throw KEMException.criticalError("Unimplemented for Binary serialization: ", k);
        }
    }

    private void add_intern(K k) {
        kInterns.put(k, numTermsWritten);
        numTermsWritten++;
    }

    private void writeString(String s) throws IOException {
        int idx = interns.getOrDefault(s, interns.size());
        data.writeInt(interns.size() - idx);
        if (idx == interns.size()) {
            data.writeInt(s.length());
            data.writeChars(s);
            interns.put(s, interns.size());
        }
    }
}
