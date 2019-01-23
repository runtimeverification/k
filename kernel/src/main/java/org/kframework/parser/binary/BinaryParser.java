// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.parser.binary;

import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.kore.mini.InjectedKLabel;
import org.kframework.kore.mini.KApply;
import org.kframework.kore.mini.KRewrite;
import org.kframework.kore.mini.KSequence;
import org.kframework.kore.mini.KToken;
import org.kframework.kore.mini.KVariable;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Parses a KAST binary term into the KORE data structures.
 *
 * Format of the KAST binary term is as follows:
 *
 * First five bytes are the magic header "\x7fKAST".
 * Next 3 bytes are the major, minor, and release version of the format. Currently
 * they are set to "\x04\x00\x00".
 *
 * Subsequently, the format contains a post-order traversal of the term according to the following rules:
 *
 * * KToken:         the byte "\x01" followed by a representation of the string of the token, and then the sort of the
 *                   token.
 * * KApply:         Representation of each child of the KApply followed by the byte "\x02" followed by a representation
 *                   of the klabel, followed by a 4-byte arity of the KApply.
 * * KSequence:      Representation of each child of the KSequence followed by the byte "\x03" followed by a 4-byte
 *                   length of the KSequence.
 * * KVariable:      The byte "\x04" followed by a representation of the name of the variable.
 * * KRewrite:       Representation of the LHS of the rewrite, followed by the RHS, followed by the byte "\x05".
 * * InjectedKLabel: The byte "\x06" followed by the representation of the klabel.
 * * KLabel:         The representation of the string of the klabel, followed by the byte "\x01" if the klabel is a
 *                   variable, and "\x00" if it's a concrete klabel.
 * * String:         A 4-byte offset in the string intern table. The intern table is commputed as the term is traversed.
 *                   An offset of 0 means that the string has not appeared before in this term, and is followed by a
 *                   4-byte length of the string followed by the String in UTF-16. An offset of 1 means the string
 *                   refers to the most recent previous string in the intern table. An offset of 2 means the
 *                   next-most-recent, and so forth.
 *
 * Note one exception to this rule in binary format 4.0.1: if a term is encountered that has already been serialized,
 * instead of serializing it again we serialize the byte '\x08' followed by a 4-byte offset in the term intern table.
 * The term intern table behaves the same as the string intern table except that it contains every term that has been
 * traversed to date.
 *
 * After the term is traversed, it terminates with the byte "\x07". Note that KAST terms are constructed to be
 * self-contained and composable. A client can take the output of two KAST terms and combine them into a single term
 * simply by concatenating the terms together after stripping their MAGIC prefix and suffix. This will not be as
 * space-compact as if the term was outputted all at once, but can be done in constant time without requiring the terms
 * to be modified internally, and will still deserialze correctly.
 */
public class BinaryParser {

    public static final byte[] MAGIC = {0x7f, 'K', 'A', 'S', 'T'};

    public static final int BEGIN = 0, KTOKEN = 1, KAPPLY = 2, KSEQUENCE = 3, KVARIABLE = 4, KREWRITE = 5,
            INJECTEDKLABEL = 6, END = 7, BACK_REFERENCE = 8;

    private final ByteBuffer data;
    private final List<String> interns = new ArrayList<>();
    private final List<K> kInterns = new ArrayList<>();

    private static K[] EMPTY_KLIST = new K[0];

    private BinaryParser(ByteBuffer data) {
        this.data = data;
    }

    private K read400(boolean _401) throws IOException {

        Deque<K> stack = new ArrayDeque<>();
        int type = 0;
        while(type != END) {
            type = data.get();
            K[] items;
            int arity;
            switch (type) {
            case KTOKEN:
                String s = readString();
                String sort = readString();
                Map<String, KToken> sortCache = ktokenCache.computeIfAbsent(sort, sort2 -> new HashMap<>());
                KToken token = sortCache.computeIfAbsent(s, s2 -> new KToken(s, Outer.parseSort(sort)));
                stack.push(token);
                break;
            case KAPPLY:
                KLabel lbl = readKLabel();
                arity = data.getInt();
                if (arity == 0)
                    items = EMPTY_KLIST;
                else
                    items = new K[arity];
                for (int i = arity - 1; i >= 0; i--) {
                    items[i] = stack.pop();
                }
                stack.push(KApply.of(lbl, items));
                break;
            case KSEQUENCE:
                arity = data.getInt();
                if (arity == 0)
                    items = EMPTY_KLIST;
                else
                    items = new K[arity];
                for (int i = arity - 1; i >= 0; i--) {
                    items[i] = stack.pop();
                }
                stack.push(new KSequence(items));
                break;
            case KVARIABLE:
                stack.push(new KVariable(readString()));
                break;
            case KREWRITE:
                K right = stack.pop();
                K left = stack.pop();
                stack.push(new KRewrite(left, right));
                break;
            case INJECTEDKLABEL:
                stack.push(new InjectedKLabel(readKLabel()));
                break;
            case END:
                break;
            case BACK_REFERENCE:
                if (!_401)
                    throw KEMException.criticalError("Unexpected code found in KAST binary term: " + type);
                int idx = data.getInt();
                stack.push(kInterns.get(kInterns.size() - idx));
                break;
            default:
                throw KEMException.criticalError("Unexpected code found in KAST binary term: " + type);
            }
            kInterns.add(stack.peek());
        }
        // gc hints
        interns.clear();
        klabelCache.clear();
        ktokenCache.clear();
        kInterns.clear();
        return stack.peek();
    }

    private Map<String, KLabel> klabelCache = new HashMap<>();
    private Map<String, Map<String, KToken>> ktokenCache = new HashMap<>();

    private KLabel readKLabel() throws IOException {
        String lbl = readString();
        if (data.get() != 0)
            return new KVariable(lbl);
        return klabelCache.computeIfAbsent(lbl, org.kframework.kore.KORE::KLabel);
    }

    private String readString() throws IOException {
        int idx = data.getInt();
        if (idx == 0) {
            int len = data.getInt();
            char[] buf = new char[len];
            for (int i = 0; i < len; i++) {
                buf[i] = data.getChar();
            }
            String s = new String(buf);
            interns.add(s);
            return s;
        } else {
            return interns.get(interns.size() - idx);
        }
    }

    public static boolean isBinaryKast(byte[] bytes) {
        return Arrays.equals(Arrays.copyOfRange(bytes, 0, 5), MAGIC);
    }

    public static K parse(byte[] in) {
        return parse(ByteBuffer.wrap(in));
    }

    public static K parse(ByteBuffer data) {
        try {
            byte[] magic = new byte[5];
            data.get(magic);
            if (!Arrays.equals(magic, MAGIC)) {
                throw KEMException.compilerError("Reading binary data from input source which is not a KAST term.");
            }
            int major = data.get();
            int minor = data.get();
            int build = data.get();
            if (major == 4 && minor == 0 && build == 0) {
                return new BinaryParser(data).read400(false);
            } else if (major == 4 && minor == 0 && build == 1) {
                return new BinaryParser(data).read400(true);
            } else {
                throw KEMException.compilerError("Unsupported version of KAST binary file: " + major + "." + minor + "." + build);
            }
        } catch (IOException e) {
            throw KEMException.criticalError("Could not read K term from binary", e);
        }
    }
}
