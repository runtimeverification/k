// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.binary;

import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.utils.errorsystem.KEMException;

import java.io.ByteArrayInputStream;
import java.io.DataInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import static org.kframework.kore.KORE.*;

/**
 * Created by dwightguth on 11/16/15.
 */
public class BinaryParser {

    private static final byte[] MAGIC = {0x7f, 'K', 'A', 'S', 'T'};

    public static final int BEGIN = 0, KTOKEN = 1, KAPPLY = 2, KSEQUENCE = 3, KVARIABLE = 4, KREWRITE = 5,
            INJECTEDKLABEL = 6, END = 7;

    private final DataInputStream data;
    private final List<String> interns = new ArrayList<>();

    private BinaryParser(DataInputStream data) {
        this.data = data;
    }

    private K read400() throws IOException {

        Deque<K> stack = new ArrayDeque<>();
        int type = 0;
        while(type != END) {
            type = data.readByte();
            List<K> items;
            int arity;
            switch (type) {
            case KTOKEN:
                stack.push(KToken(readString(), Sort(readString())));
                break;
            case KAPPLY:
                KLabel lbl = readKLabel();
                arity = data.readInt();
                items = new LinkedList<>();
                for (int i = 0; i < arity; i++) {
                    items.add(0, stack.pop());
                }
                stack.push(KApply(lbl, KList(items)));
                break;
            case KSEQUENCE:
                arity = data.readInt();
                items = new LinkedList<>();
                for (int i = 0; i < arity; i++) {
                    items.add(0, stack.pop());
                }
                stack.push(KSequence(items));
                break;
            case KVARIABLE:
                stack.push(KVariable(readString()));
                break;
            case KREWRITE:
                K right = stack.pop();
                K left = stack.pop();
                stack.push(KRewrite(left, right));
                break;
            case INJECTEDKLABEL:
                stack.push(InjectedKLabel(readKLabel()));
                break;
            case END:
                break;
            default:
                throw KEMException.criticalError("Unexpected code found in KAST binary term: " + type);
            }
        }
        return stack.peek();
    }

    private KLabel readKLabel() throws IOException {
        String lbl = readString();
        if (data.readBoolean())
            return KVariable(lbl);
        return KLabel(lbl);
    }

    private String readString() throws IOException {
        int idx = data.readInt();
        if (idx == 0) {
            int len = data.readInt();
            char[] buf = new char[len];
            for (int i = 0; i < len; i++) {
                buf[i] = data.readChar();
            }
            String s = new String(buf);
            interns.add(s);
            return s;
        } else {
            return interns.get(idx - 1);
        }
    }

    public static K parse(byte[] s) {
        ByteArrayInputStream in = new ByteArrayInputStream(s);
        return parse(in);
    }

    public static boolean isBinaryKast(byte[] bytes) {
        return Arrays.equals(Arrays.copyOfRange(bytes, 0, 5), MAGIC);
    }

    public static K parse(InputStream in) {
        try {
            DataInputStream data = new DataInputStream(in);
            byte[] magic = new byte[5];
            int read = data.read(magic);
            if (read != 5 || !Arrays.equals(magic, MAGIC)) {
                throw KEMException.compilerError("Reading binary data from input source which is not a KAST term.");
            }
            int major = data.readByte();
            int minor = data.readByte();
            int build = data.readByte();
            if (major == 4 && minor == 0 && build == 0) {
                return new BinaryParser(data).read400();
            } else {
                throw KEMException.compilerError("Unsupported version of KAST binary file: " + major + "." + minor + "." + build);
            }
        } catch (IOException e) {
            throw KEMException.criticalError("Could not read K term from binary", e);
        }
    }
}
