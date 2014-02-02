package org.kframework.backend.java.kil;

import java.util.HashMap;
import java.util.Map;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.krun.api.io.FileSystem;

import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Table;

/**
 * An object containing context specific to a particular configuration.
 */
public class TermContext extends JavaSymbolicObject {

    private static Map<Definition, TermContext> cache1 = new HashMap<Definition, TermContext>();
    private static Table<Definition, FileSystem, TermContext> cache2 = HashBasedTable.create();

    private final Definition def;
    private final FileSystem fs;
    
    private TermContext(Definition def, FileSystem fs) {
        this.def = def;
        this.fs = fs;
    }
    
    /**
     * Only used when the Term is part of a Definition instead of part of a
     * ConstrainedTerm.
     */
    public static TermContext of(Definition def) {
        TermContext termContext = cache1.get(def);
        if (termContext == null) {
            termContext = new TermContext(def, null);
            cache1.put(def, termContext);
        }
        return termContext;
    }

    public static TermContext of(Definition def, FileSystem fs) {
        assert fs != null;
        TermContext termContext = cache2.get(def, fs);
        if (termContext == null) {
            termContext = new TermContext(def, fs);
            cache2.put(def, fs, termContext);
        }
        return termContext;
    }

    public Definition definition() {
        return def;
    }

    public FileSystem fileSystem() {
        return fs;
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Visitor visitor) {
        throw new UnsupportedOperationException();
    }

}
