// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import java.io.File;

import org.kframework.kil.ASTNode;
import org.kframework.kil.FileSource;
import org.kframework.kil.Rule;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.file.JarInfo;

/**
 *
 * @author YilongL
 */
public class RemovePreincludedRules extends CopyOnWriteTransformer {

    public RemovePreincludedRules(Context context) {
        super("Remove rules that are useless for the Java backend", context);
    }

    @Override
    public ASTNode visit(Rule node, Void _)  {
        if (!(node.getSource() instanceof FileSource)) {
            return null;
        }
        String filename = ((FileSource)node.getSource()).getFile().getAbsolutePath();
        if ((!filename.startsWith(JarInfo.getKBase(false) + File.separator + "include")
                && !filename.startsWith(org.kframework.kil.loader.Constants.GENERATED_FILENAME))
                || (filename.equals(JarInfo.getKBase(false)
                        + File.separator + "include" + File.separator + "builtins"
                        + File.separator + "id.k"))
                || (filename.equals(JarInfo.getKBase(false)
                        + File.separator + "include" + File.separator + "builtins"
                        + File.separator + "int.k"))
                || (filename.equals(JarInfo.getKBase(false)
                        + File.separator + "include" + File.separator + "builtins"
                        + File.separator + "mint.k"))
                || (filename.equals(JarInfo.getKBase(false)
                        + File.separator + "include" + File.separator + "io"
                        + File.separator + "io.k"))
                || (filename.equals(JarInfo.getKBase(false)
                                + File.separator + "include" + File.separator + "builtins"
                                + File.separator + "float.k"))
                || (filename.equals(JarInfo.getKBase(false)
                        + File.separator + "include" + File.separator + "modules"
                        + File.separator + "k-functional-visitor.k"))
                || (filename.equals(JarInfo.getKBase(false)
                        + File.separator + "include" + File.separator + "modules"
                        + File.separator + "verification_lemmas.k"))) {
            return node;
        }

        return null;
    }
}
