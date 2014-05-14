// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.psi;

import com.intellij.psi.tree.IElementType;
import org.jetbrains.annotations.NonNls;
import org.jetbrains.annotations.NotNull;
import ro.uaic.fmse.kplugin.KLanguage;

public class KTokenType extends IElementType {
    public KTokenType(@NotNull @NonNls String debugName) {
        super(debugName, KLanguage.INSTANCE);
    }

    @Override
    public String toString() {
        return "KTokenType." + super.toString();
    }
}