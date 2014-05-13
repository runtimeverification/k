// Copyright (c) 2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.codeStyle;

import com.intellij.psi.codeStyle.CodeStyleSettings;
import com.intellij.psi.codeStyle.CustomCodeStyleSettings;

/**
 * @author Denis Bogdanas
 *         Created on 4/02/14.
 */
public class KCodeStyleSettings extends CustomCodeStyleSettings {
    public KCodeStyleSettings(CodeStyleSettings settings) {
        super("KCodeStyleSettings", settings);
    }
}
