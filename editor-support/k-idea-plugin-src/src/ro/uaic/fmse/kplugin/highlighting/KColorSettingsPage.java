// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.highlighting;

import com.intellij.openapi.diagnostic.Logger;
import com.intellij.openapi.editor.colors.TextAttributesKey;
import com.intellij.openapi.fileTypes.SyntaxHighlighter;
import com.intellij.openapi.options.colors.AttributesDescriptor;
import com.intellij.openapi.options.colors.ColorDescriptor;
import com.intellij.openapi.options.colors.ColorSettingsPage;
import com.intellij.openapi.util.io.FileUtil;
import org.jetbrains.annotations.NonNls;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import ro.uaic.fmse.kplugin.KIcons;

import javax.swing.*;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

public class KColorSettingsPage implements ColorSettingsPage {
    private static final AttributesDescriptor[] DESCRIPTORS = new AttributesDescriptor[]{
            new AttributesDescriptor("Keyword", KSyntaxHighlighter.KEYWORD),
            new AttributesDescriptor("Number", KSyntaxHighlighter.NUMBER),
            new AttributesDescriptor("String", KSyntaxHighlighter.STRING),
            new AttributesDescriptor("Comment", KSyntaxHighlighter.COMMENT),
            new AttributesDescriptor("Operator", KSyntaxHighlighter.OPERATOR),
            new AttributesDescriptor("Bracket", KSyntaxHighlighter.BRACKET),
            new AttributesDescriptor("Double comma", KSyntaxHighlighter.DOUBLE_COMMA),
            new AttributesDescriptor("Comma", KSyntaxHighlighter.COMMA),
            new AttributesDescriptor("Underscore", KSyntaxHighlighter.UNDERSCORE),
            new AttributesDescriptor("Label", KSyntaxHighlighter.LABEL),

            new AttributesDescriptor("Colon", KSyntaxHighlighter.COLON),
            new AttributesDescriptor("Type", KSyntaxHighlighter.TYPE),
            new AttributesDescriptor("Variable", KSyntaxHighlighter.VAR),
            new AttributesDescriptor("Aux function declaration", KSyntaxHighlighter.FUNCTION_DECLARATION),
            new AttributesDescriptor("Aux function call", KSyntaxHighlighter.FUNCTION_CALL),
            new AttributesDescriptor("Cell", KSyntaxHighlighter.CELL),
            new AttributesDescriptor("Attribute", KSyntaxHighlighter.ATTRIBUTE_BLOCK),
            new AttributesDescriptor("Module or rule name", KSyntaxHighlighter.ITEM_NAME),
            new AttributesDescriptor("Error", KSyntaxHighlighter.ERROR),
            new AttributesDescriptor("Bad Character", KSyntaxHighlighter.BAD_CHARACTER),
    };

    @NonNls
    private static final Map<String, TextAttributesKey> ourTags = new HashMap<>();

    static {
        ourTags.put("cell", KSyntaxHighlighter.CELL);
        ourTags.put("attribute", KSyntaxHighlighter.ATTRIBUTE_BLOCK);
        ourTags.put("name", KSyntaxHighlighter.ITEM_NAME);
        ourTags.put("colon", KSyntaxHighlighter.COLON);
        ourTags.put("type", KSyntaxHighlighter.TYPE);
        ourTags.put("var", KSyntaxHighlighter.VAR);
        ourTags.put("func-call", KSyntaxHighlighter.FUNCTION_CALL);
        ourTags.put("func-dec", KSyntaxHighlighter.FUNCTION_DECLARATION);
        ourTags.put("error", KSyntaxHighlighter.ERROR);
    }

    @Nullable
    @Override
    public Icon getIcon() {
        return KIcons.FILE;
    }

    @NotNull
    @Override
    public SyntaxHighlighter getHighlighter() {
        return new KSyntaxHighlighter();
    }

    @NotNull
    @Override
    public String getDemoText() {
        try {
            return FileUtil.loadTextAndClose(
                    this.getClass().getResourceAsStream("/ro/uaic/fmse/kplugin/highlighting/KColorSettingsDemo.txt"));
        } catch (IOException e) {
            Logger.getInstance(this.getClass().getName()).error(e);
            return "";
        }
    }

    @Nullable
    @Override
    public Map<String, TextAttributesKey> getAdditionalHighlightingTagToDescriptorMap() {
        return ourTags;
    }

    @NotNull
    @Override
    public AttributesDescriptor[] getAttributeDescriptors() {
        return DESCRIPTORS;
    }

    @NotNull
    @Override
    public ColorDescriptor[] getColorDescriptors() {
        return ColorDescriptor.EMPTY_ARRAY;
    }

    @NotNull
    @Override
    public String getDisplayName() {
        return "K";
    }
}
