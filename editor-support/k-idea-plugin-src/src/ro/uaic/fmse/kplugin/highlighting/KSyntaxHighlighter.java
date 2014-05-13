// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.highlighting;

import com.intellij.lexer.FlexAdapter;
import com.intellij.lexer.Lexer;
import com.intellij.openapi.editor.DefaultLanguageHighlighterColors;
import com.intellij.openapi.editor.HighlighterColors;
import com.intellij.openapi.editor.colors.CodeInsightColors;
import com.intellij.openapi.editor.colors.TextAttributesKey;
import com.intellij.openapi.editor.markup.TextAttributes;
import com.intellij.openapi.fileTypes.SyntaxHighlighterBase;
import com.intellij.psi.TokenType;
import com.intellij.psi.tree.IElementType;
import com.intellij.ui.JBColor;
import org.jetbrains.annotations.NotNull;
import ro.uaic.fmse.kplugin.KLexer;
import ro.uaic.fmse.kplugin.psi.KTypes;

import java.awt.*;
import java.io.Reader;

import static com.intellij.openapi.editor.colors.TextAttributesKey.createTextAttributesKey;

public class KSyntaxHighlighter extends SyntaxHighlighterBase {
    //color names are taken from HTML color names: http://www.html-color-names.com
    private static final Color BROWN = JBColor.decode("#A52A2A");
    private static final Color MAROON = JBColor.decode("#800000");
    private static final Color ORCHID = JBColor.decode("#DA70D6");
    private static final Color DARKGOLDENROD = JBColor.decode("#B8860B");
    private static final Color MEDIUM_MAGENTA = JBColor.decode("#C000C0");

    public static final TextAttributesKey OPERATOR
            //= createTextAttributesKey("K_OPERATOR", DefaultLanguageHighlighterColors.COMMA);
            = createTextAttributesKey("K_OPERATOR", new TextAttributes(MAROON, null, null, null, Font.PLAIN));
    public static final TextAttributesKey KEYWORD = createTextAttributesKey("K_KEYWORD",
            DefaultLanguageHighlighterColors.KEYWORD);
    public static final TextAttributesKey STRING = createTextAttributesKey("K_STRING",
            DefaultLanguageHighlighterColors.STRING);
    public static final TextAttributesKey NUMBER = createTextAttributesKey("K_NUMBER",
            DefaultLanguageHighlighterColors.NUMBER);
    public static final TextAttributesKey COMMENT = createTextAttributesKey("K_COMMENT",
            DefaultLanguageHighlighterColors.LINE_COMMENT);
    public static final TextAttributesKey BRACKET = createTextAttributesKey("K_BRACKET",
            DefaultLanguageHighlighterColors.BRACKETS);
    public static final TextAttributesKey DOUBLE_COMMA
            //= createTextAttributesKey("K_DOUBLE_COMMA", DefaultLanguageHighlighterColors.SEMICOLON);
            =
            createTextAttributesKey("K_DOUBLE_COMMA", new TextAttributes(MEDIUM_MAGENTA, null, null, null, Font.PLAIN));
    public static final TextAttributesKey COMMA = createTextAttributesKey("K_COMMA",
            DefaultLanguageHighlighterColors.COMMA);
    public static final TextAttributesKey UNDERSCORE
            //= createTextAttributesKey("K_UNDERSCORE", DefaultLanguageHighlighterColors.IDENTIFIER);
            = createTextAttributesKey("K_UNDERSCORE",
            new TextAttributes(JBColor.black, null, null, null, Font.BOLD & Font.ITALIC));
    public static final TextAttributesKey LABEL
            //= createTextAttributesKey("K_LABEL", DefaultLanguageHighlighterColors.IDENTIFIER);
            = createTextAttributesKey("K_LABEL", new TextAttributes(JBColor.black, null, null, null, Font.ITALIC));

    public static final TextAttributesKey ATTRIBUTE_BLOCK = createTextAttributesKey("K_ATTRIBUTE_BLOCK",
            CodeInsightColors.ANNOTATION_NAME_ATTRIBUTES);
    public static final TextAttributesKey ITEM_NAME = createTextAttributesKey("K_ITEM_NAME",
            CodeInsightColors.TYPE_PARAMETER_NAME_ATTRIBUTES);
    public static final TextAttributesKey CELL
            //= createTextAttributesKey("K_CELL", DefaultLanguageHighlighterColors.INSTANCE_FIELD);
            = createTextAttributesKey("K_CELL", new TextAttributes(DARKGOLDENROD, null, null, null, Font.PLAIN));
    public static final TextAttributesKey TYPE = createTextAttributesKey("K_TYPE",
            DefaultLanguageHighlighterColors.STATIC_FIELD);
    public static final TextAttributesKey COLON = createTextAttributesKey("K_COLON", TYPE);
    public static final TextAttributesKey VAR
            = createTextAttributesKey("K_VAR", new TextAttributes(JBColor.black, null, null, null, Font.BOLD));
    public static final TextAttributesKey FUNCTION_CALL
            = createTextAttributesKey("K_FUNCTION_CALL", DefaultLanguageHighlighterColors.FUNCTION_CALL);
    public static final TextAttributesKey FUNCTION_DECLARATION
            = createTextAttributesKey("K_FUNCTION_DECLARATION", DefaultLanguageHighlighterColors.FUNCTION_DECLARATION);

    static final TextAttributesKey BAD_CHARACTER = createTextAttributesKey("K_BAD_CHARACTER",
            HighlighterColors.BAD_CHARACTER);
    static final TextAttributesKey ERROR = createTextAttributesKey("K_ERROR",
            CodeInsightColors.ERRORS_ATTRIBUTES);

    private static final TextAttributesKey[] OPERATOR_KEYS = new TextAttributesKey[]{OPERATOR};
    private static final TextAttributesKey[] KEYWORD_KEYS = new TextAttributesKey[]{KEYWORD};
    private static final TextAttributesKey[] STRING_KEYS = new TextAttributesKey[]{STRING};
    private static final TextAttributesKey[] NUMBER_KEYS = new TextAttributesKey[]{NUMBER};
    private static final TextAttributesKey[] COMMENT_KEYS = new TextAttributesKey[]{COMMENT};
    private static final TextAttributesKey[] LABEL_KEYS = new TextAttributesKey[]{LABEL};
    private static final TextAttributesKey[] BRACKET_KEYS = new TextAttributesKey[]{BRACKET};
    private static final TextAttributesKey[] DOUBLE_COMMA_KEYS = new TextAttributesKey[]{DOUBLE_COMMA};
    private static final TextAttributesKey[] COMMA_KEYS = new TextAttributesKey[]{COMMA};
    private static final TextAttributesKey[] UNDERSCORE_KEYS = new TextAttributesKey[]{UNDERSCORE};

    private static final TextAttributesKey[] BAD_CHAR_KEYS = new TextAttributesKey[]{BAD_CHARACTER};
    private static final TextAttributesKey[] EMPTY_KEYS = new TextAttributesKey[0];

    @NotNull
    @Override
    public Lexer getHighlightingLexer() {
        return new FlexAdapter(new KLexer((Reader) null));
    }

    @NotNull
    @Override
    public TextAttributesKey[] getTokenHighlights(IElementType tokenType) {
        if (tokenType.equals(KTypes.OPERATOR)) {
            return OPERATOR_KEYS;
        } else if (tokenType.equals(KTypes.KEYWORD)) {
            return KEYWORD_KEYS;
        } else if (tokenType.equals(KTypes.STRING)) {
            return STRING_KEYS;
        } else if (tokenType.equals(KTypes.INTEGER_LITERAL)) {
            return NUMBER_KEYS;
        } else if (tokenType.equals(KTypes.COMMENT)) {
            return COMMENT_KEYS;
        } else if (tokenType.equals(KTypes.LABEL_TOK)) {
            return LABEL_KEYS;
        } else if (tokenType.equals(KTypes.LEFT_PAREN) || tokenType.equals(KTypes.RIGHT_PAREN)) {
            return BRACKET_KEYS;
        } else if (tokenType.equals(KTypes.DOUBLE_COMMA)) {
            return DOUBLE_COMMA_KEYS;
        } else if (tokenType.equals(KTypes.COMMA)) {
            return COMMA_KEYS;
        } else if (tokenType.equals(KTypes.UNDERSCORE)) {
            return UNDERSCORE_KEYS;
        } else if (tokenType.equals(TokenType.BAD_CHARACTER)) {
            return BAD_CHAR_KEYS;
        } else {
            return EMPTY_KEYS;
        }
    }
}
