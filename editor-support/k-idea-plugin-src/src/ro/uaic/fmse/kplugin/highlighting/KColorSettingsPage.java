package ro.uaic.fmse.kplugin.highlighting;

import com.intellij.openapi.editor.colors.TextAttributesKey;
import com.intellij.openapi.fileTypes.SyntaxHighlighter;
import com.intellij.openapi.options.colors.AttributesDescriptor;
import com.intellij.openapi.options.colors.ColorDescriptor;
import com.intellij.openapi.options.colors.ColorSettingsPage;
import org.jetbrains.annotations.NonNls;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import ro.uaic.fmse.kplugin.KIcons;

import javax.swing.*;
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
      new AttributesDescriptor("Auxiliary function call", KSyntaxHighlighter.FUNCTION_CALL),
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
    return
        "require \"core.k\"\n" +
            "require \"subtyping.k\"\n" +
            "\n" +
            "//@ \\section{Module PRIMITIVE-TYPES}\n" +
            "\n" +
            "module <name>PRIMITIVE-TYPES</name>\n" +
            "    imports <name>CORE</name>\n" +
            "    imports <name>SUBTYPING</name>\n" +
            "\n" +
            "//@ \\subsection{Type labels}\n" +
            "//@Here we rewrite Java AST terms for primitive types into their corresponding Type.\n" +
            "\n" +
            "rule 'Byte(.KList) => byte      <attribute>[structural, anywhere]</attribute>\n" +
            "\n" +
            "//@ \\subsection{Integer types normalization}\n" +
            "\n" +
            "syntax K ::= \"bitCount\" \"(\" Type \")\" <attribute>[function]</attribute>\n" +
            "\n" +
            "syntax <error>error</error>\n" +
            "\n" +
            "rule <name>[StartExecutionPhase]:</name>\n" +
            "    <cell><k></cell> . =>\n" +
            "      //K-AST for new <MainClass>().main(new String[0]);\n" +
            "      'ExprStm(\n" +
            "        'Invoke(\n" +
            "          'MethodName('TypeName(String2Id(MainClassS)),, String2Id(\"main\"))\n" +
            "        )\n" +
            "      )\n" +
            "    <cell></k></cell>\n" +
            "    <cell><env></cell> . <cell></env></cell>\n" +
            "    <cell><mainClass></cell> ListItem(MainClassS<colon>:</colon><type>String</type>) <cell></mainClass></cell>\n" +
            "    <cell><globalPhase></cell> ElaborationPhase => ExecutionPhase  <cell></globalPhase></cell>\n" +
            "\n" +
            "rule <name>[ContinueLabeledNotMatch]:</name>\n" +
            "    (whileLabel(<var>LabelK</var>:K) => .) ~> 'Continue('Some(<var>X</var>:Id)) ~> (whileImpl(_,_) => .)\n" +
            "when\n" +
            "    <var>LabelK</var> =/=K <var>X</var>";
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
