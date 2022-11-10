// Copyright (c) 2018-2020 K Team. All Rights Reserved.
package org.kframework.parser.outer;

import com.vladsch.flexmark.ast.FencedCodeBlock;
import com.vladsch.flexmark.parser.Parser;
import com.vladsch.flexmark.util.ast.Document;
import com.vladsch.flexmark.util.ast.NodeVisitor;
import com.vladsch.flexmark.util.ast.VisitHandler;
import com.vladsch.flexmark.util.data.MutableDataSet;
import org.jetbrains.annotations.NotNull;
import org.kframework.attributes.Source;
import org.kframework.parser.markdown.ASTExpressionStart;
import org.kframework.parser.markdown.TagSelector;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.HashSet;
import java.util.Set;

/**
 * Takes a Markdown file, and extract annotated code-blocks according to the mdSelector expression.
 * The inner code is kept exactly in place so error reporting can be precise.
 * @author Radu Mereuta
 */
public class ExtractFencedKCodeFromMarkdown {

    private final KExceptionManager kem;
    private final ASTExpressionStart mdSelector;

    public ExtractFencedKCodeFromMarkdown(KExceptionManager kem, String mdSelector) {
        this.kem = kem;
        this.mdSelector = TagSelector.parseSelectorExp(mdSelector);
    }

    public String extract(String mdText, Source source) {
        KCodeExtractor extractor = new KCodeExtractor(mdText, mdSelector, source, kem);
        return extractor.getKCode();
    }

    private static class KCodeExtractor {
        private final ASTExpressionStart mdSelector;
        private final String mdText;
        private final Source source;
        private final KExceptionManager kem;
        int lastOffset;
        // gather the k code in a single string without markdown
        StringBuilder kCodeSb;
        // build a copy with only whitespaces so location information for code-block parsing matches
        StringBuilder blankSb;
        public KCodeExtractor(String mdText, ASTExpressionStart mdSelector, Source source, KExceptionManager kem) {
            this.mdText = mdText;
            this.mdSelector = mdSelector;
            this.source = source;
            this.kem = kem;
        }

        NodeVisitor visitor = new NodeVisitor(
                new VisitHandler<>(FencedCodeBlock.class, this::visit)
        );

        public void visit(FencedCodeBlock block) {
            // copy up to where the code-block info starts
            while (lastOffset < block.getInfo().getStartOffset()) {
                if (Character.isWhitespace(mdText.charAt(lastOffset))) {
                    kCodeSb.append(mdText.charAt(lastOffset));
                    blankSb.append(mdText.charAt(lastOffset));
                } else
                    blankSb.append(" ");
                lastOffset++;
            }
            String cbStr = block.getInfo().toString();
            Set<String> tags = new HashSet<>();
            tags = TagSelector.parseTags(blankSb + cbStr, source, kem);
            // interested only in code blocks marked as valid by the mdSelector expression
            if (TagSelector.eval(mdSelector, tags)) {
                // navigate from previous offset to the current one and
                // make everything whitespace to preserve location info
                long offset = block.getContentChars().getStartOffset();
                while (lastOffset < offset) {
                    if (Character.isWhitespace(mdText.charAt(lastOffset))) {
                        kCodeSb.append(mdText.charAt(lastOffset));
                        blankSb.append(mdText.charAt(lastOffset));
                    } else
                        blankSb.append(" ");
                    lastOffset++;
                }
                // copy each character because block.getContentChars() removes indentation and can offset location info
                offset = block.getContentChars().getEndOffset();
                while (lastOffset < offset) {
                    kCodeSb.append(mdText.charAt(lastOffset));
                    if (Character.isWhitespace(mdText.charAt(lastOffset)))
                        blankSb.append(mdText.charAt(lastOffset));
                    else
                        blankSb.append(" ");
                    lastOffset++;
                }
            }
            // Descending into children
            visitor.visitChildren(block);
        }

        String getKCode() {
            MutableDataSet options = new MutableDataSet();
            Parser parser = Parser.builder(options).build();
            @NotNull Document doc = parser.parse(mdText);
            lastOffset = 0;
            kCodeSb = new StringBuilder();
            blankSb = new StringBuilder();
            visitor.visit(doc);
            // make everything whitespace to preserve location info for end of file errors
            while (lastOffset < mdText.length()) {
                if (Character.isWhitespace(mdText.charAt(lastOffset)))
                    kCodeSb.append(mdText.charAt(lastOffset));
                lastOffset++;
            }

            return kCodeSb.toString();
        }
    }
}
