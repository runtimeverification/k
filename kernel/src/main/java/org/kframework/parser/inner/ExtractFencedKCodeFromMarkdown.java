// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.parser.inner;

import com.vladsch.flexmark.ast.FencedCodeBlock;
import com.vladsch.flexmark.parser.Parser;
import com.vladsch.flexmark.util.ast.Document;
import com.vladsch.flexmark.util.ast.NodeVisitor;
import com.vladsch.flexmark.util.ast.VisitHandler;
import com.vladsch.flexmark.util.data.MutableDataSet;
import org.jetbrains.annotations.NotNull;

public class ExtractFencedKCodeFromMarkdown {

    public static String extract(String mdText) {
        KCodeExtractor extractor = new KCodeExtractor();
        return extractor.getKCode(mdText);
    }

    private static class KCodeExtractor {
        int lastOffset;
        StringBuilder sb;
        String mdText;

        NodeVisitor visitor = new NodeVisitor(
                new VisitHandler<>(FencedCodeBlock.class, this::visit)
        );

        public void visit(FencedCodeBlock block) {
            if (block.getInfo().toString().equals("k")) {
                // interested only in code blocks marked as `k`
                // navigate from previous offset to the current one and
                // mark make every character as whitespace to preserve location info
                while (lastOffset < block.getContentChars().getStartOffset()) {
                    if (Character.isWhitespace(mdText.charAt(lastOffset)))
                        sb.append(mdText.charAt(lastOffset));
                    lastOffset++;
                }
                // copy each character because block.getContentChars() removes indentation and can offset location info
                while (lastOffset < block.getContentChars().getEndOffset()) {
                    sb.append(mdText.charAt(lastOffset));
                    lastOffset++;
                }
            }
            // Descending into children
            visitor.visitChildren(block);
        }

        String getKCode(String mdText) {
            MutableDataSet options = new MutableDataSet();
            Parser parser = Parser.builder(options).build();
            @NotNull Document doc = parser.parse(mdText);
            lastOffset = 0;
            this.mdText = mdText;
            sb = new StringBuilder();
            visitor.visit(doc);
            return sb.toString();
        }
    }
}
