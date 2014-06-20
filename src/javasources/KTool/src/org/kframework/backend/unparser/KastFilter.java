// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import org.kframework.compile.utils.MaudeHelper;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class KastFilter extends BasicVisitor {
    protected Indenter result;
    private boolean nextline;
    
    public KastFilter(org.kframework.kil.loader.Context context) {
        super(context);
        result = new Indenter();
        result.setWidth(Integer.MAX_VALUE);
    }
    
    public KastFilter(IndentationOptions indentationOptions, boolean nextline, org.kframework.kil.loader.Context context) {
        super(context);
        result = new Indenter(indentationOptions);
        this.nextline = nextline;
    }

    public StringBuilder getResult() {
        return result.getResult();
    }

    @Override
    public Void visit(Definition def, Void _) {
        throw new RuntimeException("don't know how to kast Definition");
    }

    @Override
    public Void visit(Import imp, Void _) {
        throw new RuntimeException("don't know how to kast Import");
    }

    @Override
    public Void visit(Module mod, Void _) {
        throw new RuntimeException("don't know how to kast Module");
    }

    @Override
    public Void visit(Syntax syn, Void _) {
        throw new RuntimeException("don't know how to kast Syntax");
    }

    @Override
    public Void visit(PriorityBlock priorityBlock, Void _) {
        throw new RuntimeException("don't know how to kast PriorityBlock");
    }

    @Override
    public Void visit(Production prod, Void _) {
        throw new RuntimeException("don't know how to kast Production");
    }

    @Override
    public Void visit(Sort sort, Void _) {        
        throw new RuntimeException("don't know how to kast Sort");
    }

    @Override
    public Void visit(Terminal terminal, Void _) {
        throw new RuntimeException("don't know how to kast Terminal");
    }

    @Override
    public Void visit(StringSentence stringSentence, Void _) {
        result.write("StringSentence should not be StringSentence");
        return null;
    }

    @Override
    public Void visit(UserList userList, Void _) {
        throw new RuntimeException("don't know how to kast UserList");
    }

    @Override
    public Void visit(KList listOfK, Void _) {
        if (listOfK.getContents().size() == 0) {
            this.visitNode(new ListTerminator(listOfK.getSort(), null));
        } else if (listOfK.getContents().size() == 1) {
            this.visitNode(listOfK.getContents().get(0));
        } else {
            boolean first = true;
            for (Term term : listOfK.getContents()) {
                if (!first) {
                    result.write(",,");
                    result.endLine();
                } else {
                    first = false;
                }
                if (term == null) {
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
                            KExceptionGroup.INTERNAL, 
                            "NULL Term encountered when KastFilter ran on collection " + listOfK.getContents() + ".", 
                            listOfK.getFilename(), listOfK.getLocation()));                
                }    
                this.visitNode(term);
            }
        }
        return null;
    }

    @Override
    public Void visit(Attributes attributes, Void _) {
        throw new RuntimeException("don't know how to kast Attributes");
    }

    @Override
    public Void visit(Attribute attribute, Void _) {
        throw new RuntimeException("don't know how to kast Attribute");
    }

    @Override
    public Void visit(Configuration configuration, Void _) {
        throw new RuntimeException("don't know how to kast Configuration");
    }

    @Override
    public Void visit(Cell cell, Void _) {
        throw new RuntimeException("don't know how to kast Cell");
    }

    @Override
    public Void visit(Variable variable, Void _) {
        throw new RuntimeException("don't know how to kast Variable");
    }

    @Override
    public Void visit(ListTerminator empty, Void _) {
        String sort = empty.getSort();
        if (MaudeHelper.basicSorts.contains(sort)) {
            result.write(".");
            result.write(sort);
        } else {
            Production prd = context.listConses.get(sort);
            UserList ul = (UserList) prd.getItems().get(0);
            result.write(".List`{\"");
            result.write(ul.getSeparator());
            result.write("\"`}");
        }
        return null;
    }

    @Override
    public Void visit(Rule rule, Void _) {        
        throw new RuntimeException("don't know how to kast Rule");
    }

    @Override
    public Void visit(KApp kapp, Void _) {
        if (kapp.getLabel() instanceof Token) {
            Token token = (Token)kapp.getLabel();
            if (token.tokenSort().equals("#Id")) {
                result.write("#id \"");
            }
            result.write(token.value());
            if (token.tokenSort().equals("#Id")) {
                result.write("\"");
            } 
            result.write(token.toString());
        } else {
            this.visitNode(kapp.getLabel());
            result.write("(");
            boolean stopnextline = false;
            if (kapp.getChild() instanceof KList) {
                KList listOfK = (KList)kapp.getChild();
                if (listOfK.getContents().size() <= 1) {
                    stopnextline = true;
                }
            }
            if (kapp.getChild() instanceof ListTerminator) {
                stopnextline = true;
            }
            if (nextline) {
                if (!stopnextline) {
                    result.endLine();
                    result.indent(1);
                }
            } else {
                result.indentToCurrent();
            }
            this.visitNode(kapp.getChild());
            result.write(")");
            if (!nextline || !stopnextline) {
                result.unindent();
            }
        }
        return null;
    }

    @Override
    public Void visit(KSequence ksequence, Void _) {
        throw new RuntimeException("don't know how to kast KSequence");
    }

    @Override
    public Void visit(TermCons termCons, Void _) {
        throw new RuntimeException("don't know how to kast TermCons");
    }
    
    @Override
    public Void visit(Sentence sentence, Void _) {
        throw new RuntimeException("don't know how to kast Sentence");
    }
    
    @Override
    public Void visit(Rewrite rewrite, Void _) {
        throw new RuntimeException("don't know how to kast Rewrite");
    }

    @Override
    public Void visit(KLabelConstant kLabelConstant, Void _) {
        result.write(kLabelConstant.getLabel());
        return null;
    }

    @Override
    public Void visit(Token token, Void _) {
        result.write(token.toString());
        return null;
    }

    @Override
    public Void visit(Collection collection, Void _) {
        throw new RuntimeException("don't know how to kast Collection");
    }    
    
    @Override
    public Void visit(CollectionItem collectionItem, Void _) {
        throw new RuntimeException("don't know how to kast CollectionItem");
    }

    @Override
    public Void visit(BagItem bagItem, Void _) {
        throw new RuntimeException("don't know how to kast BagItem");
    }

    @Override
    public Void visit(Hole hole, Void _) {
        throw new RuntimeException("don't know how to kast Hole");
    }

    @Override
    public Void visit(KInjectedLabel kInjectedLabel, Void _) {
        Term term = kInjectedLabel.getTerm();
        if (MetaK.isKSort(term.getSort())) {
            result.write(KInjectedLabel.getInjectedSort(term.getSort()));
            result.write("2KLabel_("); 
        } else {
            result.write("#_(");
        }
        this.visitNode(term);
        result.write(")");
        return null;
    }

    @Override
    public Void visit(KLabel kLabel, Void _) {
        throw new RuntimeException("don't know how to kast KLabel");
    }

    @Override
    public Void visit(TermComment termComment, Void _) {
        throw new RuntimeException("don't know how to kast TermComment");
    }

    @Override
    public Void visit(Bag bag, Void _) {
        throw new RuntimeException("don't know how to kast Bag");
    }

    @Override
    public Void visit(org.kframework.kil.Ambiguity ambiguity, Void _) {
        throw new RuntimeException("don't know how to kast Ambiguity");
    }

    @Override
    public Void visit(org.kframework.kil.Context context, Void _) {
        throw new RuntimeException("don't know how to kast Context");
    }

    @Override
    public Void visit(LiterateDefinitionComment literateDefinitionComment, Void _) {
        throw new RuntimeException("don't know how to kast LiterateDefinitionComment");
    }

    @Override
    public Void visit(LiterateModuleComment literateModuleComment, Void _) {
        throw new RuntimeException("don't know how to kast LiterateModuleComment");
    }
    
    @Override
    public Void visit(org.kframework.kil.Require require, Void _) {
        throw new RuntimeException("don't know how to kast Require");
    }
}
