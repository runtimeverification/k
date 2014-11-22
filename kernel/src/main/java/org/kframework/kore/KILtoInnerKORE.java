// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore;

import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.kframework.kil.ASTNode;
import org.kframework.kil.AbstractVisitor;
import org.kframework.kil.Attributes;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.kil.Hole;
import org.kframework.kil.Import;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KSequence;
import org.kframework.kil.Lexical;
import org.kframework.kil.LiterateModuleComment;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.PriorityExtended;
import org.kframework.kil.PriorityExtendedAssoc;
import org.kframework.kil.Production;
import org.kframework.kil.Require;
import org.kframework.kil.Restrictions;
import org.kframework.kil.Sentence;
import org.kframework.kil.StringSentence;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kore.outer.*;

import scala.Enumeration.Value;
import scala.collection.Seq;

import com.google.common.collect.Sets;

import static org.kframework.kore.outer.Constructors.*;
import static org.kframework.kore.Constructors.*;

@SuppressWarnings("unused")
public class KILtoInnerKORE extends KILTransformation<K> {
    public K apply(Bag body) {
        List<K> contents = body.getContents().stream().map(this).collect(Collectors.toList());
        return KBag(contents);
    }

    KApply cellMarker = org.kframework.kore.outer.Configuration.cellMarker();

    public KApply apply(Cell body) {
        K x = (K) apply(body.getContents());
        if (x instanceof KBag && !((KBag) x).isEmpty()) {
            return KApply(KLabel(body.getLabel()), KList(((KBag) x).contents()),
                    Attributes(cellMarker));
        } else
            return KApply(KLabel(body.getLabel()), KList(x), Attributes(cellMarker));
    }

    public org.kframework.kore.KSequence apply(KSequence seq) {
        return KSequence(apply(seq.getContents()));
    }

    private List<K> apply(List<Term> contents) {
        return contents.stream().map(this).map(x -> (K) x).collect(Collectors.toList());
    }

    public KApply apply(TermCons cons) {
        return KApply(KLabel(cons.getProduction().getKLabel()), KList(apply(cons.getContents())));
    }

    public KApply apply(Hole hole) {
        return KApply(Hole(), KList());
    }

    public KVariable apply(Variable v) {
        return KVariable(v.getName());
    }
}
