package org.kframework.backend.java.symbolic;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Attribute;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Constant;
import org.kframework.kil.Empty;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.Production;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.matchers.MatcherException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;


/**
 * assumtions:
 *     all the KLabels are constants
 *     KLists are concrete (no KList variables)
 *     KLists with one element rather than the element directly
 */
public class SymbolicMatcher extends AbstractMatcher {

    class SymbolicEquality {
        public final Term lhs, rhs;

        SymbolicEquality(Term lhs, Term rhs) {
            this.lhs = lhs;
            this.rhs = rhs;
        }
    }

    private final Map<Variable, Term> substitution = new HashMap<Variable, Term>();
    private final Set<SymbolicEquality> constraints = new HashSet<SymbolicEquality>();
    private final Map<Variable, Term> freshSubstitution = new HashMap<Variable, Term>();

    public boolean isMatching(Term term, Term pattern) {
        substitution.clear();
        constraints.clear();
        freshSubstitution.clear();

        try {
            match(term, pattern);
            return true;
        } catch (MatcherException e) {
            substitution.clear();
            constraints.clear();
            freshSubstitution.clear();
            return false;
        }
    }

    /**
     * matches a cell against a cell
     *
     * @param cell
     * @param pattern
     */
    public void match(Cell cell, Term pattern) {
        if (!(pattern instanceof Cell)) {
            this.fail();
        }
        Cell patternCell = (Cell) pattern;

        if (!cell.getLabel().equals(patternCell.getLabel())) {
            fail();
        }

        match(cell.getContents(), patternCell.getContents());
    }


    /**
     * matches a bag of cells against another bag of cells
     *
     * @param bag
     * @param pattern
     */
    public void match(Bag bag, Term pattern) {
        if (!(pattern instanceof Bag)) {
            this.fail();
        }
        Bag patternBag = (Bag) pattern;

        Map<String, Term> cellMap = new HashMap<String, Term>();
        Map<String, Term> patternCellMap = new HashMap<String, Term>();

        for (Term bagItem : bag.getContents()) {
            assert bagItem instanceof Cell;

            Cell cell = (Cell) bagItem;
            cellMap.put(cell.getLabel(), cell.getContents());
        }

        for (Term patternBagItem : patternBag.getContents()) {
            assert patternBagItem instanceof Cell;

            Cell patternCell = (Cell) patternBagItem;
            patternCellMap.put(patternCell.getLabel(), patternCell.getContents());
        }

        if (!cellMap.keySet().equals(patternCellMap.keySet())) {
            fail();
        }

        for (String cellLabel : cellMap.keySet()) {
            match(cellMap.get(cellLabel), patternCellMap.get(cellLabel));
        }
    }

    public void match(Term term, Term pattern) {
        System.err.println(">>>");
        System.err.println(term);
        System.err.println("<<<");
        System.err.println(pattern);
        System.err.println("===");

        if (term instanceof Variable || pattern instanceof Variable
                || isSymbolicTerm(term) || isSymbolicTerm(pattern)) {
            constraints.add(new SymbolicEquality(term, pattern));
        } else {
            // match properly
            term.accept(this, pattern);
        }
    }

    @Override
    public void match(KSequence term, Term pattern) {
        if (!(pattern instanceof KSequence)) {
            this.fail();
        }

        KSequence patternKSequence = (KSequence) pattern;
        this.match(term.getContents(), patternKSequence.getContents());
    }

    @Override
    public void match(KApp term, Term pattern) {
        if (!(pattern instanceof KApp)) {
            fail();
        }

        KApp patternKApp = (KApp) pattern;
        this.match(term.getLabel(), patternKApp.getLabel());
        this.match(term.getChild(), patternKApp.getChild());
    }

    @Override
    public void match(KList term, Term pattern) {
        if(!(pattern instanceof KList)){
            fail();
        }

        KList patternKList = (KList) pattern;
        match(term.getContents(), patternKList.getContents());
    }

    @Override
    public void match(Empty term, Term patten) {
        if(!(patten instanceof Empty)) {
            fail();
        }
    }

    @Override
    public void match(KInjectedLabel term, Term patten) {
        if(!(patten instanceof KInjectedLabel)) {
            fail();
        }

        KInjectedLabel patternKInjectedLabel = (KInjectedLabel) patten;
        this.match(term.getTerm(), patternKInjectedLabel.getTerm());
    }

    @Override
    public void match(Constant term, Term pattern) {
        if(!term.equals(pattern)) {
            fail();
        }
    }


    public void match(List<Term> termList, List<Term> patternList) {
        int length = Math.min(termList.size(), patternList.size());
        for(int index = 0; index < length - 1; ++index) {
            this.match(termList.get(index), patternList.get(index));
        }

        if (termList.size() != patternList.size()) {
            System.err.println("ana are pere");

            if (termList.size() > length && patternList.get(length - 1) instanceof Variable) {
                List<Term> list = new ArrayList<Term>(termList.size() - length);
                for (int index = length - 1; index < termList.size(); ++index) {
                    list.add(termList.get(index));
                }

                //KList kList = new KList(list);
                //this.match(kList, (Variable) patternList.get(length - 1));
                KSequence kSequence = new KSequence(list);
                this.match(kSequence, (Variable) patternList.get(length - 1));

            } else if (patternList.size() > length && termList.get(length - 1) instanceof Variable) {
                List<Term> list = new ArrayList<Term>(patternList.size() - length);
                for (int index = length - 1; index < patternList.size(); ++index) {
                    list.add(patternList.get(index));
                }

                //KList kList = new KList(list);
                //this.match((Variable) termList.get(length - 1), kList);
                KSequence kSequence = new KSequence(list);
                this.match((Variable) termList.get(length - 1), kSequence);

            } else {
                this.fail();
            }
        } else {
            // match the last elements
            this.match(termList.get(length - 1), patternList.get(length - 1));
        }
    }


    public static boolean isSymbolicTerm(Term term) {
        if (term instanceof KApp) {
            KApp app = (KApp) term;
            if (app.getLabel() instanceof Constant) {
                Constant constant = (Constant) app.getLabel();

                assert constant.getSort().equals("KLabel");

                return isFunction(constant.getValue());
            }
        } else {
            // cases for maps, bags, sets, lists, etc
        }

        return false;
    }

    public static boolean isConstructor(String klabel) {
        return !isFunction(klabel);
    }

    public static boolean isFunction(String klabel) {
        if (!DefinitionHelper.labels.containsKey(klabel)) {
            return false;
        }

        for (String cons : DefinitionHelper.labels.get(klabel)) {
            assert DefinitionHelper.conses.containsKey(cons);

            Production production = DefinitionHelper.conses.get(cons);
            if (production.containsAttribute(Attribute.FUNCTION.getKey())) {
                return true;
            }
            if (production.containsAttribute(Attribute.PREDICATE.getKey())) {
                return true;
            }
        }

        return false;
    }

    public static boolean isBuiltinConstant(Term term) {
        return term instanceof Constant && MetaK.isBuiltinSort(term.getSort());
    }

}
