// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.builtin.KLabels;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attribute.Key;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.CellDataStructure;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.Production;
import org.kframework.kil.Sort;
import org.kframework.kil.UserList;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.KRunOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.Poset;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.RequestScoped;

import java.io.Serializable;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;
import com.google.inject.Inject;

@RequestScoped
public class Context implements Serializable {

    public static final Set<Key<String>> parsingTags = ImmutableSet.of(
        Attribute.keyOf("left"),
        Attribute.keyOf("right"),
        Attribute.keyOf("non-assoc"));

    public static final Set<String> specialTerminals = ImmutableSet.of(
        "(",
        ")",
        ",",
        "[",
        "]",
        "{",
        "}");

    /**
     * Represents the bijection map between conses and productions.
     */
    public Set<Production> productions = new HashSet<>();
    /**
     * Represents a map from all Klabels in string representation
     * to sets of corresponding productions.
     * why?
     */
    public SetMultimap<String, Production> klabels = HashMultimap.create();
    public SetMultimap<String, Production> tags = HashMultimap.create();
    public Map<String, Cell> cells = new HashMap<>();
    public Map<String, Sort> cellSorts = new HashMap<>();
    public Map<Sort, Production> listProductions = new LinkedHashMap<>();
    public SetMultimap<String, Production> listKLabels = HashMultimap.create();

    public Map<Sort, Production> canonicalBracketForSort = new HashMap<>();
    private Poset<Sort> subsorts = Poset.create();
    private Poset<Sort> syntacticSubsorts = Poset.create();
    private Poset<String> priorities = Poset.create();
    private Poset<String> assocLeft = Poset.create();
    private Poset<String> assocRight = Poset.create();
    public Map<String, Sort> configVarSorts = new HashMap<>();
    public Map<String, CellDataStructure> cellDataStructures = new HashMap<>();
    public Set<Sort> variableTokenSorts = new HashSet<>();
    public HashMap<Sort, String> freshFunctionNames = new HashMap<>();
    public HashMap<Sort, Sort> smtSortFlattening = new HashMap<>();

    private BiMap<String, Production> conses;

    /**
     * The two structures below are populated by the InitializeConfigurationStructure step of the compilation.
     * configurationStructureMap represents a map from cell names to structures containing cell data.
     * maxConfigurationLevel represent the maximum level of cell nesting in the configuration.
     */
    private ConfigurationStructureMap configurationStructureMap = new ConfigurationStructureMap();
    private int maxConfigurationLevel = -1;

    /**
     * {@link Map} of sort names into {@link DataStructureSort} instances.
     */
    private Map<Sort, DataStructureSort> dataStructureSorts;

    /**
     * {@link Set} of sorts with lexical productions.
     */
    private Set<Sort> tokenSorts;


    public java.util.List<String> getKomputationCells() {
        return kompileOptions.experimental.kCells;
    }

    public ConfigurationStructureMap getConfigurationStructureMap() {
        return configurationStructureMap;
    }

    public int getMaxConfigurationLevel() {
        return maxConfigurationLevel;
    }

    public void setMaxConfigurationLevel(int maxConfigurationLevel) {
        this.maxConfigurationLevel = maxConfigurationLevel;
    }

    private void initSubsorts(Poset<Sort> subsorts) {
        subsorts.addElement(Sort.KLABEL);
        subsorts.addRelation(Sort.KLIST, Sort.K);
        subsorts.addRelation(Sort.K, Sort.KITEM);
        subsorts.addRelation(Sort.KITEM, Sort.KRESULT);
        subsorts.addRelation(Sort.BAG, Sort.BAG_ITEM);
    }

    // TODO(dwightguth): remove these fields and replace with injected dependencies
    @Deprecated @Inject public transient GlobalOptions globalOptions;
    public KompileOptions kompileOptions;
    @Deprecated @Inject(optional=true) public transient KRunOptions krunOptions;

    public Context() {
        initSubsorts(subsorts);
        initSubsorts(syntacticSubsorts);
    }

    public Sort startSymbolPgm() {
        return configVarSorts.getOrDefault("PGM", Sort.K);
    }

    public void addProduction(Production p) {
        productions.add(p);
        if (p.getKLabel() != null) {
            klabels.put(p.getKLabel(), p);
            tags.put(p.getKLabel(), p);
            if (p.isListDecl()) {
                listKLabels.put(p.getTerminatorKLabel(), p);
            }
        }
        if (p.isListDecl()) {
            listProductions.put(p.getSort(), p);
        }
        for (Attribute<?> a : p.getAttributes().values()) {
            tags.put(a.getKey().toString(), p);
        }
    }

    public void removeProduction(Production p) {
        productions.remove(p);
         if (p.getKLabel() != null) {
            klabels.remove(p.getKLabel(), p);
            tags.remove(p.getKLabel(), p);
            if (p.isListDecl()) {
                listKLabels.remove(p.getTerminatorKLabel(), p);
            }
        }
        if (p.isListDecl()) {
            // AndreiS: this code assumes each list sort has only one production
            listProductions.remove(p.getSort());
        }
        for (Attribute<?> a : p.getAttributes().values()) {
            tags.remove(a.getKey().toString(), p);
        }
    }

    public void addCellDecl(Cell c) {
        cells.put(c.getLabel(), c);

        String sortName = c.getCellAttributes().get(Cell.SORT_ATTRIBUTE);
        Sort sort = sortName == null ? c.getContents().getSort() : Sort.of(sortName);
        if (sort.equals(Sort.BAG_ITEM))
            sort = Sort.BAG;
        cellSorts.put(c.getLabel(), sort);
    }

    public Sort getCellSort(Cell cell) {
        Sort sort = cellSorts.get(cell.getLabel());

        if (sort == null) {
            if (cell.getLabel().equals("k"))
                sort = Sort.K;
            else if (cell.getLabel().equals("freshCounter"))
                sort = Sort.K;
            else if (cell.getLabel().equals("path-condition"))
                sort = Sort.K;
        } else {
            // if the k cell is opened, then the sort needs to take into consideration desugaring
            if (cell.getEllipses() != Ellipses.NONE) {
                if (isSubsortedEq(Sort.LIST, sort))
                    sort = Sort.LIST;
                else if (isSubsortedEq(Sort.BAG, sort))
                    sort = Sort.BAG;
                else if (isSubsortedEq(Sort.MAP, sort))
                    sort = Sort.MAP;
                else if (isSubsortedEq(Sort.SET, sort))
                    sort = Sort.SET;
                else // any other computational sort
                    sort = Sort.K;
            }
        }
        return sort;
    }

    public boolean isListSort(Sort sort) {
        return listProductions.containsKey(sort);
    }

    /**
     * Returns a unmodifiable view of all sorts.
     */
    public Set<Sort> getAllSorts() {
        return Collections.unmodifiableSet(subsorts.getElements());
    }

    /**
     * Takes a List sort and returns the sort of the elements of that List sort. e.g, for List{Exp, ","}, returns Exp.
     *
     * returns null if not a List sort
     *
     * we suppress cast warnings because we know that the sort must be UserList
     */
    @SuppressWarnings("cast")
    public Sort getListElementSort(Sort sort) {
        if (!isListSort(sort))
            return null;
        return ((UserList) listProductions.get(sort).getItems().get(0)).getSort();
    }

    /**
     * Finds the LUB (Least Upper Bound) of a given set of sorts.
     *
     * @param sorts
     *            the given set of sorts
     * @return the sort which is the LUB of the given set of sorts on success;
     *         otherwise {@code null}
     */
    public Sort getLUBSort(Sort... sorts) {
        return subsorts.getLUB(Sets.newHashSet(sorts));
    }

    /**
     * Checks if there is any well-defined common subsort of a given set of
     * sorts.
     *
     * @param sorts
     *            the given set of sorts
     * @return {@code true} if there is at least one well-defined common
     *         subsort; otherwise, {@code false}
     */
    public boolean hasCommonSubsort(Sort... sorts) {
        Set<Sort> maximalLowerBounds = subsorts.getMaximalLowerBounds(Sets.newHashSet(sorts));

        if (maximalLowerBounds.isEmpty()) {
            return false;
        } else if (maximalLowerBounds.size() == 1) {
            Sort sort = maximalLowerBounds.iterator().next();
            /* checks if the only common subsort is undefined */
            if (sort.equals(Sort.BUILTIN_BOT)
                    || isListSort(sort)
                    && getListElementSort(sort).equals(Sort.BUILTIN_BOT)) {
                return false;
            }
        }

        return true;
    }

    public void addPriority(String bigPriority, String smallPriority) {
        // add the new priority
        priorities.addRelation(bigPriority, smallPriority);
    }

    public void finalizePriority() {
        priorities.transitiveClosure();
    }

    public void addLeftAssoc(String label1, String label2) {
        assocLeft.addRelation(label1, label2);
    }

    public void addRightAssoc(String label1, String label2) {
        assocRight.addRelation(label1, label2);
    }

    public boolean isLeftAssoc(String label1, String label2) {
        return assocLeft.isInRelation(label1, label2);
    }

    public boolean isRightAssoc(String label1, String label2) {
        return assocRight.isInRelation(label1, label2);
    }

    /**
     * Check to see if the two klabels are in the wrong order according to the priority filter.
     */
    public boolean isPriorityWrong(String klabelParent, String klabelChild) {
        return priorities.isInRelation(klabelParent, klabelChild);
    }

    public void addSubsort(Sort bigSort, Sort smallSort) {
        subsorts.addRelation(bigSort, smallSort);
    }

    public void addSyntacticSubsort(Sort bigSort, Sort smallSort) {
        syntacticSubsorts.addRelation(bigSort, smallSort);
    }

    /**
     * Computes the transitive closure of the subsort relation to make it
     * becomes a partial order set.
     */
    public void computeSubsortTransitiveClosure() {
        computeSubsortTransitiveClosure(subsorts);
        computeSubsortTransitiveClosure(syntacticSubsorts);
   }

    private void computeSubsortTransitiveClosure(Poset<Sort> subsorts) {
        List<Sort> circuit = subsorts.checkForCycles();
        if (circuit != null) {
            String msg = "Circularity detected in subsorts: ";
            for (Sort sort : circuit)
                msg += sort + " < ";
            msg += circuit.get(0);
            throw KEMException.criticalError(msg);
        }
        subsorts.transitiveClosure();
        // detect if lists are subsorted (Vals Ids < Exps)
        for (Production prod1 : listProductions.values()) {
            for (Production prod2 : listProductions.values()) {
                Sort sort1 = ((UserList) prod1.getItems().get(0)).getSort();
                Sort sort2 = ((UserList) prod2.getItems().get(0)).getSort();
                if (subsorts.isInRelation(sort1, sort2)) {
                    subsorts.addRelation(prod1.getSort(), prod2.getSort());
                }
            }
        }
        subsorts.transitiveClosure();
    }

    /**
     * Check to see if smallSort is subsorted to bigSort (strict)
     */
    public boolean isSubsorted(Sort bigSort, Sort smallSort) {
        return subsorts.isInRelation(bigSort, smallSort);
    }

    /**
     * Check to see if smallSort is subsorted or equal to bigSort
     */
    public boolean isSubsortedEq(Sort bigSort, Sort smallSort) {
        if (bigSort.equals(smallSort))
            return true;
        return subsorts.isInRelation(bigSort, smallSort);
    }

    /**
     * Check to see if smallSort is a strict syntactic subsort of bigSort
     * (any term parsing as smallSort also parses as bigSort).
     * In particular, elements of a user cons list are syntactically
     * but not semantically subsorted to the list type.
     *
     */
    public boolean isSyntacticSubsorted(Sort bigSort, Sort smallSort) {
        return syntacticSubsorts.isInRelation(bigSort, smallSort);
    }

    /**
     * Check to see if smallSort is syntactically subsorted or equal to bigSort
     * (any term parsing as smallSort also parses as bigSort).
     * In particular, elements of a user cons list are syntactically
     * but not semantically subsorted to the list type.
     */
    public boolean isSyntacticSubsortedEq(Sort bigSort, Sort smallSort) {
        if (bigSort.equals(smallSort))
            return true;
        return syntacticSubsorts.isInRelation(bigSort, smallSort);
    }

    public boolean isSpecialTerminal(String terminal) {
        return specialTerminals.contains(terminal);
    }

    public boolean isParsingTag(Key<?> key) {
        return parsingTags.contains(key);
    }

    public static final int HASH_PRIME = 37;

    /**
     * Returns a {@link Set} of productions associated with the specified KLabel
     *
     * @param label
     *            string representation of the KLabel
     * @return list of productions associated with the label
     */
    public Set<Production> productionsOf(String label) {
        return klabels.get(label);
    }

    public Map<Sort, DataStructureSort> getDataStructureSorts() {
        return Collections.unmodifiableMap(dataStructureSorts);
    }

    public void setDataStructureSorts(Map<Sort, DataStructureSort> dataStructureSorts) {
        this.dataStructureSorts = new HashMap<>(dataStructureSorts);
    }

    /**
     * Return the DataStructureSort corresponding to the given Sort, or null if
     * the sort is not known as a data structure sort.
     */
    public DataStructureSort dataStructureSortOf(Sort sort) {
        return dataStructureSorts.get(sort);
    }

    /**
     * Like dataStructureSortOf, except it returns null also if
     * the sort corresponds to a DataStructureSort which isn't a list sort.
     */
    public DataStructureSort dataStructureListSortOf(Sort sort) {
        DataStructureSort dataStructSort = dataStructureSorts.get(sort);
        if (dataStructSort == null) return null;
        if (!dataStructSort.type().equals(Sort.LIST)) return null;
        return dataStructSort;
    }

    /**
     * Get a DataStructureSort for the default list sort, or raise a nice exception.
     * Equivalent to
     * <code>dataStructureListSortOf(DataStructureSort.DEFAULT_LIST_SORT)</code>,
     * if it succeeds.
     */
    public DataStructureSort getDefaultListDataStructureSort() {
        DataStructureSort list = dataStructureListSortOf(DataStructureSort.DEFAULT_LIST_SORT);
        if (list == null) {
            throw KEMException.internalError(
                    "A sort List must exist and be recognized as a data structure sort."
                            + " Installation is corrupt or --no-prelude used with incomplete definition.");
        }
        return list;
    }

    /**
     * Returns the set of sorts that have lexical productions.
     */
    public Set<Sort> getTokenSorts() {
        return Collections.unmodifiableSet(tokenSorts);
    }

    public void setTokenSorts(Set<Sort> tokenSorts) {
        this.tokenSorts = new HashSet<>(tokenSorts);
    }

    public void makeFreshFunctionNamesMap(Set<Production> freshProductions) {
        for (Production production : freshProductions) {
            if (!production.containsAttribute(Attribute.FUNCTION_KEY)) {
                throw KExceptionManager.compilerError(
                        "missing [function] attribute for fresh function " + production,
                        production);
            }

            if (freshFunctionNames.containsKey(production.getSort())) {
                throw KExceptionManager.compilerError(
                        "multiple fresh functions for sort " + production.getSort(),
                        production);
            }

            freshFunctionNames.put(production.getSort(), production.getKLabel());
        }
    }

    public void makeSMTSortFlatteningMap(Set<Production> freshProductions) {
        for (Production production : freshProductions) {
            if (!production.isSubsort()) {
                throw KExceptionManager.compilerError(
                        "unexpected tag [smt-sort-flatten] for non-subsort production " + production,
                        production);
            }

            smtSortFlattening.put(production.getSubsort(), production.getSort());
        }
    }

    /**
     * @deprecated DO NOT USE outside the SDF frontend!
     */
    @Deprecated
    public BiMap<String, Production> getConses() {
        return conses;
    }

    private int number = 0;


    /**
     * Generate incremental numbers that doesn't contain the number 1
     *
     * @return an integer that doesn't contain the number 1
     */
    private int getUniqueId() {
        boolean valid = false;
        while (!valid) {
            int nr = number;
            while (nr > 0) {
                if (nr % 10 == 1) {
                    number++;
                    break;
                } else {
                    nr /= 10;
                }
            }
            if (nr == 0) {
                valid = true;
            }
        }
        return number++;
    }

    public void computeConses() {
        assert conses == null : "can only compute conses once";
        conses = HashBiMap.create();
        for (Production p : productions) {
            // add cons to productions that don't have it already
            if (p.containsAttribute("bracket")) {
                // don't add cons to bracket production
                String cons2 = StringUtil.escapeSort(p.getSort()) + "1Bracket";
                conses.put(cons2, p);
            } else if (p.isLexical()) {
            } else if (p.isSubsort()) {
            } else {
                String cons;
                if (p.isListDecl())
                    cons = StringUtil.escapeSort(p.getSort()) + "1" + "ListSyn";
                else
                    cons = StringUtil.escapeSort(p.getSort()) + "1" + getUniqueId() + "Syn";
                conses.put(cons, p);
            }
        }
    }

    public Poset<Sort> subsorts() {
        return subsorts;
    }

}
