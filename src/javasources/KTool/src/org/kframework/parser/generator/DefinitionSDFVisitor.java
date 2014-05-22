// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.kframework.kil.KLabelConstant;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.PriorityBlockExtended;
import org.kframework.kil.PriorityExtended;
import org.kframework.kil.PriorityExtendedAssoc;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Restrictions;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.Subsort;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class DefinitionSDFVisitor extends BasicVisitor {

    public Set<Production> outsides = new HashSet<Production>();
    public Set<Production> constants = new HashSet<Production>();
    public Set<String> constantSorts = new HashSet<String>();
    public Set<Sort> insertSorts = new HashSet<Sort>(); // list of inserted sorts that need to avoid the priority filter
    public Set<Subsort> subsorts = new HashSet<Subsort>();
    public Set<Production> listProds = new HashSet<Production>(); // list of sorts declared as being list
    public Set<Sort> userSorts = new HashSet<Sort>(); // list of sorts declared by the user (to be declared later as Start symbols if no declaration for Start was found)
    public StringBuilder sdf = new StringBuilder();
    public List<Production> lexical = new ArrayList<Production>();
    public List<Restrictions> restrictions = new ArrayList<Restrictions>();
    private boolean ground = false;

    public DefinitionSDFVisitor(boolean ground, Context context) {
        super(context);
        constantSorts.add("#Id");
        constantSorts.add("#Bool");
        constantSorts.add("#Int");
        constantSorts.add("#String");
        constantSorts.add("#Float");
        this.ground = ground;
    }

    public Void visit(Syntax syn, Void _) {

        userSorts.add(syn.getSort());
        processPriorities(syn.getPriorityBlocks());
        return null;
    }

    public Void visit(PriorityExtended node, Void _) {
        // reconstruct a syntax declaration from the syntax priorities
        List<PriorityBlock> priblocks = new ArrayList<PriorityBlock>();
        for (int i = 0; i < node.getPriorityBlocks().size(); i++) {
            PriorityBlockExtended pbe1 = node.getPriorityBlocks().get(i);
            PriorityBlock pb1 = new PriorityBlock();

            for (KLabelConstant tag : pbe1.getProductions()) {
                Set<Production> prods2 = SDFHelper.getProductionsForTag(tag.getLabel(), context);
                if (prods2.isEmpty()) {
                    String msg = "Could not find any production represented by tag: " + tag.getLabel();
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, tag.getFilename(), tag.getLocation()));
                }
                pb1.getProductions().addAll(prods2);
            }
            priblocks.add(pb1);
        }

        processPriorities(priblocks);
        return null;
    }

    public Void visit(PriorityExtendedAssoc node, Void _) {
        // reconstruct a syntax declaration from the syntax priorities
        List<PriorityBlock> priblocks = new ArrayList<PriorityBlock>();
        PriorityBlock pb1 = new PriorityBlock();
        pb1.setAssoc(node.getAssoc());

        for (KLabelConstant tag : node.getTags()) {
            Set<Production> prods2 = SDFHelper.getProductionsForTag(tag.getLabel(), context);
            if (prods2.isEmpty()) {
                String msg = "Could not find any production represented by tag: " + tag.getLabel();
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, tag.getFilename(), tag.getLocation()));
            }
            pb1.getProductions().addAll(prods2);
        }
        priblocks.add(pb1);

        processPriorities(priblocks);
        return null;
    }

    private void processPriorities(List<PriorityBlock> priblocks) {
        List<PriorityBlock> prilist = new ArrayList<PriorityBlock>();
        for (PriorityBlock prt : priblocks) {
            PriorityBlock p = new PriorityBlock();
            p.setAssoc(prt.getAssoc());

            // filter the productions according to their form
            for (Production prd : prt.getProductions()) {
                if (prd.containsAttribute("onlyLabel")) {
                    // if a production has this attribute, don't add it to the list
                } else if (prd.containsAttribute("notInRules") && !ground) {
                    // if a production has this attribute, don't add it to the list
                } else if (prd.containsAttribute("notInGround") && ground) {
                    // if a production has this attribute, don't add it to the list
                } else if (prd.isLexical()) {
                    lexical.add(prd);
                } else if (prd.isSubsort()) {
                    if (!prd.getSort().equals("KResult")) { // avoid KResult because it breaks subsortings in SDF
                        p.getProductions().add(prd);
                        subsorts.add(new Subsort(prd.getSort(), ((Sort) prd.getItems().get(0)).getName()));
                        // add the small sort to the user sorts to add it to the variable declarations
                        userSorts.add((Sort) prd.getItems().get(0));
                    }
                } else if (prd.getItems().get(0) instanceof Terminal && prd.getItems().size() == 1 && prd.isConstant()) {
                    constants.add(prd);
                    constantSorts.add(prd.getSort());
                } else if (prd.getItems().get(0) instanceof Terminal && prd.getItems().get(prd.getItems().size() - 1) instanceof Terminal) {
                    outsides.add(prd);
                } else if (prd.isListDecl()) {
                    outsides.add(prd);
                    listProds.add(prd);
                    subsorts.add(new Subsort(prd.getSort(), ((UserList) prd.getItems().get(0)).getSort()));
                } else {
                    p.getProductions().add(prd);
                }
            }
            if (p.getProductions().size() > 0)
                prilist.add(p);
        }

        if (prilist.size() > 0) {
            if (prilist.size() == 1 && (prilist.get(0).getAssoc() == null || prilist.get(0).getAssoc().equals(""))) {
                // weird bug in SDF - if you declare only one production in a priority block, it gives parse errors
                // you need to have at least 2 productions or a block association
                PriorityBlock prt = prilist.get(0);
                for (Production p : prt.getProductions())
                    outsides.add(p);
            } else {
                sdf.append("context-free priorities\n");

                for (PriorityBlock prt : prilist) {
                    if (prt.getAssoc() == null || prt.getAssoc().equals(""))
                        sdf.append("{\n");
                    else
                        sdf.append("{ " + prt.getAssoc() + ":\n");
                    for (Production p : prt.getProductions()) {
                        sdf.append("    ");
                        List<ProductionItem> items = p.getItems();
                        for (int i = 0; i < items.size(); i++) {
                            ProductionItem itm = items.get(i);
                            if (itm instanceof Terminal) {
                                Terminal t = (Terminal) itm;
                                if (!ground) {
                                    if (t.getTerminal().equals(":"))
                                        sdf.append("ColonDz ");
                                    else if (t.getTerminal().equals("?"))
                                        sdf.append("QuestionMarkDz ");
                                    else if (t.getTerminal().equals("!"))
                                        sdf.append("ExclamationMarkDz ");
                                    else
                                        sdf.append("\"" + StringUtil.escape(t.getTerminal()) + "\" ");
                                } else
                                    sdf.append("\"" + StringUtil.escape(t.getTerminal()) + "\" ");
                            } else if (itm instanceof Sort) {
                                Sort srt = (Sort) itm;
                                // if we are on the first or last place and this sort is not a list, just print the sort
                                if (i == 0 || i == items.size() - 1) {
                                    sdf.append(StringUtil.escapeSortName(srt.getName()) + " ");
                                } else {
                                    // if this sort should be inserted to avoid the priority filter, then add it to the list
                                    insertSorts.add(srt);
                                    String tempstr = srt.getName();
                                    if (tempstr.endsWith("CellSort") || tempstr.endsWith("CellFragment"))
                                        tempstr = "Bag";
                                    sdf.append("InsertDz" + StringUtil.escapeSortName(tempstr) + " ");
                                }
                            }
                        }
                        sdf.append("-> " + StringUtil.escapeSortName(p.getSort()));
                        sdf.append(SDFHelper.getSDFAttributes(p.getAttributes()) + "\n");
                    }
                    sdf.append("} > ");
                }
                sdf = new StringBuilder(sdf.substring(0, sdf.length() - 3) + "\n\n");
            }
        }
    }

    public Void visit(Restrictions node, Void _) {
        restrictions.add(node);
        return null;
    }
}
