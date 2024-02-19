// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

package org.kframework.builtin;

import static org.kframework.kore.KORE.KLabel;

import org.kframework.kore.KLabel;

public class KLabels {
  public static final KLabel AND = KLabel("_andBool_");
  public static final KLabel OR = KLabel("_orBool_");

  public static final KLabel KSEQ = KLabel("#KSequence");
  public static final KLabel DOTK = KLabel("#EmptyK");

  public static final KLabel CELLS = KLabel("#cells");

  public static final KLabel DOTS = KLabel("#dots");
  public static final KLabel NO_DOTS = KLabel("#noDots");

  public static final KLabel KREWRITE = KLabel("#KRewrite");
  public static final KLabel KLIST = KLabel("#KList");
  public static final KLabel EMPTYKLIST = KLabel("#EmptyKList");
  public static final KLabel KAPP = KLabel("#KApply");

  public static final String GENERATED_TOP_CELL_NAME = "generatedTop";
  public static final KLabel GENERATED_TOP_CELL = KLabel("<generatedTop>");
  public static final String GENERATED_COUNTER_CELL_NAME = "generatedCounter";
  public static final KLabel GENERATED_COUNTER_CELL = KLabel("<generatedCounter>");
  public static final KLabel INIT_GENERATED_TOP_CELL = KLabel("initGeneratedTopCell");
  public static final KLabel INIT_GENERATED_COUNTER_CELL = KLabel("initGeneratedCounterCell");
  public static final String THIS_CONFIGURATION = "THIS_CONFIGURATION";

  public static final KLabel STRATEGY_CELL = KLabel("<s>");
  public static final KLabel STUCK = KLabel("#STUCK");

  public static final KLabel ML_FALSE = KLabel("#Bottom");
  public static final KLabel ML_TRUE = KLabel("#Top");
  public static final KLabel ML_OR = KLabel("#Or");
  public static final KLabel ML_AND = KLabel("#And");
  public static final KLabel ML_NOT = KLabel("#Not");
  public static final KLabel ML_CEIL = KLabel("#Ceil");
  public static final KLabel ML_FLOOR = KLabel("#Floor");
  public static final KLabel ML_EQUALS = KLabel("#Equals");
  public static final KLabel ML_IMPLIES = KLabel("#Implies");
  public static final KLabel ML_EXISTS = KLabel("#Exists");
  public static final KLabel ML_FORALL = KLabel("#Forall");
  public static final KLabel CTL_AG = KLabel("#AG");
  public static final KLabel RL_wEF = KLabel("weakExistsFinally");
  public static final KLabel RL_wAF = KLabel("weakAlwaysFinally");

  public static final KLabel ListItem = KLabel("ListItem");
  public static final KLabel List = KLabel("_List_");
  public static final KLabel DotList = KLabel(".List");
  public static final KLabel MapItem = KLabel("_|->_");
  public static final KLabel Map = KLabel("_Map_");
  public static final KLabel DotMap = KLabel(".Map");
  public static final KLabel SetItem = KLabel("SetItem");
  public static final KLabel Set = KLabel("_Set_");
  public static final KLabel DotSet = KLabel(".Set");

  public static final KLabel NOT_EQUALS_K = KLabel("_=/=K_");
  public static final KLabel IN_K = KLabel("_:=K_");
  public static final KLabel NOT_IN_K = KLabel("_:/=K_");

  public static final KLabel MAP_LOOKUP = KLabel("Map:lookup");

  public static final String INJ = "inj";
}
