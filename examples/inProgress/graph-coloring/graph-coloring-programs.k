kmod GRAPH-COLORING-PROGRAMS is including DOT
  syntax K ::= Program
  syntax Program ::= pcolors | pcards | pcg | png | full

  macro pcolors =
Graph(
  None()
, GraphKwd()
, Some("colors")
, Some(
    Seq(
      NodeStmt(NodeID("red"), None())
    , Seq(
        NodeStmt(NodeID("green"), None())
      , Seq(
          NodeStmt(NodeID("blue"), None())
        , Seq(
            NodeStmt(NodeID("purple"), None())
          , NodeStmt(
              NodeID("master")
            , Some(Attr(Some(AttrIDAssign("type", "master"))))
            )
          )
        )
      )
    )
  )
)


  macro pcards =
Graph(
  None()
, GraphKwd()
, Some("cards")
, Some(
    Seq(
      EdgeStmt(NodeID("ae"), EdgeRHS(EdgeOpUndirected(), NodeID("A1")), None())
    , Seq(
        EdgeStmt(NodeID("bf"), EdgeRHS(EdgeOpUndirected(), NodeID("A1")), None())
      , Seq(
          EdgeStmt(NodeID("bf"), EdgeRHS(EdgeOpUndirected(), NodeID("A2")), None())
        , Seq(
            EdgeStmt(NodeID("cf"), EdgeRHS(EdgeOpUndirected(), NodeID("A2")), None())
          , Seq(
              EdgeStmt(NodeID("dg"), EdgeRHS(EdgeOpUndirected(), NodeID("A2")), None())
            , Seq(
                EdgeStmt(NodeID("eh"), EdgeRHS(EdgeOpUndirected(), NodeID("A1")), None())
              , Seq(
                  EdgeStmt(NodeID("eh"), EdgeRHS(EdgeOpUndirected(), NodeID("B1")), None())
                , Seq(
                    EdgeStmt(NodeID("fe"), EdgeRHS(EdgeOpUndirected(), NodeID("A1")), None())
                  , Seq(
                      EdgeStmt(NodeID("fe"), EdgeRHS(EdgeOpUndirected(), NodeID("A2")), None())
                    , Seq(
                        EdgeStmt(NodeID("fg"), EdgeRHS(EdgeOpUndirected(), NodeID("A2")), None())
                      , Seq(
                          EdgeStmt(NodeID("gi"), EdgeRHS(EdgeOpUndirected(), NodeID("A2")), None())
                        , Seq(
                            EdgeStmt(NodeID("gi"), EdgeRHS(EdgeOpUndirected(), NodeID("B2")), None())
                          , Seq(
                              EdgeStmt(NodeID("gl"), EdgeRHS(EdgeOpUndirected(), NodeID("A2")), None())
                            , Seq(
                                EdgeStmt(NodeID("gl"), EdgeRHS(EdgeOpUndirected(), NodeID("B2")), None())
                              , Seq(
                                  EdgeStmt(NodeID("hi"), EdgeRHS(EdgeOpUndirected(), NodeID("B1")), None())
                                , Seq(
                                    EdgeStmt(NodeID("hj"), EdgeRHS(EdgeOpUndirected(), NodeID("B1")), None())
                                  , Seq(
                                      EdgeStmt(NodeID("hj"), EdgeRHS(EdgeOpUndirected(), NodeID("B2")), None())
                                    , EdgeStmt(NodeID("ik"), EdgeRHS(EdgeOpUndirected(), NodeID("B2")), None())
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

  macro pcg = 
Graph(
  None()
, DigraphKwd()
, Some("cg")
, Some(
    Seq(
      EdgeStmt(
        NodeID("a")
      , EdgeRHS(EdgeOpDirected(), NodeID("e"))
      , Some(
          Attr(
            Some(
              Seq(
                AttrIDAssign("name", "ae")
              , Seq(AttrIDAssign("color", "red"), AttrIDAssign("cost", "8"))
              )
            )
          )
        )
      )
    , Seq(
        EdgeStmt(
          NodeID("b")
        , EdgeRHS(EdgeOpDirected(), NodeID("f"))
        , Some(
            Attr(
              Some(
                Seq(
                  AttrIDAssign("name", "bf")
                , Seq(AttrIDAssign("color", "green"), AttrIDAssign("cost", "8"))
                )
              )
            )
          )
        )
      , Seq(
          EdgeStmt(
            NodeID("c")
          , EdgeRHS(EdgeOpDirected(), NodeID("f"))
          , Some(
              Attr(
                Some(
                  Seq(
                    AttrIDAssign("name", "cf")
                  , Seq(AttrIDAssign("color", "red"), AttrIDAssign("cost", "5"))
                  )
                )
              )
            )
          )
        , Seq(
            EdgeStmt(
              NodeID("d")
            , EdgeRHS(EdgeOpDirected(), NodeID("g"))
            , Some(
                Attr(
                  Some(
                    Seq(
                      AttrIDAssign("name", "dg")
                    , Seq(AttrIDAssign("color", "blue"), AttrIDAssign("cost", "8"))
                    )
                  )
                )
              )
            )
          , Seq(
              EdgeStmt(
                NodeID("e")
              , EdgeRHS(EdgeOpDirected(), NodeID("h"))
              , Some(
                  Attr(
                    Some(
                      Seq(
                        AttrIDAssign("name", "eh")
                      , Seq(AttrIDAssign("color", "green"), AttrIDAssign("cost", "3"))
                      )
                    )
                  )
                )
              )
            , Seq(
                EdgeStmt(
                  NodeID("f")
                , EdgeRHS(EdgeOpDirected(), NodeID("e"))
                , Some(
                    Attr(
                      Some(
                        Seq(
                          AttrIDAssign("name", "fe")
                        , Seq(AttrIDAssign("color", "purple"), AttrIDAssign("cost", "3"))
                        )
                      )
                    )
                  )
                )
              , Seq(
                  EdgeStmt(
                    NodeID("f")
                  , EdgeRHS(EdgeOpDirected(), NodeID("g"))
                  , Some(
                      Attr(
                        Some(
                          Seq(
                            AttrIDAssign("name", "fg")
                          , Seq(AttrIDAssign("color", "green"), AttrIDAssign("cost", "3"))
                          )
                        )
                      )
                    )
                  )
                , Seq(
                    EdgeStmt(
                      NodeID("g")
                    , EdgeRHS(EdgeOpDirected(), NodeID("i"))
                    , Some(
                        Attr(
                          Some(
                            Seq(
                              AttrIDAssign("name", "gi")
                            , Seq(AttrIDAssign("color", "purple"), AttrIDAssign("cost", "5"))
                            )
                          )
                        )
                      )
                    )
                  , Seq(
                      EdgeStmt(
                        NodeID("g")
                      , EdgeRHS(EdgeOpDirected(), NodeID("l"))
                      , Some(
                          Attr(
                            Some(
                              Seq(
                                AttrIDAssign("name", "gl")
                              , Seq(AttrIDAssign("color", "red"), AttrIDAssign("cost", "13"))
                              )
                            )
                          )
                        )
                      )
                    , Seq(
                        EdgeStmt(
                          NodeID("h")
                        , EdgeRHS(EdgeOpDirected(), NodeID("j"))
                        , Some(
                            Attr(
                              Some(
                                Seq(
                                  AttrIDAssign("name", "hj")
                                , Seq(AttrIDAssign("color", "green"), AttrIDAssign("cost", "6"))
                                )
                              )
                            )
                          )
                        )
                      , Seq(
                          EdgeStmt(
                            NodeID("h")
                          , EdgeRHS(EdgeOpDirected(), NodeID("i"))
                          , Some(
                              Attr(
                                Some(
                                  Seq(
                                    AttrIDAssign("name", "hi")
                                  , Seq(AttrIDAssign("color", "blue"), AttrIDAssign("cost", "8"))
                                  )
                                )
                              )
                            )
                          )
                        , EdgeStmt(
                            NodeID("i")
                          , EdgeRHS(EdgeOpDirected(), NodeID("k"))
                          , Some(
                              Attr(
                                Some(
                                  Seq(
                                    AttrIDAssign("name", "ik")
                                  , Seq(AttrIDAssign("color", "blue"), AttrIDAssign("cost", "5"))
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

  macro png =
Graph(
  None()
, DigraphKwd()
, Some("ng")
, Some(
    Seq(
      EdgeStmt(
        NodeID("master")
      , EdgeRHS(EdgeOpDirected(), NodeID("red"))
      , Some(
          Attr(
            Some(Seq(AttrIDAssign("length", "2"), AttrIDAssign("cost", "0")))
          )
        )
      )
    , Seq(
        EdgeStmt(
          NodeID("master")
        , EdgeRHS(EdgeOpDirected(), NodeID("green"))
        , Some(
            Attr(
              Some(Seq(AttrIDAssign("length", "3"), AttrIDAssign("cost", "0")))
            )
          )
        )
      , Seq(
          EdgeStmt(
            NodeID("master")
          , EdgeRHS(EdgeOpDirected(), NodeID("blue"))
          , Some(
              Attr(
                Some(Seq(AttrIDAssign("length", "3"), AttrIDAssign("cost", "0")))
              )
            )
          )
        , Seq(
            EdgeStmt(
              NodeID("master")
            , EdgeRHS(EdgeOpDirected(), NodeID("purple"))
            , Some(
                Attr(
                  Some(Seq(AttrIDAssign("length", "2"), AttrIDAssign("cost", "0")))
                )
              )
            )
          , Seq(
              EdgeStmt(
                NodeID("red")
              , EdgeRHS(EdgeOpDirected(), NodeID("master"))
              , Some(
                  Attr(
                    Some(Seq(AttrIDAssign("length", "2"), AttrIDAssign("cost", "20")))
                  )
                )
              )
            , Seq(
                EdgeStmt(
                  NodeID("red")
                , EdgeRHS(EdgeOpDirected(), NodeID("green"))
                , Some(
                    Attr(
                      Some(Seq(AttrIDAssign("length", "3"), AttrIDAssign("cost", "10")))
                    )
                  )
                )
              , Seq(
                  EdgeStmt(
                    NodeID("red")
                  , EdgeRHS(EdgeOpDirected(), NodeID("purple"))
                  , Some(
                      Attr(
                        Some(Seq(AttrIDAssign("length", "3"), AttrIDAssign("cost", "10")))
                      )
                    )
                  )
                , Seq(
                    EdgeStmt(
                      NodeID("blue")
                    , EdgeRHS(EdgeOpDirected(), NodeID("master"))
                    , Some(
                        Attr(
                          Some(Seq(AttrIDAssign("length", "3"), AttrIDAssign("cost", "10")))
                        )
                      )
                    )
                  , Seq(
                      EdgeStmt(
                        NodeID("blue")
                      , EdgeRHS(EdgeOpDirected(), NodeID("red"))
                      , Some(
                          Attr(
                            Some(Seq(AttrIDAssign("length", "2"), AttrIDAssign("cost", "0")))
                          )
                        )
                      )
                    , Seq(
                        EdgeStmt(
                          NodeID("blue")
                        , EdgeRHS(EdgeOpDirected(), NodeID("green"))
                        , Some(
                            Attr(
                              Some(Seq(AttrIDAssign("length", "2"), AttrIDAssign("cost", "0")))
                            )
                          )
                        )
                      , Seq(
                          EdgeStmt(
                            NodeID("green")
                          , EdgeRHS(EdgeOpDirected(), NodeID("blue"))
                          , Some(
                              Attr(
                                Some(Seq(AttrIDAssign("length", "2"), AttrIDAssign("cost", "0")))
                              )
                            )
                          )
                        , Seq(
                            EdgeStmt(
                              NodeID("green")
                            , EdgeRHS(EdgeOpDirected(), NodeID("red"))
                            , Some(
                                Attr(
                                  Some(Seq(AttrIDAssign("length", "3"), AttrIDAssign("cost", "20")))
                                )
                              )
                            )
                          , Seq(
                              EdgeStmt(
                                NodeID("purple")
                              , EdgeRHS(EdgeOpDirected(), NodeID("master"))
                              , Some(
                                  Attr(
                                    Some(Seq(AttrIDAssign("length", "2"), AttrIDAssign("cost", "0")))
                                  )
                                )
                              )
                            , Seq(
                                EdgeStmt(
                                  NodeID("purple")
                                , EdgeRHS(EdgeOpDirected(), NodeID("red"))
                                , Some(
                                    Attr(
                                      Some(Seq(AttrIDAssign("length", "3"), AttrIDAssign("cost", "20")))
                                    )
                                  )
                                )
                              , Seq(
                                  EdgeStmt(
                                    NodeID("purple")
                                  , EdgeRHS(EdgeOpDirected(), NodeID("blue"))
                                  , Some(
                                      Attr(
                                        Some(Seq(AttrIDAssign("length", "3"), AttrIDAssign("cost", "10")))
                                      )
                                    )
                                  )
                                , EdgeStmt(
                                    NodeID("purple")
                                  , EdgeRHS(EdgeOpDirected(), NodeID("green"))
                                  , Some(
                                      Attr(
                                        Some(Seq(AttrIDAssign("length", "2"), AttrIDAssign("cost", "10")))
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

  macro full = Seq(pcolors, Seq(pcg, Seq(pcards, png)))

endkm
