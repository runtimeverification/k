package org.kframework.krun.gui.UIDesign;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.awt.geom.Point2D;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Pattern;
import javax.imageio.ImageIO;
import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JTabbedPane;
import javax.swing.JTextField;
import org.apache.commons.io.FileUtils;
import org.apache.commons.lang3.StringEscapeUtils;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.ConcretizeSyntax;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.Transition;
import org.kframework.krun.gui.Controller.RunKRunCommand;
import org.kframework.krun.gui.UIDesign.xmlEditor.XMLEditorKit;
import org.kframework.krun.gui.diff.DiffFrame;
import org.kframework.krun.gui.helper.HelpFrame;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitTypeCheckVisitor;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;
import edu.uci.ics.jung.algorithms.shortestpath.DijkstraShortestPath;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.visualization.GraphZoomScrollPane;
import edu.uci.ics.jung.visualization.VisualizationImageServer;
import edu.uci.ics.jung.visualization.control.CrossoverScalingControl;
import edu.uci.ics.jung.visualization.control.ScalingControl;
import edu.uci.ics.jung.visualization.subLayout.GraphCollapser;

//use generic graph since we modify it
@SuppressWarnings({ "rawtypes", "unchecked" })
public class GraphRepresentation extends JPanel implements ItemListener {

  private static final long serialVersionUID = 1017336668368978842L;
  private int index = 0;
  private VisualizationViewerDemo vvd;
  private GraphZoomScrollPane gzsp;
  private GraphCollapser collapser;
  private JPanel commandControl;
  private JTabbedPane tabbedPane;
  private ConfigurationPanel nodeInfo;
  private final JTextField numberField = new JTextField(5);
  private JLabel numberOfSteps;
  private JButton step;
  private JButton stepAll;
  private JButton collapse;
  private JButton expand;
  private JButton exit;
  private JButton compare;
  private JButton help;
  //private JButton edit;
  private RunKRunCommand commandProcessor;
  private final ScalingControl scaler = new CrossoverScalingControl();
  private Context definitionHelper;
  private int totalSelections;
  private boolean enabled;
  // keep track of number of selection
  private int nonKrunStateSelection;

  public GraphRepresentation(RunKRunCommand command, Context definitionHelper)
          throws Exception {
    this.definitionHelper = definitionHelper;
    tabbedPane = new JTabbedPane();
    initCommandProcessor(command);
    initGraph();
    initCollapser();
    initNodeInfoPanel();
    initCommandControlElements();
    addZoom();
    packComponents();
    // add listener for configuration selection
    vvd.getVv().getPickedVertexState().addItemListener(this);
    nonKrunStateSelection = 0;
    enabled = true;
    totalSelections = 0;
  }

  public void initCommandProcessor(RunKRunCommand command) {
    this.commandProcessor = command;
  }

  public void initGraph() throws Exception {
    Graph graph = null;
    try {
      graph = commandProcessor.firstStep(definitionHelper);
    } catch (IOException e) {
      e.printStackTrace();
      MainWindow.showAndExit(e);
    } catch (Exception e) {
      e.printStackTrace();
      MainWindow.showAndExit(e);
    }
    vvd = new VisualizationViewerDemo(graph, definitionHelper);
  }

  public void initCollapser() {
    collapser = new GraphCollapser(vvd.getLayout().getGraph());
  }

  public void initNodeInfoPanel()
  {
    nodeInfo = new ConfigurationPanel();
    Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
    nodeInfo.setPreferredSize(new Dimension(screenSize.width / 3, screenSize.height));
    nodeInfo.setBorder(BorderFactory.createTitledBorder("Configuration"));
  }

  public void initCommandControlElements() {
    commandControl = new JPanel();
    numberOfSteps = new JLabel("Input number of steps:");
    help = new JButton("Help");
    step = new JButton("Step");
    stepAll = new JButton("Step-all");
    collapse = new JButton("Collapse");
    expand = new JButton("Expand");
    exit = new JButton("Exit");
    compare = new JButton("Compare");
    compare.setEnabled(false);
    //edit = new JButton("Edit conf");
    addActionForHelpButton();
    addActionForStepButton();
    addActionForStepAllButton();
    addActionForCollapse();
    addActionForExpand();
    addActionForExit();
    addActionForCompare();
    addActionForEdit();
    // compare 2 selected nodes
    addCommandPanelElements();
  }

  public void addZoom() {
    gzsp = new GraphZoomScrollPane(vvd.getVv());
  }

  public void packComponents() {
    this.setLayout(new BorderLayout());
    JPanel controls = new JPanel();
    controls.add(commandControl);
    this.add(gzsp);
    // this.add(nodeInfo,BorderLayout.EAST);
    this.add(tabbedPane, BorderLayout.EAST);
    this.add(controls, BorderLayout.SOUTH);
  }

  public void addActionForHelpButton() {
    help.addActionListener(new ActionListener() {
      @SuppressWarnings("unused")
      public void actionPerformed(ActionEvent e) {
        HelpFrame helper = new HelpFrame(definitionHelper);
      }
    });
  }

  public void addActionForStepButton() {
    step.addActionListener(new ActionListener() {
      public void actionPerformed(ActionEvent e) {
        synchronized (ActionListener.class) {
          Object[] picked = vvd.getSelectedVertices().toArray();
          if (picked.length > 0) {
            for (int i = 0; i < picked.length; i++) {
              if (!(picked[i] instanceof KRunState))
                continue;
              KRunState pick = (KRunState) picked[i];
              try {
                // run command just for leaves
                if (vvd.getVv().getGraphLayout().getGraph().getSuccessorCount(pick) == 0) {
                  commandProcessor.step(pick, determineNoOfSteps());
                }
                // reset the selection
                vvd.getVv().getPickedVertexState().pick(pick, false);
              } catch (IOException e1) {
                e1.printStackTrace();
              } catch (Exception e1) {
                e1.printStackTrace();
              }
            }
            redrawGraphAndResetScroll();
          }
          else if (picked.length == 0) {
            showMessageOfSelectRequirement("Step");
          }
          resetNoOfSteps();
        }
      }
    });
  }

  public void addActionForStepAllButton() {
    stepAll.addActionListener(new ActionListener() {
      public void actionPerformed(ActionEvent e) {
        synchronized (ActionListener.class) {
          Object[] picked = vvd.getSelectedVertices().toArray();
          if (picked.length > 0) {
            for (int i = 0; i < picked.length; i++) {
              if (!(picked[i] instanceof KRunState))
                continue;
              KRunState pick = (KRunState) picked[i];
              try {
                // run command just for leaves
                if (vvd.getVv().getGraphLayout().getGraph().getSuccessorCount(pick) == 0
                        || picked.length == 1) {
                  commandProcessor.step_all(determineNoOfSteps(), pick);
                }
                // reset the selection
                vvd.getVv().getPickedVertexState().pick(pick, false);

              } catch (IOException e1) {
                e1.printStackTrace();
              } catch (Exception e1) {
                e1.printStackTrace();
              }
            }
            redrawGraphAndResetScroll();
          }
          else if (picked.length == 0) {
            showMessageOfSelectRequirement("Step-all");
          }
          resetNoOfSteps();
        }
      }
    });
  }

  public void addActionForCollapse() {
    collapse.addActionListener(new ActionListener() {
      public void actionPerformed(ActionEvent e) {
        Collection<KRunState> picked = new HashSet<KRunState>(vvd.getSelectedVertices());
        if (picked.size() > 1) {
          Graph<KRunState, Transition> inGraph = vvd.getLayout().getGraph();
          Graph clusterGraph = collapser.getClusterGraph(inGraph, picked);
          Graph g = collapser.collapse(vvd.getLayout().getGraph(), clusterGraph);
          double sumx = 0;
          double sumy = 0;
          for (Object v : picked) {
            Point2D p = (Point2D) vvd.getLayout().transform(v);
            sumx += p.getX();
            sumy += p.getY();
            // break;
          }
          Point2D cp = new Point2D.Double(sumx / picked.size(), sumy / picked.size());
          vvd.getVv().getRenderContext().getParallelEdgeIndexFunction().reset();
          vvd.getLayout().setGraph(g);
          vvd.getLayout().setLocation(clusterGraph, cp);
          vvd.getVv().getPickedVertexState().clear();
          vvd.getVv().repaint();
        }
      }
    });
  }

  public void addActionForExpand() {
    expand.addActionListener(new ActionListener() {
      public void actionPerformed(ActionEvent e) {
        Collection picked = new HashSet(vvd.getVv().getPickedVertexState().getPicked());
        for (Object v : picked) {
          if (v instanceof Graph) {
            Graph g = collapser.expand(vvd.getLayout().getGraph(), (Graph) v);
            vvd.getVv().getRenderContext().getParallelEdgeIndexFunction().reset();
            vvd.getLayout().setGraph(g);
            vvd.getLayout().resetGraphPosition(g);
          }
          vvd.getVv().getPickedVertexState().clear();
          vvd.getVv().repaint();
        }
      }
    });
  }

  public void addActionForExit() {
    exit.addActionListener(new ActionListener() {
      public void actionPerformed(ActionEvent e) {
        System.exit(0);
      }
    });
  }

  public void addActionForCompare() {
    compare.addActionListener(new ActionListener() {
      public void actionPerformed(ActionEvent e) {
        if (vvd == null) {
          return;
        }
        KRunState first = null, second = null;
        Set<KRunState> picked = vvd.getSelectedVertices();
        if (picked == null || picked.size() != 2) {
          showMessageOfSelectRequirement("Select two configurations to compare.");
          return;
        }
        for (KRunState krs : picked) {
          if (first == null) {
            first = krs;
          }
          else {
            second = krs;
          }
        }
        new DiffFrame(first, second, null, definitionHelper).setVisible(true);
      }
    });
  }

  public void addActionForEdit() {
    //    edit.addActionListener(new ActionListener() {
    //      public void actionPerformed(ActionEvent e) {
    //        if (vvd == null) {
    //          return;
    //        }
    //        Set<KRunState> picked = vvd.getSelectedVertices();
    //        if (picked == null || picked.size() != 1) {
    //          showMessageOfSelectRequirement("Select one configurations to edit.");
    //          return;
    //        }
    //        for (KRunState krs : picked) {
    //          ConfEditor confE = new ConfEditor(krs);
    //          confE.setVisible(true);
    //          KRunState t = confE.getKrunState();
    //          System.out.println(t.toString());
    //        }
    //      }
    //    });
  }

  public int determineNoOfSteps() {
    if (numberField.getText().isEmpty()
            || (Pattern.matches("[a-zA-Z]+", numberField.getText()) == true)) {
      return 1;
    }
    else {
      return Integer.parseInt(numberField.getText());
    }
  }

  public void resetNoOfSteps() {
    numberField.setText("");
  }

  public void showMessageOfSelectRequirement(String method) {
    JOptionPane.showMessageDialog(new JFrame("Selection needed"), "Select a vertex for the '"
            + method + "' method!");
  }

  public void showMessage(String message) {
    JOptionPane.showMessageDialog(new JFrame("Attention"), message, "",
            JOptionPane.INFORMATION_MESSAGE);
  }

  public void addCommandPanelElements() {
    commandControl.add(this.help);
    commandControl.add(this.step);
    commandControl.add(this.stepAll);
    commandControl.add(this.collapse);
    commandControl.add(this.expand);
    commandControl.add(this.numberOfSteps);
    commandControl.add(this.numberField);
    commandControl.add(this.compare);
    commandControl.add(this.exit);
    //    commandControl.add(this.edit);

  }

  public boolean findShortestPath(Object source, Object target, String rule) {
    DijkstraShortestPath<Object, Transition> shortestPath = new DijkstraShortestPath<Object, Transition>(
            (Graph) vvd.getLayout().getGraph());
    List<Transition> path = shortestPath.getPath(source, target);
    if (path.size() < 1) {
      return false;
    }
    else {
      for (Transition edge : path) {
        if (edge.getLabel().equals(Transition.TransitionType.UNLABELLED) && !rule.equals("")) {
          edge.setLabel(rule);
        }
      }
      return true;
    }
  }

  public void addNewGraphComponent(KRunState source, KRunState target, int depth, String rule) {
    setId(target);
    vvd.addEdge(source, target, depth, rule);
    vvd.resetGraphLayout();
  }

  public void setId(KRunState vertex) {
    vertex.setStateId(index);
    index++;
  }

  private static String getXmlFromKrunState(KRunState pick, Context definitionHelper) {
    // TO-DO : create our own filter that ignores xml characters from a tag
    StringBuffer rez = new StringBuffer();
    String str = getStrFromKrunState(pick, definitionHelper);
    for (String line : str.split("\n")) {
      line = line.trim();
      if (line.startsWith("<") && line.endsWith(">"))
        rez.append(line + "\n");
      else
        rez.append(StringEscapeUtils.escapeXml(line) + "\n");
    }
    return rez.toString();
  }

  private static String getStrFromKrunState(KRunState pick, Context definitionHelper) {
    Term term = pick.getResult();
    try {
      term = (Term) term.accept(new ConcretizeSyntax(definitionHelper));
      term = (Term) term.accept(new TypeInferenceSupremumFilter(definitionHelper));
      term = (Term) term.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(
              definitionHelper), definitionHelper));
      // as a last resort, undo concretization
      term = (Term) term.accept(new org.kframework.krun.FlattenDisambiguationFilter(
              definitionHelper));
    } catch (TransformerException e) {
      e.printStackTrace();
    }
    if (term.getClass() == Cell.class) {
      Cell generatedTop = (Cell) term;
      if (generatedTop.getLabel().equals("generatedTop")) {
        term = generatedTop.getContents();
      }
    }
    // set the color map
    ColorVisitor cv = new ColorVisitor(definitionHelper);
    term.accept(cv);

    UnparserFilter unparser = new UnparserFilter(true, false, definitionHelper);
    term.accept(unparser);
    return unparser.getResult();
  }

  
  public static void displayEdgeInfo(Transition pick, KRunState src, KRunState dest,
          Context definitionHelper) {
    new DiffFrame(src, dest, pick, definitionHelper).setVisible(true);
  }

  public void redrawGraphAndResetScroll() {
    Graph newGrapg = null;
    try {
      newGrapg = commandProcessor.getCurrentGraph();
    } catch (Exception e1) {
      e1.printStackTrace();
      return;
    }
    Graph oldGraph = vvd.getLayout().getGraph();
    for (Object v : newGrapg.getVertices()) {
      if (vvd.verifyExistingVertex(v) == null)

        oldGraph.addVertex(v);
    }
    for (Object e : newGrapg.getEdges()) {
      try {
        Object source, dest;
        source = newGrapg.getSource(e);
        dest = newGrapg.getDest(e);
        if (vvd.verifyCanAddEdge(source, dest)) {
          oldGraph.addEdge(e, source, dest);
        }
      }
      // should not happen
      catch (IllegalArgumentException iae) {
      }
    }
    vvd.resetGraphLayout();
    gzsp.revalidate();
    gzsp.repaint();
  }

  @Override
  public void itemStateChanged(ItemEvent event) {
    Object item = event.getItem();
    scaler.scale(vvd.getVv(), 1f, (Point2D) vvd.getLayout().transform(item));
    if (event.getStateChange() == ItemEvent.SELECTED) {
      totalSelections++;
    }
    else {
      totalSelections--;
    }
    totalSelections = vvd.getSelectedVertices().size();
    if (!(item instanceof KRunState)) {
      // when a non KrunState vertex is selected disable the
      // (step/step-all/compare) buttons
      if (event.getStateChange() == ItemEvent.SELECTED) {
        nonKrunStateSelection++;
        changeBttnsEnableStatus(false);
      }
      else {
        nonKrunStateSelection--;
        if (nonKrunStateSelection == 0 && totalSelections > 0) {
          changeBttnsEnableStatus(true);
        }
      }
    }
    else {
      if (nonKrunStateSelection == 0 && totalSelections > 0) {
        changeBttnsEnableStatus(true);
      }
      else {
        changeBttnsEnableStatus(false);
      }
    }
    if (totalSelections == 2 && nonKrunStateSelection == 0) {
      changeCompareStatus(true);
    }
    else {
      changeCompareStatus(false);
    }
    if (totalSelections == 1 && nonKrunStateSelection == 0) {
      changeEditStatus(true);
    }
    else {
      changeEditStatus(false);
    }
    if (totalSelections > 1) {
      changeCollapseStatus(true);
    }
    else {
      changeCollapseStatus(false);
    }

    if (nonKrunStateSelection == 1) {
      changeExpandStatus(true);
    }
    else {
      changeExpandStatus(false);
    }
    // add remove from configuration pane
    if (item instanceof KRunState) {
      KRunState sel = (KRunState) item;
      if (event.getStateChange() == ItemEvent.SELECTED) {
        addConfToTabbed(sel);
      }
      else {
        removeFromConfTabbed(sel);
      }
    }
  }

  public void removeFromConfTabbed(KRunState pick) {
    // find the index
    int index = -1;
    for (int i = 0; i < tabbedPane.getTabCount(); i++) {
      if (tabbedPane.getTitleAt(i).contains(pick.getStateId() + "")) {
        index = i;
        break;
      }
    }
    if (index != -1) {
      tabbedPane.remove(index);
    }
  }

  public void addConfToTabbed(KRunState pick) {
    ConfigurationPanel conf = new ConfigurationPanel();
    // nodeInfo.init(getXmlFromKrunState(pick,definitionHelper));
    conf.init(getXmlFromKrunState(pick, definitionHelper));
    XMLEditorKit.collapseMemorizedTags();
    tabbedPane.addTab("Config " + pick.getStateId(), conf);
    tabbedPane.setSelectedIndex(tabbedPane.getTabCount() - 1);
  }

  public void changeBttnsEnableStatus(boolean status) {
    if (enabled == status)
      return;
    step.setEnabled(status);
    stepAll.setEnabled(status);
    numberField.setEnabled(status);
    enabled = status;
  }

  public void changeCompareStatus(boolean status) {
    compare.setEnabled(status);
  }

  public void changeExpandStatus(boolean status) {
    expand.setEnabled(status);
  }

  public void changeCollapseStatus(boolean status) {
    collapse.setEnabled(status);
  }

  public void changeEditStatus(boolean status) {
    //    edit.setEnabled(status);
  }

  public void savePng(String file){
    VisualizationImageServer<KRunState, Transition> vis =
            new VisualizationImageServer<KRunState, Transition>(vvd.getVv().getGraphLayout(),
                    vvd.getVv().getGraphLayout().getSize());
    vis.setBackground(Color.WHITE);
    BufferedImage image = (BufferedImage) vis.getImage(
            new Point2D.Double(vvd.getVv().getGraphLayout().getSize().getWidth() / 2,
                    vvd.getVv().getGraphLayout().getSize().getHeight() / 2),
                    new Dimension(vvd.getVv().getGraphLayout().getSize()));
    // Write image to a png file
    File outputfile = new File(file);

    try {
      ImageIO.write(image, "png", outputfile);
    } catch (IOException e) {
      // Exception handling
    }
  }
  
  private boolean saveConf(String folder,KRunState conf){
    String confStr = getStrFromKrunState(conf, definitionHelper);
    File out= new File(folder+File.separator + "conf"+conf.getStateId()); 
    try {
      FileUtils.writeStringToFile(out, confStr);
    } catch (IOException e) {
      e.printStackTrace();
      return false; 
    }
    return true ; 
  }
  
  public void saveSelectedConf(String folder){
    Object[] picked = vvd.getSelectedVertices().toArray();
    if (picked.length > 0) {
      for (int i = 0; i < picked.length; i++) {
        if (!(picked[i] instanceof KRunState))
          continue;
        KRunState pick = (KRunState) picked[i];
        saveConf(folder, pick);
      }
      showMessage("Selected configs saved in : \n" +(new File(folder).getPath()) );
    }
  }
}
