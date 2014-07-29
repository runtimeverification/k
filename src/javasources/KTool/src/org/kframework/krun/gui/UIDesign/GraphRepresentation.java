// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.UIDesign;

import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.Transition;
import org.kframework.krun.gui.Controller.RunKRunCommand;
import org.kframework.krun.gui.Controller.XmlUnparseFilter;
import org.kframework.krun.gui.UIDesign.xmlEditor.XMLEditorKit;
import org.kframework.krun.gui.diff.DiffFrame;
import org.kframework.krun.gui.helper.HelpFrame;
import org.kframework.utils.BinaryLoader;

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
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Pattern;

import javax.imageio.ImageIO;
import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JTabbedPane;
import javax.swing.JTextField;
import javax.swing.filechooser.FileNameExtensionFilter;

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
    private final static String SAVED_CONF_EXT = "sconf";
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
    // private JButton edit;
    private RunKRunCommand commandProcessor;
    private final ScalingControl scaler = new CrossoverScalingControl();
    private Context definitionHelper;
    private int totalSelections;
    private boolean enabled;
    // keep track of number of selection
    private int nonKrunStateSelection;

    public GraphRepresentation(RunKRunCommand command) {
        this.definitionHelper = command.getContext();
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

    public void initGraph() {
        Graph graph = null;
        graph = commandProcessor.firstStep();
        vvd = new VisualizationViewerDemo(graph, this);
    }

    public void initCollapser() {
        collapser = new GraphCollapser(vvd.getLayout().getGraph());
    }

    public void initNodeInfoPanel() {
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
        // TODO finish implementation
        // edit = new JButton("Edit conf");
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

    public Context getDefinitionHelper() {
        return definitionHelper;
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

                    int oldNoOfVertices = vvd.getLayout().getGraph().getVertexCount();
                    Object[] picked = vvd.getSelectedVertices().toArray();
                    int noOfSteps = determineNoOfSteps();
                    if (picked.length > 0) {
                        for (int i = 0; i < picked.length; i++) {

                            if (!(picked[i] instanceof KRunState)){
                                continue;
                            }
                            KRunState pick = (KRunState) picked[i];
                            try {
                                commandProcessor.step(pick, determineNoOfSteps());

                                // reset the selection
                                vvd.getVv().getPickedVertexState().pick(pick, false);
                                // enable selection of the results

                                int newNoOfVertices = vvd.getLayout().getGraph().getVertexCount();
                                if(newNoOfVertices == oldNoOfVertices)
                                {
                                    selectActionStepResults(pick, 0, noOfSteps);
                                }
                            } catch (KRunExecutionException e1) {
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

    public void selectActionStepResults(KRunState vertex, int step, int totalSteps){
        if(step >= totalSteps){
            return;
        }
        else{
            Object[] successors = vvd.getLayout().getGraph().getSuccessors(vertex).toArray();
            if(++step == totalSteps){
                vvd.getVv().getPickedVertexState().pick(successors[0], true);
                return;
            }
            else{
                selectActionStepResults((KRunState)successors[0], step, totalSteps);
            }
        }

    }

    public void addActionForStepAllButton() {
        stepAll.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                synchronized (ActionListener.class) {
                    int oldNoOfVertices = vvd.getLayout().getGraph().getVertexCount();
                    int noOfSteps = determineNoOfSteps();
                    Object[] picked = vvd.getSelectedVertices().toArray();
                    if (picked.length > 0) {
                        for (int i = 0; i < picked.length; i++) {
                            if (!(picked[i] instanceof KRunState))
                                continue;
                            KRunState pick = (KRunState) picked[i];
                            try {
                                // run command just for leaves
                                //if (vvd.getVv().getGraphLayout().getGraph().getSuccessorCount(pick) == 0
                                //      || picked.length == 1) {
                                commandProcessor.step_all(determineNoOfSteps(), pick);
                                //}
                                // reset the selection
                                vvd.getVv().getPickedVertexState().pick(pick, false);

                                int newNoOfVertices = vvd.getLayout().getGraph().getVertexCount();
                                if(newNoOfVertices == oldNoOfVertices)
                                {
                                    selectActionStepAllResults(pick, 0, noOfSteps);
                                }

                            } catch (KRunExecutionException e1) {
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

    public void selectActionStepAllResults(KRunState vertex, int step, int totalSteps){
        if(step >= totalSteps){
            return;
        }
        else{
            Object[] successors = vvd.getLayout().getGraph().getSuccessors(vertex).toArray();
            if(++step == totalSteps){
                for(int i = 0; i < successors.length; i++){
                    vvd.getVv().getPickedVertexState().pick(successors[i], true);
                }
                return;
            }
            else{
                for(int i = 0; i < successors.length; i++){

                    selectActionStepAllResults((KRunState)successors[0], step, totalSteps);
                }
            }
        }

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
                synchronized(MainWindow.instance().lock) {
                    MainWindow.instance().lock.notify();
                }
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
                    } else {
                        second = krs;
                    }
                }
                showCompareFrame(first, second, null);
            }
        });
    }

    public void showCompareFrame(KRunState first, KRunState second, Transition transition) {
        new DiffFrame(first, second, null, definitionHelper).setVisible(true);
    }

    public void addActionForEdit() {
        // edit.addActionListener(new ActionListener() {
        // public void actionPerformed(ActionEvent e) {
        // if (vvd == null) {
        // return;
        // }
        // Set<KRunState> picked = vvd.getSelectedVertices();
        // if (picked == null || picked.size() != 1) {
        // showMessageOfSelectRequirement("Select one configurations to edit.");
        // return;
        // }
        // for (KRunState krs : picked) {
        // ConfEditor confE = new ConfEditor(krs);
        // confE.setVisible(true);
        // KRunState t = confE.getKrunState();
        // System.out.println(t.toString());
        // }
        // }
        // });
    }

    public int determineNoOfSteps() {
        if (numberField.getText().isEmpty()
                || (Pattern.matches("[a-zA-Z]+", numberField.getText()) == true)) {
            return 1;
        } else {
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
        // TODO finish implementation
        // commandControl.add(this.edit);
    }

    public boolean findShortestPath(Object source, Object target, String rule) {
        DijkstraShortestPath<Object, Transition> shortestPath = new DijkstraShortestPath<Object, Transition>(
                (Graph) vvd.getLayout().getGraph());
        List<Transition> path = shortestPath.getPath(source, target);
        if (path.size() < 1) {
            return false;
        } else {
            for (Transition edge : path) {
                if (edge.getLabel().equals(Transition.TransitionType.UNLABELLED)
                        && !rule.equals("")) {
                    edge.setLabel(rule);
                }
            }
            return true;
        }
    }

    public void redrawGraphAndResetScroll() {
        Graph newGrapg = null;
        newGrapg = commandProcessor.getCurrentGraph();
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
        } else {
            totalSelections--;
        }
        totalSelections = vvd.getSelectedVertices().size();
        if (!(item instanceof KRunState)) {
            // when a non KrunState vertex is selected disable the
            // (step/step-all/compare) buttons
            if (event.getStateChange() == ItemEvent.SELECTED) {
                nonKrunStateSelection++;
                changeBttnsEnableStatus(false);
            } else {
                nonKrunStateSelection--;
                if (nonKrunStateSelection == 0 && totalSelections > 0) {
                    changeBttnsEnableStatus(true);
                }
            }
        } else {
            if (nonKrunStateSelection == 0 && totalSelections > 0) {
                changeBttnsEnableStatus(true);
            } else {
                changeBttnsEnableStatus(false);
            }
        }
        if (totalSelections == 2 && nonKrunStateSelection == 0) {
            changeCompareStatus(true);
        } else {
            changeCompareStatus(false);
        }
        if (totalSelections == 1 && nonKrunStateSelection == 0) {
            changeEditStatus(true);
        } else {
            changeEditStatus(false);
        }
        if (totalSelections > 1) {
            changeCollapseStatus(true);
        } else {
            changeCollapseStatus(false);
        }

        if (nonKrunStateSelection == 1) {
            changeExpandStatus(true);
        } else {
            changeExpandStatus(false);
        }
        // add remove from configuration pane
        if (item instanceof KRunState) {
            KRunState sel = (KRunState) item;
            if (event.getStateChange() == ItemEvent.SELECTED) {
                addConfToTabbed(sel);
            } else {
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
        // edit.setEnabled(status);
    }

    public void savePng(String file) {
        VisualizationImageServer<KRunState, Transition> vis = new VisualizationImageServer<KRunState, Transition>(
                vvd.getVv().getGraphLayout(), vvd.getVv().getGraphLayout().getSize());
        vis.setBackground(Color.WHITE);
        BufferedImage image = (BufferedImage) vis.getImage(new Point2D.Double(vvd.getVv()
                .getGraphLayout().getSize().getWidth() / 2, vvd.getVv().getGraphLayout().getSize()
                .getHeight() / 2), new Dimension(vvd.getVv().getGraphLayout().getSize()));
        // Write image to a png file
        File outputfile = new File(file);

        try {
            ImageIO.write(image, "png", outputfile);
            showMessage("Png saved in :" + outputfile.getCanonicalPath());
        } catch (IOException e) {
            try {
                showMessage("Unable to save png to file :" + outputfile.getCanonicalPath());
            } catch (IOException e1) {
            }
        }
    }

    private boolean saveConf(String folder, KRunState conf) {
        File f = new File(folder + File.separator + "confSer" + conf.getStateId() + ".serConf");
        return saveConf(f, conf);
    }

    private boolean saveConf(File file, KRunState conf) {
        FileOutputStream outObj;
        try {
            outObj = new FileOutputStream(file);
            ObjectOutputStream s = new ObjectOutputStream(outObj);
            s.writeObject(conf);
            s.flush();
            s.close();
        } catch (FileNotFoundException e1) {
            e1.printStackTrace();
            return false;
        } catch (IOException e) {
            e.printStackTrace();
            return false;
        }
        return true;
    }

    public void saveSelectedConf() {
        Object[] picked = vvd.getSelectedVertices().toArray();
        if (picked.length > 0) {
            KRunState conf = (KRunState) picked[0];
            JFileChooser chooser = new JFileChooser();
            chooser.setCurrentDirectory(new java.io.File("."));
            chooser.setAcceptAllFileFilterUsed(false);
            chooser.setDialogTitle("Choose where to save configuration");
            if (picked.length == 1) {
                FileNameExtensionFilter filter = new FileNameExtensionFilter(
                        "Serialized configuration(*." + SAVED_CONF_EXT + ")", SAVED_CONF_EXT);
                chooser.setFileFilter(filter);
                chooser.setSelectedFile(new File("conf" + conf.getStateId() + "." + SAVED_CONF_EXT));
                int returnVal = chooser.showSaveDialog(this);
                if (returnVal == JFileChooser.APPROVE_OPTION) {
                    File file = chooser.getSelectedFile();
                    File toSaveFile;
                    if (!file.getName().endsWith(SAVED_CONF_EXT)) {
                        toSaveFile = new File(file.getParent(), file.getName() + "."
                                + SAVED_CONF_EXT);
                    } else {
                        toSaveFile = file;
                    }
                    if (toSaveFile.exists()) {
                        if (JOptionPane.showConfirmDialog(null,
                                "Selected file already exists. Override ?", "File exists",
                                JOptionPane.YES_NO_OPTION) != JOptionPane.YES_OPTION) {
                            return;
                        }
                    }
                    saveConf(toSaveFile, conf);
                }
            } else {
                chooser.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
                int returnVal = chooser.showSaveDialog(this);
                String dirPath = null;
                if (returnVal == JFileChooser.APPROVE_OPTION) {
                    File file = chooser.getSelectedFile();
                    dirPath = file.getAbsolutePath();
                } else {
                    return;
                }
                for (int i = 0; i < picked.length; i++) {
                    if (!(picked[i] instanceof KRunState))
                        continue;
                    saveConf(dirPath, (KRunState) picked[i]);
                }
            }
        }
    }

    private KRunState loadConf(File f) {
        return BinaryLoader.loadOrDie(KRunState.class, f.getAbsolutePath());
    }

    public void loadConf() {
        FileNameExtensionFilter filter = new FileNameExtensionFilter("Serialized configuration",
                SAVED_CONF_EXT);
        JFileChooser fc = new JFileChooser();
        fc.addChoosableFileFilter(filter);
        fc.setCurrentDirectory(new File("."));
        int returnVal = fc.showOpenDialog(gzsp);
        if (returnVal == JFileChooser.APPROVE_OPTION) {
            File file = fc.getSelectedFile();
            try {
                KRunState conf = loadConf(file);
                // addConfToTabbed(conf);
                MainWindow.addDebugTab(new GraphRepresentation(new RunKRunCommand(conf,
                        commandProcessor.getKrun(),
                        definitionHelper)),
                        "Tab resulted from loading :" + file.getName());
            } catch (ClassCastException e) {
                showMessage("Unable to load configuration from file");
            }
        }

    }

    private static String getXmlFromKrunState(KRunState pick, Context definitionHelper) {
        Term term = pick.getResult();
        if (term.getClass() == Cell.class) {
            Cell generatedTop = (Cell) term;
            if (generatedTop.getLabel().equals("generatedTop")) {
                term = generatedTop.getContents();
            }
        }
        // set the color map
        ColorVisitor cv = new ColorVisitor(definitionHelper);
        cv.visitNode(term);

        XmlUnparseFilter unparser = new XmlUnparseFilter(true, false, definitionHelper);
        unparser.visitNode(term);
        return unparser.getResult();
    }
}

