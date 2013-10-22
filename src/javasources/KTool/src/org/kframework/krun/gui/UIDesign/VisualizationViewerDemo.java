package org.kframework.krun.gui.UIDesign;

import java.awt.BasicStroke;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Paint;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import org.apache.commons.collections15.Predicate;
import org.apache.commons.collections15.Transformer;
import org.apache.commons.collections15.functors.ConstantTransformer;
import org.kframework.kil.loader.Context;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.Transition;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.visualization.DefaultVisualizationModel;
import edu.uci.ics.jung.visualization.VisualizationModel;
import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.control.DefaultModalGraphMouse;
import edu.uci.ics.jung.visualization.control.ModalGraphMouse;
import edu.uci.ics.jung.visualization.decorators.EdgeShape;
import edu.uci.ics.jung.visualization.decorators.ToStringLabeller;
import edu.uci.ics.jung.visualization.renderers.DefaultVertexLabelRenderer;
import edu.uci.ics.jung.visualization.renderers.GradientVertexRenderer;
import edu.uci.ics.jung.visualization.renderers.VertexLabelAsShapeRenderer;
import edu.uci.ics.jung.visualization.util.PredicatedParallelEdgeIndexFunction;

@SuppressWarnings({ "rawtypes", "unchecked" })
public class VisualizationViewerDemo {

  private DynamicLayout layout;
  public static final int distanceParentChild = 100;
  public static final int distanceSameLevelNodes = 100;
  private VisualizationViewer<KRunState, Transition> vv;
  public static final int width = 400;
  public static final int heigth = 600;
  public static ArrayList<Integer> oldIds = new ArrayList<Integer>();
  protected Context definitionHelper;

  public VisualizationViewerDemo(Context definitionHelper) {
    this.definitionHelper = definitionHelper;
  }

  public VisualizationViewerDemo(Graph graph, Context definitionHelper) {
    this.definitionHelper = definitionHelper;
    init(graph);
  }

  public void init(Graph<KRunState, Transition> graph) {
    initLayout(graph);
    initVisualizationViewer();
    setVertexProperties();
    setEdgeProperties();
    setBackgroundColor();
    addMouseActivity();
    setPredicates();
  }

  public void initLayout(Graph<KRunState, Transition> graph) {
    layout = new DynamicLayout<KRunState, Transition>(graph, distanceSameLevelNodes,
            distanceParentChild);
  }

  public void initVisualizationViewer() {
    Dimension preferredSize = new Dimension(width, heigth);
    final VisualizationModel<KRunState, Transition> visualizationModel = new DefaultVisualizationModel<KRunState, Transition>(
            layout, preferredSize);
    vv = new VisualizationViewer<KRunState, Transition>(visualizationModel, preferredSize);
  }

  public void setVertexProperties() {
    VertexLabelAsShapeRenderer<KRunState, Transition> shapeRenderer =
            new VertexLabelAsShapeRenderer<KRunState, Transition>(vv.getRenderContext());

    Transformer stringer = new Transformer() {
      public String transform(Object e) {
        try {
          Integer id = ((KRunState) e).getStateId();
          if (!oldIds.contains(id)) {
            oldIds.add(id);
            if (getLayout().getGraph().getSuccessorCount((KRunState) e) == 0)
              vv.getPickedVertexState().pick((KRunState) e, true);
          }
          return "<html><center>Config<p> " + id;
        } catch (ClassCastException exc) {
          String result = "Configs[";
          result += clusteredGraphComponents("", e);
          result += "]";
          return result;
        }
      }
    };
    vv.getRenderContext().setVertexLabelTransformer(stringer);
    vv.getRenderContext().setVertexShapeTransformer(shapeRenderer);
    vv.getRenderContext().setVertexLabelRenderer(new DefaultVertexLabelRenderer(Color.red));
    vv.getRenderer().setVertexRenderer(
            new GradientVertexRenderer<KRunState, Transition>(Color.gray, Color.white, true));
    vv.getRenderer().setVertexLabelRenderer(shapeRenderer);
    vv.setVertexToolTipTransformer(new ToStringLabeller<KRunState>());
    vv.getRenderContext().setVertexShapeTransformer(new ClusterVertexShapeFunction<KRunState>());
  }

  public String clusteredGraphComponents(String result, Object e) {
    for (Object vertex : ((DirectedSparseGraph<?, ?>) e).getVertices()) {
      try {
        result += ((KRunState) vertex).getStateId() + ", ";
      } catch (Exception exc) {
        result += clusteredGraphComponents("", vertex);
      }
    }
    return result;
  }

  public void setEdgeProperties() {
    Transformer<Transition, Paint> edgePaint = new Transformer<Transition, Paint>() {
      private final Color[] palette = { Color.BLACK, Color.RED };

      public Paint transform(Transition i) {
        Set<Transition> selected = getSelectedEdges();
        if (selected.contains(i)) {
          return palette[1];
        }
        return palette[0];
      }
    };
    vv.getRenderContext().setEdgeDrawPaintTransformer(edgePaint);
    vv.getRenderContext()
            .setEdgeStrokeTransformer(new ConstantTransformer(new BasicStroke(1.75f)));
    vv.getRenderContext().setEdgeShapeTransformer(
            new EdgeShape.CubicCurve<KRunState, Transition>());
    Transformer<Transition, String> stringer = new Transformer<Transition, String>() {
      public String transform(Transition e) {
        return e.getLabel();
      }
    };
    vv.getRenderContext().setEdgeLabelTransformer(stringer);
    vv.getRenderContext().setLabelOffset(10);

  }

  public void setBackgroundColor() {
    vv.setBackground(Color.white);
  }

  public void addMouseActivity() {
    final DefaultModalGraphMouse<Object, Object> graphMouse = new DefaultModalGraphMouse<Object, Object>();
    vv.setGraphMouse(graphMouse);
    vv.addKeyListener(graphMouse.getModeKeyListener());
    vv.addMouseListener(new MouseAdapter() {
      public void mouseClicked(MouseEvent me) {
        if (getSelectedEdges().size() == 1) {
          for (Object edge : getSelectedEdges()) {
            try {
              KRunState dest = (KRunState) layout.getGraph().getDest((Transition) edge);
              KRunState src = (KRunState) layout.getGraph().getSource((Transition) edge);
              GraphRepresentation.displayEdgeInfo((Transition) edge, src, dest, definitionHelper);
              resetEdgeSelection();
            } catch (Exception e) {
            }
          }
        }
      }
    });
    graphMouse.setMode(ModalGraphMouse.Mode.PICKING);
  }

  public void resetEdgeSelection() {
    this.vv.getPickedEdgeState().clear();
  }

  public void setPredicates() {

    // use for subgraph action?!
    final PredicatedParallelEdgeIndexFunction eif = PredicatedParallelEdgeIndexFunction
            .getInstance();
    final Set<Transition> exclusions = new HashSet<Transition>();
    eif.setPredicate(new Predicate<Transition>() {
      public boolean evaluate(Transition e) {
        return exclusions.contains(e);
      }
    });

    this.vv.getRenderContext().setParallelEdgeIndexFunction(eif);
  }

  public DynamicLayout getLayout() {
    return layout;
  }

  public void setLayout(DynamicLayout layout) {
    this.layout = layout;
  }

  public VisualizationViewer getVv() {
    return vv;
  }

  public void setVv(VisualizationViewer vv) {
    this.vv = vv;
  }

  public Set getSelectedVertices() {
    return this.vv.getPickedVertexState().getPicked();
  }

  public Set getSelectedEdges() {
    return this.vv.getPickedEdgeState().getPicked();
  }

  public void resetGraphLayout() {
    this.layout.setGraph(this.layout.getGraph());
    this.layout.resetGraphPosition(this.layout.getGraph());
  }

  public void addEdge(KRunState source, KRunState target, int depth, String rule) {
	  this.layout.getGraph().addEdge(
            Transition.reduce(definitionHelper), source, target);
  }

  public Object verifyExistingVertex(Object vertex) {
    for (Object v : this.layout.getGraph().getVertices()) {
      try {
        if (((KRunState) v).equals(vertex))
        {
          return v;
        }
      } catch (ClassCastException cce) {
        // the node is colapse d
        for (Object expV : ((DirectedSparseGraph<?, ?>) v).getVertices()) {
          if (((KRunState) expV).equals(vertex))
          {
            return v;
          }
        }
      }
    }
    return null;
  }

  public boolean verifyCanAddEdge(Object source, Object dest) {
    for (Object vertex : layout.getGraph().getVertices()) {
      if (vertex instanceof DirectedSparseGraph<?, ?>) {
        DirectedSparseGraph v = (DirectedSparseGraph) vertex;
        if (v.containsVertex(source) && v.containsVertex(dest)) {
          return false;
        }
      }
    }
    return true;
  }

}