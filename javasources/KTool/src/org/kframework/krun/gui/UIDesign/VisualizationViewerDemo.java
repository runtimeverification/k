package org.kframework.krun.gui.UIDesign;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Paint;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.HashSet;
import java.util.Set;

import org.apache.commons.collections15.Predicate;
import org.apache.commons.collections15.Transformer;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.Transition;

import edu.uci.ics.jung.graph.DirectedSparseMultigraph;
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

public class VisualizationViewerDemo {
  
	private DynamicLayout<KRunState, Transition> layout;
	public static final int distanceParentChild = 100;
	public static final int distanceSameLevelNodes = 100;
	private VisualizationViewer<KRunState, Transition> vv;
	public static final int width = 400;
	public static final int heigth = 600;
		 
	public VisualizationViewerDemo(){}
	 
	public VisualizationViewerDemo(Graph<KRunState,Transition> graph){		
		init(graph);		
	}
	
	public void init(Graph<KRunState,Transition> graph){		
		initLayout(graph);
		initVisualizationViewer();
		setVertexProperties();
		setEdgeProperties();
		setBackgroundColor();
		addMouseActivity();
		setPredicates();
	}
	
	public void initLayout(Graph<KRunState, Transition>graph){
		layout = new DynamicLayout<KRunState, Transition>(graph, distanceSameLevelNodes, distanceParentChild);	
	}
	
	public void initVisualizationViewer(){
		 Dimension preferredSize = new Dimension(width, heigth);
	     final VisualizationModel<KRunState, Transition> visualizationModel = new DefaultVisualizationModel<KRunState, Transition>(layout, preferredSize);
	     vv =  new VisualizationViewer<KRunState, Transition>(visualizationModel, preferredSize);
	     
	}
	
	public void setVertexProperties(){
		 VertexLabelAsShapeRenderer<KRunState, Transition> shapeRenderer = 
				 new VertexLabelAsShapeRenderer<KRunState, Transition>(vv.getRenderContext());	       
	   
		 Transformer<KRunState,String> stringer = new Transformer<KRunState,String>(){
		    	public String transform(KRunState e) {
		    		try{
		    			String id = ((KRunState)e).getStateId()+"";
		    			return "<html><center>Vertex<p> " + id;
		    		}catch(Exception exc){
		    			String result = "Vertices[";
		    			result += clusteredGraphComponents("",e);
		    			result +="]";
			    		return result;
		    		}
		        }
		    };
		 vv.getRenderContext().setVertexLabelTransformer(stringer);
		    
	       vv.getRenderContext().setVertexShapeTransformer(shapeRenderer);
	       vv.getRenderContext().setVertexLabelRenderer(new DefaultVertexLabelRenderer(Color.red));	       
	       vv.getRenderer().setVertexRenderer(new GradientVertexRenderer<KRunState, Transition>(Color.gray, Color.white, true));
	       vv.getRenderer().setVertexLabelRenderer(shapeRenderer);
	       vv.setVertexToolTipTransformer(new ToStringLabeller<KRunState>());
		   vv.getRenderContext().setVertexShapeTransformer(new ClusterVertexShapeFunction<KRunState>());
	}
	
	public String clusteredGraphComponents(String result, Object e){
		for(Object vertex:((DirectedSparseMultigraph<?, ?>)e).getVertices()){
			try{
				result +=((KRunState)vertex).getStateId()+", ";
			}catch(Exception exc){
				result += clusteredGraphComponents("", vertex);
			}
		}
		return result;
	}
	
	public void setEdgeProperties(){
		Transformer<Transition, Paint> edgePaint = new Transformer<Transition, Paint>() {
	   	    private final Color[] palette = {Color.GREEN, Color.RED}; 
	   	    public Paint transform(Transition i) { 
	   	    	Set<Transition> selected = getSelectedEdges();	   	    	
	   	    	if(selected.contains(i)){
	   	    		return palette[1];
	   	    	}
	   	        return palette[0];
	   	    }
	   	};	   	
	   	vv.getRenderContext().setEdgeDrawPaintTransformer(edgePaint);
	   	vv.getRenderContext().setEdgeShapeTransformer(new EdgeShape.CubicCurve<KRunState, Transition>());
	    Transformer<Transition,String> stringer = new Transformer<Transition,String>(){
	    	public String transform(Transition e) {
	    		return e.getLabel();
	        }
	    };
	    vv.getRenderContext().setEdgeLabelTransformer(stringer);
	    vv.getRenderContext().setLabelOffset(10);
//	    ConstantDirectionalEdgeValueTransformer<Transition,Number> mv = new ConstantDirectionalEdgeValueTransformer<Transition,Number>(.5,.7);
//	    mv.setDirectedValue(new Double(((int)(.5*10))/10f));
//	    vv.getRenderContext().setEdgeLabelClosenessTransformer(mv);
	}
	
	public void setBackgroundColor(){
		 vv.setBackground(Color.white);
	}
	
	public void addMouseActivity(){
		
		final DefaultModalGraphMouse<Object, Object> graphMouse = new DefaultModalGraphMouse<Object, Object>();
		vv.setGraphMouse(graphMouse);
	    vv.addKeyListener(graphMouse.getModeKeyListener());
	    vv.addMouseListener(new MouseAdapter() {
	        public void mouseClicked(MouseEvent me) {
	            if(getSelectedVertices().size()==1){
	            	for(Object vertex:getSelectedVertices()){
	            		try{
	            			GraphRepresentation.displayVertexInfo((KRunState)vertex);
	            		}catch(Exception e){}
	            	}
	            }
				if(getSelectedEdges().size() == 1){
	            	for(Object edge:getSelectedEdges()){
	            		try{
	            			KRunState dest = layout.getGraph().getDest((Transition)edge);
	            			KRunState src = layout.getGraph().getSource((Transition)edge);
	            			GraphRepresentation.displayEdgeInfo((Transition)edge,src,dest);
	            			resetEdgeSelection();
	            		}catch(Exception e){}
	            	}
	            }
	          }
	        });
	    graphMouse.setMode(ModalGraphMouse.Mode.PICKING);
	}	 
	
	public void resetEdgeSelection(){
		this.vv.getPickedEdgeState().clear();
	}
	
	public void setPredicates(){
		
		//use for subgraph action?!
		final PredicatedParallelEdgeIndexFunction<KRunState, Transition> eif = PredicatedParallelEdgeIndexFunction.getInstance();
		final Set<Transition> exclusions = new HashSet<Transition>();
		eif.setPredicate(new Predicate<Transition>() {    	
			public boolean evaluate(Transition e) {
				return exclusions.contains(e);
			}});

		this.vv.getRenderContext().setParallelEdgeIndexFunction(eif);
	}

	public DynamicLayout<KRunState, Transition> getLayout() {
		return layout;
	}
	
	public void setLayout(DynamicLayout<KRunState, Transition> layout) {
		this.layout = layout;
	}

	public VisualizationViewer<KRunState, Transition> getVv() {
		return vv;
	}

	public void setVv(VisualizationViewer<KRunState, Transition> vv) {
		this.vv = vv;
	}
	
	public Set<KRunState> getSelectedVertices(){
		return this.vv.getPickedVertexState().getPicked();
	}
	
	public Set<Transition> getSelectedEdges(){
		return this.vv.getPickedEdgeState().getPicked();
	}
	
	public void resetGraphLayout(){
		this.layout.setGraph(this.layout.getGraph());
		this.layout.resetGraphPosition(this.layout.getGraph());
	}
	
	public void addEdge(KRunState source, KRunState target, int depth, String rule){
		this.layout.getGraph().addEdge(new Transition(Transition.TransitionType.REDUCE), source, target);
	}
	
	public Object verifyExistingVertex(KRunState vertex){
		for(Object v:this.layout.getGraph().getVertices()){
			if(((KRunState)v).equals(vertex))
			{
				return v;
			}
		}		
		return null;
	}
}