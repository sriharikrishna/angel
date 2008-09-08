// $Id: xaif_interface.cpp,v 1.15 2008/02/28 14:57:33 gottschling Exp $
#ifdef USEXAIFBOOSTER

#include <set>

#include "angel/include/xaif_interface.hpp"
#include "angel/include/eliminations.hpp"
#include "angel/include/heuristics.hpp"
#include "angel/include/reroutings.hpp"
#include "angel/include/angel_tools.hpp"

#include "angel/include/angel_io.hpp"
#include "angel/include/sa.hpp"

namespace angel {

using namespace std;
using namespace boost;
using namespace xaifBoosterCrossCountryInterface;

inline size_t which_index (const LinearizedComputationalGraphVertex * const add,
			   const vector<const LinearizedComputationalGraphVertex*>& av) {
  for (size_t c= 0; c < av.size(); c++) if (add == av[c]) return c;
  return av.size(); }

struct edge_address_t {
  ad_edge_t                                   e;
  const LinearizedComputationalGraphEdge*     address; 
  edge_address_t (int _i, int _j, const LinearizedComputationalGraphEdge* _address) :
    e (_i, _j), address (_address) {}
};

void read_graph_xaif_booster (const LinearizedComputationalGraph& xg, c_graph_t& cg,
			      vector<const LinearizedComputationalGraphVertex*>& av,
			      vector<edge_address_t>& ae) {
  typedef LinearizedComputationalGraph       xgraph_t;
  typedef LinearizedComputationalGraphVertex xvertex_t;
  typedef LinearizedComputationalGraphEdge   xedge_t;
  typedef c_graph_t::vertex_t                vertex_t;

  int nv= xg.numVertices ();
  c_graph_t gtmp (0, nv, 0); // all vertices as intermediate for now

  xgraph_t::ConstVertexIteratorPair vip (xg.vertices());

  // independents are first
  const xgraph_t::VertexPointerList&  indeps_list= xg.getIndependentList ();
  xgraph_t::VertexPointerList::const_iterator 
    bi= indeps_list.begin(), be= indeps_list.end();
  for (; bi != be; bi++) {
    av.push_back (*bi);
    // indeps.push_back (c);
  }

  // remaining are sorted topologically
  while ((int) av.size() < nv) {
    xgraph_t::ConstVertexIterator vi (vip.first), v_end (vip.second);
    for (; vi != v_end; ++vi) {
      if (which_index (&*vi, av) != av.size()) continue;
      xgraph_t::ConstInEdgeIteratorPair inedges (xg.getInEdgesOf (*vi));
      xgraph_t::ConstInEdgeIterator ie= inedges.first, iend= inedges.second;
      bool all_num= true; // all predecessors numbered
      for (; ie != iend; ++ie)
        if (which_index (&(xg.getSourceOf (*ie)), av) == av.size()) {
	  all_num= false; break; }
      if (all_num) av.push_back (&*vi);
    } }

  // re-activated
  vector<vertex_t> indeps;
  for (bi= indeps_list.begin(); bi != be; bi++) indeps.push_back (which_index (*bi, av));

  // test whether indeps in the beginning
  for (size_t c= 0; c < indeps.size(); c++)
    // assert (indeps[c] < indeps.size());
    throw_exception (indeps[c] >= indeps.size(), consistency_exception,
		     "Independent not at the beginning");
    
  vector<vertex_t> deps;
  const xgraph_t::VertexPointerList&  deps_list= xg.getDependentList ();
  bi= deps_list.begin(), be= deps_list.end();
  for (; bi != be; bi++) deps.push_back (which_index (*bi, av)); 

  int edge_number= 0;
  boost::property_map<c_graph_t, EdgeType>::type eType = get(EdgeType(), cg);
  xgraph_t::ConstEdgeIteratorPair eip (xg.edges());
  for (xgraph_t::ConstEdgeIterator ei (eip.first), e_end (eip.second); ei != e_end; ++ei) {
    vertex_t source= which_index (& (xg.getSourceOf (*ei)), av),
             target= which_index (& (xg.getTargetOf (*ei)), av);
    pair<c_graph_t::edge_t, bool> new_edge = add_edge (source, target, edge_number++, cg);
    ae.push_back (edge_address_t(source, target, &*ei));
    if ((*ei).getEdgeLabelType() == LinearizedComputationalGraphEdge::UNIT_LABEL)
      eType[new_edge.first] = UNIT_EDGE;
    else if ((*ei).getEdgeLabelType() == LinearizedComputationalGraphEdge::CONSTANT_LABEL)
      eType[new_edge.first] = CONSTANT_EDGE;
    else
      eType[new_edge.first] = VARIABLE_EDGE;
  } // end for all LCG edges

  cg.X= int (indeps.size()); cg.dependents= deps;

#ifndef NDEBUG
  write_graph ("read_graph_xaif_booster: resulting graph", cg);
#endif

}

inline const LinearizedComputationalGraphEdge* 
xaif_edge_pr (line_graph_t::edge_t e, const accu_graph_t& ag, const vector<edge_address_t>& ae) {
  line_graph_t::const_evn_t evn= get (vertex_name, ag.lg);
  ad_edge_t edge_name= evn[e];
  
  int first_try= e - ag.lg.x();
  if (edge_name == ae[first_try].e) return ae[first_try].address;
  for (size_t c= 0; c < ae.size(); c++)
    if (edge_name == ae[c].e) return ae[c].address;
  return 0;
}

void write_graph_xaif_booster (const accu_graph_t& ag,
			       const vector<const LinearizedComputationalGraphVertex*>& av,
			       const vector<edge_address_t>& ae,
			       JacobianAccumulationExpressionList& JAElist,
			       LinearizedComputationalGraph& remainderLCG,
			       VertexCorrelationList& v_cor_list,
			       EdgeCorrelationList& e_cor_list) {
  remainderLCG.clear();
  set<unsigned int> independent_indices, dependent_indices;
  // line_graph_t::const_evn_t evn= get (vertex_name, ag.lg);

  // make a preliminary pass to make remainder graph vertices
  for (size_t c = 0; c < ag.accu_exp.size(); c++) {
    ad_edge_t my_jacobi = ag.jacobi_entries[c];
    if (my_jacobi.second != 0) {
      // store indices of indep and dep vertices
      independent_indices.insert(my_jacobi.first);
      dependent_indices.insert(my_jacobi.second);
    }
  } // end preliminary pass
      
  // create and correlate remainder graph vertices from indep and dep sets
  for (set<unsigned int>::const_iterator sit = independent_indices.begin(); sit != independent_indices.end(); sit++) {
    LinearizedComputationalGraphVertex& new_remainder_vertex = remainderLCG.addVertex();
    VertexCorrelationEntry new_vertex_correlation;
    new_vertex_correlation.myOriginalVertex_p = av[*sit];
    new_vertex_correlation.myRemainderVertex_p = &new_remainder_vertex;
    v_cor_list.push_back(new_vertex_correlation);
  }
  for (set<unsigned int>::const_iterator sit = dependent_indices.begin(); sit != dependent_indices.end(); sit++) {
    LinearizedComputationalGraphVertex& new_remainder_vertex = remainderLCG.addVertex();
    VertexCorrelationEntry new_vertex_correlation;
    new_vertex_correlation.myOriginalVertex_p = av[*sit];
    new_vertex_correlation.myRemainderVertex_p = &new_remainder_vertex;
    v_cor_list.push_back(new_vertex_correlation);
  }

  // iterate over all angel JAEs
  vector<JacobianAccumulationExpressionVertex*> exp_output_pr; // pointer to output vertex of expression
  for (size_t c= 0; c < ag.accu_exp.size(); c++) {
    const accu_exp_graph_t& my_exp= ag.accu_exp[c];
    property_map<pure_accu_exp_graph_t, vertex_name_t>::const_type vpr= get (vertex_name, my_exp);

    JacobianAccumulationExpression& new_exp = JAElist.addExpression();
    //exp_pr.push_back(&new_exp);
    vector<JacobianAccumulationExpressionVertex*> vp (my_exp.v());
    for (size_t vc= 0; vc < (size_t) my_exp.v(); vc++) {      
      const accu_exp_t& prop= vpr[vc];
      JacobianAccumulationExpressionVertex& new_vertex = new_exp.addVertex();
      vp[vc]= &new_vertex;

      // the last vertex in the expression is the output vertex
      if (vc+1 == (size_t) my_exp.v()) exp_output_pr.push_back(&new_vertex);

      switch (prop.ref_kind) { 
      case accu_exp_t::nothing: throw_exception (true, consistency_exception, "Unset vertex"); break;
      case accu_exp_t::exp:
	throw_debug_exception (prop.ref.exp_nr >= int (c), consistency_exception, "Expression number too large")
	new_vertex.setInternalReference (*exp_output_pr[prop.ref.exp_nr]); break;
      case accu_exp_t::lgn: {
	const LinearizedComputationalGraphEdge* ptr= xaif_edge_pr (prop.ref.node, ag, ae); 
	throw_debug_exception (ptr == NULL, consistency_exception, "Unset reference");
	new_vertex.setExternalReference (*ptr); } break;
      case accu_exp_t::isop:    
	new_vertex.setOperation (prop.ref.op == accu_exp_t::add ? JacobianAccumulationExpressionVertex::ADD_OP
								: JacobianAccumulationExpressionVertex::MULT_OP);
      } // end switch on prop.ref_kind
    } // end all expression vertices

    // deal with JAE edges    
    graph_traits<pure_accu_exp_graph_t>::edge_iterator ei, e_end;
    for (tie (ei, e_end)= edges (my_exp); ei != e_end; ei++)
      new_exp.addEdge (*vp[source (*ei, my_exp)], *vp[target (*ei, my_exp)]);

    // deal with JAEs that are Jacobian entries
    ad_edge_t my_jacobi = ag.jacobi_entries[c];
    if (my_jacobi.second != 0) {
      //new_exp.setJacobianEntry (*av[my_jacobi.second], *av[my_jacobi.first]);

      // create edge in the remainder graph
      const LinearizedComputationalGraphVertex* original_src_p = av[my_jacobi.first];
      const LinearizedComputationalGraphVertex* original_tgt_p = av[my_jacobi.second];
      LinearizedComputationalGraphVertex* remainder_src_p = NULL;
      LinearizedComputationalGraphVertex* remainder_tgt_p = NULL;
      for (VertexCorrelationList::iterator vcori = v_cor_list.begin(); vcori != v_cor_list.end(); vcori++) {
	if (vcori->myOriginalVertex_p == original_src_p)	remainder_src_p = vcori->myRemainderVertex_p;
	else if (vcori->myOriginalVertex_p == original_tgt_p)	remainder_tgt_p = vcori->myRemainderVertex_p;
      } // end all vertex correlation entries
      throw_exception (remainder_src_p == NULL || remainder_tgt_p == NULL, consistency_exception, "Vertex in remainder graph could not be found");
      LinearizedComputationalGraphEdge& new_remainder_edge = remainderLCG.addEdge(*remainder_src_p, *remainder_tgt_p);

      // crate the correlation entry
      EdgeCorrelationEntry new_edge_correlation;
      new_edge_correlation.myRemainderGraphEdge_p = &new_remainder_edge;
      new_edge_correlation.myType = EdgeCorrelationEntry::JAE_VERT;
      new_edge_correlation.myEliminationReference.myJAEVertex_p = exp_output_pr.back();
      //new_edge_correlation.myEliminationReference.myJAEVertex_p = getJAE_p (*ei, angelLCG, edge_ref_list);
      e_cor_list.push_back(new_edge_correlation);
    } // end if Jacobian entry

  } // end all Jacobian accumulation expressions
} // end write_graph_xaif_booster()

unsigned int num_nontrivial_edges (const c_graph_t& angelLCG,
				   const Elimination::AwarenessLevel_E ourAwarenessLevel) {
  boost::property_map<c_graph_t, EdgeType>::const_type eType = get (EdgeType(), angelLCG);
  unsigned int numNontrivialEdges = 0;
  c_graph_t::ei_t ei, e_end;
  for (tie (ei, e_end)= edges (angelLCG); ei != e_end; ++ei)
    if (ourAwarenessLevel == Elimination::NO_AWARENESS
    || (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[*ei] != UNIT_EDGE)
    || (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[*ei] == VARIABLE_EDGE))
      numNontrivialEdges++;

  return numNontrivialEdges;
} // end of num_nontrivial_edges()

unsigned int numIntermediateVertices (const c_graph_t& angelLCG) {
  unsigned int numIntermediates = 0;
  c_graph_t::vi_t vi, v_end;
  for (tie (vi, v_end) = vertices (angelLCG); vi != v_end; ++vi)
    if (vertex_type (*vi, angelLCG) == intermediate) numIntermediates++;
  return numIntermediates;
} // end numIntermediateVertices()

unsigned int numIntermediateVerticesWithoutUnitEdge (const c_graph_t& angelLCG) {
  boost::property_map<c_graph_t, EdgeType>::const_type eType = get(EdgeType(), angelLCG);
  unsigned int numIntermediatesWithoutUnitEdge = 0;
  c_graph_t::vi_t vi, v_end;
  c_graph_t::iei_t iei, ie_end;
  c_graph_t::oei_t oei, oe_end;

  for (tie (vi, v_end) = vertices (angelLCG); vi != v_end; ++vi) {
    if (vertex_type (*vi, angelLCG) == intermediate) {
      for (tie(iei, ie_end) = in_edges (*vi, angelLCG); iei != ie_end; ++iei)
	if (eType[*iei] == UNIT_EDGE) break;
      for (tie(oei, oe_end) = out_edges (*vi, angelLCG); oei != oe_end; ++oei)
	if (eType[*oei] == UNIT_EDGE) break;
      if ( iei == ie_end && oei == oe_end) numIntermediatesWithoutUnitEdge++;
    }
  }
  return numIntermediatesWithoutUnitEdge;
} // end numIntermediateVertices()

void ourLCG_to_angelLCG (const LinearizedComputationalGraph& ourLCG,
			 vector<const LinearizedComputationalGraphVertex*>& ourLCG_verts,
			 c_graph_t& angelLCG,
			 list<EdgeRef_t>& edge_ref_list) {
  angelLCG.clear();

  // COPY VERTICES
  const LinearizedComputationalGraph::VertexPointerList& ourLCG_indeps = ourLCG.getIndependentList ();
  const LinearizedComputationalGraph::VertexPointerList& ourLCG_deps = ourLCG.getDependentList ();
  LinearizedComputationalGraph::VertexPointerList::const_iterator LCGvi;

  // Add pointers to independent vertices to vector ourLCG_verts
  for (LCGvi = ourLCG_indeps.begin(); LCGvi != ourLCG_indeps.end(); LCGvi++)
    ourLCG_verts.push_back (*LCGvi);

  // remaining are sorted topologically
  int nv = ourLCG.numVertices ();
  LinearizedComputationalGraph::ConstVertexIteratorPair vip (ourLCG.vertices());
  while ((int) ourLCG_verts.size() < nv) {
    for (LinearizedComputationalGraph::ConstVertexIterator topi (vip.first), top_end (vip.second); topi != top_end; ++topi) {
      if (which_index (&*topi, ourLCG_verts) != ourLCG_verts.size()) continue;
      bool all_num = true; // all predecessors numbered
      LinearizedComputationalGraph::ConstInEdgeIteratorPair inedges (ourLCG.getInEdgesOf (*topi));
      for (LinearizedComputationalGraph::ConstInEdgeIterator ie = inedges.first, iend = inedges.second; ie != iend; ++ie)
	if (which_index (&(ourLCG.getSourceOf (*ie)), ourLCG_verts) == ourLCG_verts.size()) {
	  all_num = false;
	  break;
	}
      if (all_num) ourLCG_verts.push_back (&*topi);
    } // end all vertices
  }

  // populate vectors of independent and dependent vertices
  vector<c_graph_t::vertex_t> indeps, deps;
  for (LCGvi = ourLCG_indeps.begin(); LCGvi != ourLCG_indeps.end(); LCGvi++)
    indeps.push_back (which_index (*LCGvi, ourLCG_verts));
  angelLCG.x(int (indeps.size()));
  for (LCGvi = ourLCG_deps.begin(); LCGvi != ourLCG_deps.end(); LCGvi++)
    deps.push_back (which_index (*LCGvi, ourLCG_verts)); 
  angelLCG.dependents = deps;

  // ensure that indeps occur in the beginning
  for (size_t c = 0; c < indeps.size(); c++)
    throw_exception (indeps[c] >= indeps.size(), consistency_exception, "Independent not at the beginning");

  // COPY EDGES ----------------------------------------------------------------
  int edge_number = 0;
  boost::property_map<c_graph_t, EdgeType>::type eType = get(EdgeType(), angelLCG);
  LinearizedComputationalGraph::ConstEdgeIteratorPair eip (ourLCG.edges());
  for (LinearizedComputationalGraph::ConstEdgeIterator ei (eip.first), e_end (eip.second); ei != e_end; ++ei) {
    // locate source and target of edge in angelLCG
    c_graph_t::vertex_t angelSource = which_index (& (ourLCG.getSourceOf (*ei)), ourLCG_verts);
    c_graph_t::vertex_t	angelTarget = which_index (& (ourLCG.getTargetOf (*ei)), ourLCG_verts);
    pair<c_graph_t::edge_t, bool> new_edge = add_edge (angelSource, angelTarget, edge_number++, angelLCG);
    if ((*ei).getEdgeLabelType() == LinearizedComputationalGraphEdge::UNIT_LABEL)
      eType[new_edge.first] = UNIT_EDGE;
    else if ((*ei).getEdgeLabelType() == LinearizedComputationalGraphEdge::CONSTANT_LABEL)
      eType[new_edge.first] = CONSTANT_EDGE;
    else
      eType[new_edge.first] = VARIABLE_EDGE;

    EdgeRef_t new_edge_ref (new_edge.first, &*ei);
    edge_ref_list.push_back(new_edge_ref);
  } // end for all LCG edges

#ifndef NDEBUG
  write_graph ("angelLCG (constructed from ourLCG): ", angelLCG);
#endif

} // end ourLCG_to_angelLCG()

void populate_remainderGraph_and_correlationLists (const c_graph_t& angelLCG,
						   const vector<const LinearizedComputationalGraphVertex*> ourLCG_verts,
						   const list<EdgeRef_t>& edge_ref_list,
						   LinearizedComputationalGraph& remainderLCG,
						   VertexCorrelationList& v_cor_list,
						   EdgeCorrelationList& e_cor_list) {
  remainderLCG.clear();

  // copy and correlate vertices
  v_cor_list.resize(0);
  c_graph_t::vi_t vi, v_end;
  for (tie (vi, v_end) = vertices (angelLCG); vi != v_end; ++vi) {
    // since vertices aren't removed from angelLCG, only copy non-isolated vertices
    if (in_degree (*vi, angelLCG) != 0 || out_degree (*vi, angelLCG) != 0) {
      LinearizedComputationalGraphVertex& new_rvert (remainderLCG.addVertex());
      // add a new correlation entry to the list
      VertexCorrelationEntry new_rvert_cor;
      new_rvert_cor.myOriginalVertex_p = ourLCG_verts[*vi];
      new_rvert_cor.myRemainderVertex_p = &new_rvert;
      v_cor_list.push_back(new_rvert_cor);
    }
  } // end all vertices

  // copy and correlate edges
  boost::property_map<c_graph_t, EdgeType>::const_type eType = get(EdgeType(), angelLCG);
  e_cor_list.resize(0);
  c_graph_t::ei_t ei, e_end;
  for (tie(ei, e_end) = edges(angelLCG); ei != e_end; ++ei) {
    // Find source and target in remainder LCG
    const LinearizedComputationalGraphVertex* original_src_p = ourLCG_verts[source(*ei, angelLCG)];
    const LinearizedComputationalGraphVertex* original_tgt_p = ourLCG_verts[target(*ei, angelLCG)];
    LinearizedComputationalGraphVertex* remainder_src_p = NULL;
    LinearizedComputationalGraphVertex* remainder_tgt_p = NULL;
    for (VertexCorrelationList::iterator vcori = v_cor_list.begin(); vcori != v_cor_list.end(); vcori++) {
      if (vcori->myOriginalVertex_p == original_src_p) remainder_src_p = vcori->myRemainderVertex_p;
      else if (vcori->myOriginalVertex_p == original_tgt_p) remainder_tgt_p = vcori->myRemainderVertex_p;
    } // end all vertex correlation entries
    throw_exception (remainder_src_p == NULL || remainder_tgt_p == NULL, consistency_exception,
					"Vertex in remainder graph could not be correlated");

    // create the edge and its correlation entry
    LinearizedComputationalGraphEdge& new_redge = remainderLCG.addEdge(*remainder_src_p, *remainder_tgt_p);
    EdgeCorrelationEntry new_edge_correlation;
    new_edge_correlation.myRemainderGraphEdge_p = &new_redge;

    // set the edge type (unit/const/variable)
    switch (eType[*ei]) { 
    case UNIT_EDGE:
      new_redge.setEdgeLabelType(LinearizedComputationalGraphEdge::UNIT_LABEL);
      break;
    case CONSTANT_EDGE:
      new_redge.setEdgeLabelType(LinearizedComputationalGraphEdge::CONSTANT_LABEL);
      break;
    case VARIABLE_EDGE:
      new_redge.setEdgeLabelType(LinearizedComputationalGraphEdge::VARIABLE_LABEL);
      break;
    }

    // derive contents of correlation entry from the internal edge reference list
    EdgeRefType_E new_remainder_edge_ref_t = getRefType (*ei, angelLCG, edge_ref_list);
    if (new_remainder_edge_ref_t == LCG_EDGE) {
      new_edge_correlation.myEliminationReference.myOriginalEdge_p = getLCG_p (*ei, angelLCG, edge_ref_list);
      new_edge_correlation.myType = EdgeCorrelationEntry::LCG_EDGE;
    }
    else if (new_remainder_edge_ref_t == JAE_VERT) {
      new_edge_correlation.myEliminationReference.myJAEVertex_p = getJAE_p (*ei, angelLCG, edge_ref_list);
      new_edge_correlation.myType = EdgeCorrelationEntry::JAE_VERT;
    }
    else throw_exception (true, consistency_exception, "Edge reference type neither LCG_EDGE nor JAE_VERT");

    e_cor_list.push_back(new_edge_correlation);
  } // end all edges in angelLCG

} // end populate_remainderGraph_and_correlationLists()

unsigned int replay_elim_seq (c_graph_t& angelLCG,
			      const vector<EdgeElim> edgeElimSeqV,
			      unsigned int& previous_numNontrivialEdges,
			      const Elimination::AwarenessLevel_E ourAwarenessLevel,
			      elimSeq_cost_t& dummy_elimSeq_cost,
			      refillDependenceMap_t& dummy_refillDependenceMap) {
  unsigned int computationalCost = 0;
  for (size_t i = 0; i < edgeElimSeqV.size(); i++) {
    if (i == edgeElimSeqV.size() - 1) // save previous_numNontrivialEdges
      previous_numNontrivialEdges = num_nontrivial_edges(angelLCG, ourAwarenessLevel);
    #ifndef NDEBUG
    cout << "\t";
    #endif
    computationalCost += edgeElimSeqV[i].isFront() ?
       front_elim(edgeElimSeqV[i].getE(angelLCG), angelLCG, ourAwarenessLevel, dummy_elimSeq_cost, dummy_refillDependenceMap)
     : back_elim(edgeElimSeqV[i].getE(angelLCG), angelLCG, ourAwarenessLevel, dummy_elimSeq_cost, dummy_refillDependenceMap);
  } // end iterate over edge elims
  return computationalCost;
} // end replay_elim_seq()

unsigned int replay_transformation_seq(c_graph_t& angelLCG,
				       const vector<Transformation> transformationSeqV,
				       unsigned int& previous_numNontrivialEdges,
				       const Elimination::AwarenessLevel_E ourAwarenessLevel,
				       transformationSeq_cost_t& dummy_transformationSeq_cost,
				       refillDependenceMap_t& dummy_refillDependenceMap) {
  unsigned int computationalCost = 0;
  for (size_t i = 0; i < transformationSeqV.size(); i++) {
    if (i == transformationSeqV.size() - 1) // save previous_numNontrivialEdges
      previous_numNontrivialEdges = num_nontrivial_edges(angelLCG, ourAwarenessLevel);
    #ifndef NDEBUG
    cout << "\t";
    #endif
    // REROUTING
    if (transformationSeqV[i].isRerouting)
      computationalCost += transformationSeqV[i].getRerouting().isPre() ?
	 prerouteEdge_noJAE(transformationSeqV[i].getRerouting().getER(angelLCG), angelLCG, ourAwarenessLevel)
       : postrouteEdge_noJAE(transformationSeqV[i].getRerouting().getER(angelLCG), angelLCG, ourAwarenessLevel);
    // EDGE ELIMINATION
    else {
      computationalCost += transformationSeqV[i].getEdgeElim().isFront() ?
	 frontEdgeElimination_noJAE(transformationSeqV[i].getEdgeElim().getE(angelLCG), angelLCG, ourAwarenessLevel, &dummy_transformationSeq_cost, dummy_refillDependenceMap)
       : backEdgeElimination_noJAE(transformationSeqV[i].getEdgeElim().getE(angelLCG), angelLCG, ourAwarenessLevel, &dummy_transformationSeq_cost, dummy_refillDependenceMap);
    } // end edge elimination
  } // end iterate over transformations
  return computationalCost;
} // end replay_transformation_seq()

} // end namespace angel



using namespace angel;

namespace xaifBoosterCrossCountryInterface {
void compute_partial_elimination_sequence_sa (const LinearizedComputationalGraph& ourLCG,
					      const Elimination::AwarenessLevel_E ourAwarenessLevel,
					      const bool allowMaintainingFlag,
					      JacobianAccumulationExpressionList& jae_list,
					      LinearizedComputationalGraph& remainderLCG,
					      VertexCorrelationList& v_cor_list,
					      EdgeCorrelationList& e_cor_list) {
#ifndef NDEBUG
  cout << "ourAwarenessLevel is set to " << Elimination::AwarenessLevelToString(ourAwarenessLevel) << endl;
#endif

  // Create internal (angel) LCG from xaifBooster LCG
  vector<const LinearizedComputationalGraphVertex*> ourLCG_verts;
  c_graph_t angelLCG;
  list<EdgeRef_t> edge_ref_list;
  ourLCG_to_angelLCG (ourLCG, ourLCG_verts, angelLCG, edge_ref_list);

  srand(time(NULL));

  c_graph_t angelLCG_copy (angelLCG);
  elimSeq_cost_t dummy_elimSeq_cost (0, 0, 0, 0, 0, 0);
  refillDependenceMap_t dummy_refillDependenceMap;
  vector<EdgeElim> allEdgeElimsV, edgeElimSeqV, best_edgeElimSeqV;

  unsigned int previous_numNontrivialEdges = num_nontrivial_edges(angelLCG_copy, ourAwarenessLevel);
  unsigned int bestNumNontrivialEdges = num_nontrivial_edges(angelLCG_copy, ourAwarenessLevel);
  unsigned int computationalCost_at_bestEdgeCount = 0;
  unsigned int computationalCost = 0;
  double T = 10;
  unsigned int max_steps = 20 * num_vertices(angelLCG);
  for (unsigned int steps_counter = 0; steps_counter < max_steps; steps_counter++) {
    // adjust temperature
    if(steps_counter%10==0)
      T = 10;
    else
      T = T/2.0;
#ifndef NDEBUG
    cout << "datapoint:" << computationalCost << ":" << num_nontrivial_edges(angelLCG_copy, ourAwarenessLevel) << endl;
    cout << "T=" << T << endl;
#endif
    eliminatable_edges(angelLCG_copy, allEdgeElimsV);
    if (allEdgeElimsV.empty()) break; // no more eliminatable edges

    // calculate relative probabilities for each possible edge elim
    vector<double> deltaE(allEdgeElimsV.size() + 1);
    for (size_t c = 0; c < allEdgeElimsV.size(); c++)
      deltaE[c] = edge_elim_effect (allEdgeElimsV[c], angelLCG_copy, ourAwarenessLevel);
    deltaE[allEdgeElimsV.size()] = (int)previous_numNontrivialEdges - (int)num_nontrivial_edges(angelLCG_copy, ourAwarenessLevel);

    unsigned int choice_index = chooseTarget_sa(deltaE, T);
    if (choice_index != allEdgeElimsV.size()) { // eliminate an edge
      previous_numNontrivialEdges = num_nontrivial_edges(angelLCG_copy, ourAwarenessLevel);
      edgeElimSeqV.push_back(allEdgeElimsV[choice_index]);
      computationalCost += allEdgeElimsV[choice_index].isFront() ?
	 front_elim(allEdgeElimsV[choice_index].getE(angelLCG_copy), angelLCG_copy, ourAwarenessLevel, dummy_elimSeq_cost, dummy_refillDependenceMap)
       : back_elim(allEdgeElimsV[choice_index].getE(angelLCG_copy), angelLCG_copy, ourAwarenessLevel, dummy_elimSeq_cost, dummy_refillDependenceMap);
      // check whether we've beaten our CURRENT best
      if (num_nontrivial_edges (angelLCG_copy, ourAwarenessLevel) < bestNumNontrivialEdges
       || (num_nontrivial_edges (angelLCG_copy, ourAwarenessLevel) == bestNumNontrivialEdges && computationalCost < computationalCost_at_bestEdgeCount)) {
	bestNumNontrivialEdges = num_nontrivial_edges (angelLCG_copy, ourAwarenessLevel);
	computationalCost_at_bestEdgeCount = computationalCost;
	best_edgeElimSeqV = edgeElimSeqV;
#ifndef NDEBUG
	cout << "** New best_num_edges found: " << bestNumNontrivialEdges << " with computational cost " << computationalCost << " after " << edgeElimSeqV.size() << " eliminations" << endl;
#endif
      }
    }
    else { // this corresponds to a backtracking (going back cannot lead to a new "best-so-far" result)
      #ifndef NDEBUG
      cout << "Performing a BACKTRACKING step" << endl;
      #endif
      if (edgeElimSeqV.empty())
	continue;
      angelLCG_copy = angelLCG;
      edgeElimSeqV.pop_back();
      computationalCost = replay_elim_seq(angelLCG_copy, edgeElimSeqV, previous_numNontrivialEdges, ourAwarenessLevel, dummy_elimSeq_cost, dummy_refillDependenceMap);
    }
  } // end of elimination sequence

#ifndef NDEBUG
  // Really, we output the number of intermediates with no incident unit edge (can be normalized)
  cout << "Achieved a nontrivial edge count of " << bestNumNontrivialEdges << endl;
  cout << "Best sequence of edge elims: ";
  for (size_t c = 0; c < best_edgeElimSeqV.size(); c++)
    cout << endl << best_edgeElimSeqV[c].debug().c_str();
  cout << endl << endl << "****** Now re-performing best_edgeElimSeqV until we reach our edge goal of " << bestNumNontrivialEdges << " nontrivial edges" << endl;
#endif

  unsigned int cost_of_elim_seq = 0;
  if (num_nontrivial_edges (angelLCG, ourAwarenessLevel) == bestNumNontrivialEdges) {
#ifndef NDEBUG
    cout << "No eliminations necessary to reach the desired edge count of " << bestNumNontrivialEdges << endl;
#endif
  }
  else { //replay the elimination sequence until we reach edge count goal
    for (size_t c = 0; c < best_edgeElimSeqV.size(); c++) {
      cost_of_elim_seq += best_edgeElimSeqV[c].isFront() ?
	 front_eliminate_edge_directly(best_edgeElimSeqV[c].getE(angelLCG), angelLCG, ourAwarenessLevel, edge_ref_list, jae_list)
       : back_eliminate_edge_directly(best_edgeElimSeqV[c].getE(angelLCG), angelLCG, ourAwarenessLevel, edge_ref_list, jae_list);
      if (num_nontrivial_edges (angelLCG, ourAwarenessLevel) == bestNumNontrivialEdges) {
	#ifndef NDEBUG
	cout << "Goal of " << bestNumNontrivialEdges << " reached" << endl;
	#endif
	break;
      }
    }
  }
#ifndef NDEBUG
  write_graph ("angelLCG after partial edge elimination sequence (G prime): ", angelLCG);
  writeVertexAndEdgeTypes (cout, angelLCG);
  cout << "compute_partial_elimination_sequence: cost " << cost_of_elim_seq << endl;
#endif
  populate_remainderGraph_and_correlationLists (angelLCG, ourLCG_verts, edge_ref_list, remainderLCG, v_cor_list, e_cor_list);
} // end compute_partial_elimination_sequence_sa()

void compute_partial_elimination_sequence (const LinearizedComputationalGraph& ourLCG,
					   const Elimination::AwarenessLevel_E ourAwarenessLevel,
					   const bool allowMaintainingFlag,
					   JacobianAccumulationExpressionList& jae_list,
					   LinearizedComputationalGraph& remainderLCG,
					   VertexCorrelationList& v_cor_list,
					   EdgeCorrelationList& e_cor_list) {
#ifndef NDEBUG
  cout << "allowMaintainingFlag is set to "; if (allowMaintainingFlag) cout << "true"; else cout << "false";
  cout << ", and ourAwarenessLevel is set to " << Elimination::AwarenessLevelToString(ourAwarenessLevel) << endl;
#endif

  // Create internal (angel) LCG from xaifBooster LCG
  vector<const LinearizedComputationalGraphVertex*> ourLCG_verts;
  c_graph_t angelLCG;
  list<EdgeRef_t> edge_ref_list;
  ourLCG_to_angelLCG (ourLCG, ourLCG_verts, angelLCG, edge_ref_list);

#ifndef NDEBUG
  cout << endl << "****** Performing total elim sequences and building up refill dependence information..." << endl;
#endif

  // To begin with, the best elimination sequence is NO elimination sequence
  elimSeq_cost_t *bestEliminationSequence = new elimSeq_cost_t (num_nontrivial_edges(angelLCG, ourAwarenessLevel), // bestNumNontrivialEdges
								0, // cost
								0, // costAtBestEdgecount
								numIntermediateVertices(angelLCG), // numIntermediatesAtBestEdgecount
								numIntermediateVerticesWithoutUnitEdge(angelLCG), // numIntermediatesWithoutUnitEdgeAtBestEdgecount
								0); // lastDesiredElim
  elimSeq_cost_t *currentEliminationSequence;

  // while I eliminate, build up list of refill dependences.  This is STATIC, because I store the vertex dependences
  refillDependenceMap_t refillDependences;
  vector<edge_bool_t> bev1, bev2, bev3, bev4, bev5;

  unsigned int seqNum = 0;
  while (true) {
    c_graph_t angelLCG_copy (angelLCG);
    currentEliminationSequence = new elimSeq_cost_t (num_nontrivial_edges (angelLCG_copy, ourAwarenessLevel), // bestNumNontrivialEdges
						     0, // cost
						     0, // costAtBestEdgecount
						     numIntermediateVertices(angelLCG_copy), // numIntermediatesAtBestEdgecount
						     numIntermediateVerticesWithoutUnitEdge(angelLCG), // numIntermediatesWithoutUnitEdgeAtBestEdgecount
						     0); // lastDesiredElim
#ifndef NDEBUG
    cout << "++++++++++++++++++++++++" << endl << "TRYING A NEW COMPLETE ELIMINATION SEQUENCE" << "++++++++++++++++++++++++" << endl;
#endif

    // perform a complete elimination sequence that preserves scarcity and tries to avoid refill
    unsigned int elimNum = 0;
    while(true) {
#ifndef NDEBUG
      cout << "datapoint:" << seqNum << ":" << elimNum << ":" << num_nontrivial_edges(angelLCG_copy, ourAwarenessLevel) << endl;
#endif

      // run through the heuristics pipeline
      eliminatable_objects (angelLCG_copy, bev1);

      if (reducing_edge_eliminations (bev1, angelLCG_copy, ourAwarenessLevel, bev2) == 0 && allowMaintainingFlag)
	maintaining_edge_eliminations (bev1, angelLCG_copy, ourAwarenessLevel, bev2);

      if (!bev2.empty())
	refill_avoiding_edge_eliminations (bev2, angelLCG_copy, refillDependences, bev3);
      else
	refill_avoiding_edge_eliminations (bev1, angelLCG_copy, refillDependences, bev3);

      if (!bev3.empty()) // there are some refill avoiding elims
	lowest_markowitz_edge (bev3, angelLCG_copy, bev4);
      else if (!bev2.empty()) // there are no refill avoiding elims, but there are scarcity-preserving elims
	lowest_markowitz_edge (bev2, angelLCG_copy, bev4);
      else // there are no refill avoiding elims, and no scarcity-preserving elims
	lowest_markowitz_edge (bev1, angelLCG_copy, bev4);

      reverse_mode_edge (bev4, angelLCG_copy, bev5);

      if (bev5.empty()) break; // no more eliminatable edges

      c_graph_t::edge_t e = bev5[0].first;
      bool isFront = bev5[0].second;
      edge_ij_elim_t thisElim (source (e, angelLCG), target (e, angelLCG), isFront);
      currentEliminationSequence->edgeElimVector.push_back(thisElim);

      currentEliminationSequence->cost += isFront ? front_elim (e, angelLCG_copy, ourAwarenessLevel, *currentEliminationSequence, refillDependences)
						  : back_elim (e, angelLCG_copy, ourAwarenessLevel, *currentEliminationSequence, refillDependences);

      // check whether we've beaten our CURRENT best
      if (num_nontrivial_edges (angelLCG_copy, ourAwarenessLevel) < currentEliminationSequence->bestNumNontrivialEdges) {
        currentEliminationSequence->bestNumNontrivialEdges = num_nontrivial_edges (angelLCG_copy, ourAwarenessLevel);
        currentEliminationSequence->costAtBestEdgecount = currentEliminationSequence->cost;
	currentEliminationSequence->numIntermediatesAtBestEdgecount = numIntermediateVertices(angelLCG_copy);
	currentEliminationSequence->numIntermediatesWithoutUnitEdgeAtBestEdgecount = numIntermediateVerticesWithoutUnitEdge(angelLCG_copy);
        currentEliminationSequence->lastDesiredElim = currentEliminationSequence->edgeElimVector.size();
#ifndef NDEBUG
        cout << "** new best_num_edges for currentElimSeq: " << currentEliminationSequence->bestNumNontrivialEdges << endl;
#endif
      }

#ifndef NDEBUG
      write_refillDependences (cout, refillDependences);
#endif

      elimNum++;
    } // end of elimination sequence
    bool finished = !currentEliminationSequence->revealedNewDependence;

#ifndef NDEBUG
    cout << "complete elim sequence complete.  This sequence achieved " << currentEliminationSequence->bestNumNontrivialEdges << " edges and ";
    if (currentEliminationSequence->revealedNewDependence) cout << "DID"; else cout << "DID NOT";
    cout << " add new dependence information to the dependence map" << endl;
#endif

    // check whether we've beaten our OVERALL best, or MATCHED it with lower cost
    if (currentEliminationSequence->bestNumNontrivialEdges < bestEliminationSequence->bestNumNontrivialEdges
     || (currentEliminationSequence->bestNumNontrivialEdges == bestEliminationSequence->bestNumNontrivialEdges
      && currentEliminationSequence->costAtBestEdgecount < bestEliminationSequence->costAtBestEdgecount)) {
      delete bestEliminationSequence;
      bestEliminationSequence = currentEliminationSequence;
      currentEliminationSequence = NULL;
#ifndef NDEBUG
      cout << "This elimination sequence is best so far" << endl;
#endif
    }
    else { // latest elimination sequence isn't an improvement
#ifndef NDEBUG
      cout << "This elimination sequence isn't an improvement" << endl;
#endif
      delete currentEliminationSequence;
    }

    if (finished) break;
    seqNum++;
  } // end determine best elimination sequence

#ifndef NDEBUG
  // Really, we output the number of intermediates with no incident unit edge (can be normalized)
  cout << "The best partial edge elimination sequence achieves a nontrivial edge count of " << bestEliminationSequence->bestNumNontrivialEdges
       << ", at which point there are " << bestEliminationSequence->numIntermediatesWithoutUnitEdgeAtBestEdgecount << " intermediate vertices" << endl;
       //<< ", at which point " << bestElimSeqFound.numIntermediatesWithoutUnitEdgeAtBestEdgecount << " of "
       //<< bestElimSeqFound.numIntermediatesAtBestEdgecount << " intermediate vertices have no incident unit edges" << endl;
#endif

#ifndef NDEBUG
  cout << "heuristic phase complete.  bestElimSeqFound achieves a nontrivial edge count of " << bestEliminationSequence->bestNumNontrivialEdges << endl;
  cout << "contents of bestElimSeqFound.edgeElimVector: " << endl;
  for (size_t c = 0; c < bestEliminationSequence->edgeElimVector.size(); c++)
    cout << "((" << bestEliminationSequence->edgeElimVector[c].i << "," << bestEliminationSequence->edgeElimVector[c].j << ")," << bestEliminationSequence->edgeElimVector[c].front << ") ";
  cout << endl << endl << "****** Now re-performing bestElimSeqFound until we reach our edge goal of " << bestEliminationSequence->bestNumNontrivialEdges << " nontrivial edges" << endl;
#endif

  unsigned int cost_of_elim_seq = 0;

  if (num_nontrivial_edges (angelLCG, ourAwarenessLevel) == bestEliminationSequence->bestNumNontrivialEdges) {
#ifndef NDEBUG
    cout << "No eliminations necessary to reach the desired edge count of " << bestEliminationSequence->bestNumNontrivialEdges << endl;
#endif
  }
  else { //replay the elimination sequence until we reach edge count goal
    c_graph_t::edge_t e;
    bool found_e;
    for (size_t c = 0; c < bestEliminationSequence->edgeElimVector.size(); c++) {
      bool isFront = bestEliminationSequence->edgeElimVector[c].front;
      // find the edge from i,j representation
      tie (e, found_e) = edge (bestEliminationSequence->edgeElimVector[c].i, bestEliminationSequence->edgeElimVector[c].j, angelLCG);
      throw_exception (!found_e, consistency_exception, "edge in elims_performed could not be found in angelLCG for elimination");

      cost_of_elim_seq += isFront ? front_eliminate_edge_directly (e, angelLCG, ourAwarenessLevel, edge_ref_list, jae_list)
				  : back_eliminate_edge_directly (e, angelLCG, ourAwarenessLevel, edge_ref_list, jae_list);

      if (num_nontrivial_edges (angelLCG, ourAwarenessLevel) == bestEliminationSequence->bestNumNontrivialEdges) {
#ifndef NDEBUG
	cout << "Goal of " << bestEliminationSequence->bestNumNontrivialEdges << " reached" << endl;
#endif
	break;
      }
    }
  }
  delete bestEliminationSequence;

#ifndef NDEBUG
  write_graph ("angelLCG after partial edge elimination sequence (G prime): ", angelLCG);
  writeVertexAndEdgeTypes (cout, angelLCG);
  cout << "compute_partial_elimination_sequence: cost " << cost_of_elim_seq << endl;
#endif

  populate_remainderGraph_and_correlationLists (angelLCG, ourLCG_verts, edge_ref_list, remainderLCG, v_cor_list, e_cor_list);
} // end compute_partial_elimination_sequence()

void compute_partial_transformation_sequence_sa(const LinearizedComputationalGraph& ourLCG,
						const Elimination::AwarenessLevel_E ourAwarenessLevel,
						const bool allowMaintainingFlag,
						JacobianAccumulationExpressionList& jae_list,
						LinearizedComputationalGraph& remainderLCG,
						VertexCorrelationList& v_cor_list,
						EdgeCorrelationList& e_cor_list,
						unsigned int& numReroutings) {
  #ifndef NDEBUG
  cout << "ourAwarenessLevel is set to " << Elimination::AwarenessLevelToString(ourAwarenessLevel) << endl;
  #endif

  srand(time(NULL));

  // Create internal (angel) LCG from xaifBooster LCG
  vector<const LinearizedComputationalGraphVertex*> ourLCG_verts;
  c_graph_t angelLCG_orig;
  list<EdgeRef_t> edge_ref_list;
  ourLCG_to_angelLCG (ourLCG, ourLCG_verts, angelLCG_orig, edge_ref_list);

  unsigned int max_steps = 20 * num_vertices(angelLCG_orig);
  double T = 10;

  transformationSeq_cost_t dummy_transformationSeq_cost (0, 0, 0, 0, 0, 0);
  refillDependenceMap_t dummy_refillDependenceMap;
  vector<Transformation> allViableTransformationsV, transformationSeqV, best_transformationSeqV;
  c_graph_t angelLCG (angelLCG_orig);
  unsigned int previous_numNontrivialEdges = num_nontrivial_edges(angelLCG, ourAwarenessLevel);
  unsigned int bestNumNontrivialEdges = num_nontrivial_edges(angelLCG, ourAwarenessLevel);
  unsigned int computationalCost_at_bestEdgeCount = 0;
  unsigned int computationalCost = 0;
  for (unsigned int steps_counter = 0; steps_counter < max_steps; steps_counter++) {
    // adjust temperature
    if(steps_counter%10 == 0)
      T = 10;
    else
      T = T / 2.0;
    #ifndef NDEBUG
    cout << "datapoint:" << T << ":" << computationalCost << ":" << num_nontrivial_edges(angelLCG, ourAwarenessLevel) << endl;
    #endif

    // assess the effect of each viable transformation
    all_viable_transformations(angelLCG, transformationSeqV, allViableTransformationsV);
    if (allViableTransformationsV.empty())
      break;
    vector<double> deltaE(allViableTransformationsV.size() + 1);
    for (size_t c = 0; c < allViableTransformationsV.size(); c++)
      deltaE[c] = transformation_effect(allViableTransformationsV[c], angelLCG, ourAwarenessLevel);
    // calculate probability for going backwards one step
    deltaE[allViableTransformationsV.size()] = (int)previous_numNontrivialEdges - (int)num_nontrivial_edges(angelLCG, ourAwarenessLevel);

    unsigned int choice_index = chooseTarget_sa(deltaE, T);
    if (choice_index != allViableTransformationsV.size()) { // perform a transformation
      previous_numNontrivialEdges = num_nontrivial_edges(angelLCG, ourAwarenessLevel);
      transformationSeqV.push_back(allViableTransformationsV[choice_index]);
      // REROUTING
      if (allViableTransformationsV[choice_index].isRerouting) {
	computationalCost += allViableTransformationsV[choice_index].getRerouting().isPre() ?
	   prerouteEdge_noJAE(allViableTransformationsV[choice_index].getRerouting().getER(angelLCG), angelLCG, ourAwarenessLevel)
	 : postrouteEdge_noJAE(allViableTransformationsV[choice_index].getRerouting().getER(angelLCG), angelLCG, ourAwarenessLevel);
      }
      // EDGE ELIM
      else {
	computationalCost += allViableTransformationsV[choice_index].getEdgeElim().isFront() ?
	   frontEdgeElimination_noJAE(allViableTransformationsV[choice_index].getEdgeElim().getE(angelLCG), angelLCG, ourAwarenessLevel, &dummy_transformationSeq_cost, dummy_refillDependenceMap)
	 : backEdgeElimination_noJAE(allViableTransformationsV[choice_index].getEdgeElim().getE(angelLCG), angelLCG, ourAwarenessLevel, &dummy_transformationSeq_cost, dummy_refillDependenceMap);
      } // end edge elim

      // check whether we've beaten our CURRENT best
      if (num_nontrivial_edges (angelLCG, ourAwarenessLevel) < bestNumNontrivialEdges
       || (num_nontrivial_edges (angelLCG, ourAwarenessLevel) == bestNumNontrivialEdges && computationalCost < computationalCost_at_bestEdgeCount)) {
	bestNumNontrivialEdges = num_nontrivial_edges (angelLCG, ourAwarenessLevel);
	computationalCost_at_bestEdgeCount = computationalCost;
	best_transformationSeqV = transformationSeqV;
	#ifndef NDEBUG
	cout << "** New best_num_edges found: " << bestNumNontrivialEdges
	     << " with computational cost " << computationalCost 
	     << " after " << transformationSeqV.size() << " transformations" << endl;
	#endif
      }
    } // end perform a transformation
    else { // this corresponds to a backtracking (NOTE: going back cannot lead to a new "best-so-far" result)
      #ifndef NDEBUG
      cout << "Performing a BACKTRACKING step" << endl;
      #endif
      if (transformationSeqV.empty())
	continue;
      angelLCG = angelLCG_orig;
      transformationSeqV.pop_back();
      computationalCost = replay_transformation_seq(angelLCG, transformationSeqV, previous_numNontrivialEdges, ourAwarenessLevel, dummy_transformationSeq_cost, dummy_refillDependenceMap);
    } // end backtracking
  }

  #ifndef NDEBUG
  cout << "Achieved a nontrivial edge count of " << bestNumNontrivialEdges << endl;
  cout << "Best sequence of transformations: " << endl;
  for (size_t c = 0; c < best_transformationSeqV.size(); c++)
    cout << best_transformationSeqV[c].debug().c_str() << endl;
  cout << endl << endl << "****** Now re-performing best_transformationSeqV until we reach our edge goal of " << bestNumNontrivialEdges << " nontrivial edges" << endl;
  #endif

  //replay the elimination sequence until we reach edge count goal
  numReroutings = 0;
  unsigned int cost_of_transformation_seq = 0;
  if (num_nontrivial_edges (angelLCG_orig, ourAwarenessLevel) > bestNumNontrivialEdges) {
    for (size_t c = 0; c < best_transformationSeqV.size(); c++) {
/*
      if (transformationSeqV[c].isRerouting) { // REROUTING
	numReroutings++;
	edge_reroute_t er (allViableTransformationsV[current_ind].myRerouteElim);
	cost_of_transformation_seq += er.isPre ? preroute_edge_directly(er, angelLCG, ourAwarenessLevel, edge_ref_list, jae_list)
					       : postroute_edge_directly(er, angelLCG, ourAwarenessLevel, edge_ref_list, jae_list);
      }
      else { // EDGE ELIMINATION
	edge_ij_elim_t eij (allViableTransformationsV[current_ind].myElim);
	c_graph_t::edge_t e;
	getEdgeFromIJRep(eij, angelLCG, e);
	cost_of_transformation_seq += eij.front ? front_eliminate_edge_directly(e, angelLCG_orig, ourAwarenessLevel, edge_ref_list, jae_list)
						: back_eliminate_edge_directly(e, angelLCG_orig, ourAwarenessLevel, edge_ref_list, jae_list);
      }
*/
      if (num_nontrivial_edges (angelLCG_orig, ourAwarenessLevel) == bestNumNontrivialEdges) {
	#ifndef NDEBUG
	cout << "Goal of " << bestNumNontrivialEdges << " reached" << endl;
	#endif
	break;
      }
    }
  }
  #ifndef NDEBUG
  else
    cout << "No eliminations necessary to reach the desired edge count of " << bestNumNontrivialEdges << endl;
  #endif

  #ifndef NDEBUG
  write_graph ("angelLCG after partial transformation sequence (G prime): ", angelLCG_orig);
  writeVertexAndEdgeTypes (cout, angelLCG_orig);
  cout << "compute_partial_transformation_sequence: cost " << cost_of_transformation_seq << endl;
  #endif
  populate_remainderGraph_and_correlationLists (angelLCG_orig, ourLCG_verts, edge_ref_list, remainderLCG, v_cor_list, e_cor_list);
} // end compute_partial_transformation_sequence_sa()

void compute_partial_transformation_sequence (const LinearizedComputationalGraph& ourLCG,
					      const Elimination::AwarenessLevel_E ourAwarenessLevel,
					      const bool allowMaintainingFlag,
					      JacobianAccumulationExpressionList& jae_list,
					      LinearizedComputationalGraph& remainderLCG,
					      VertexCorrelationList& v_cor_list,
					      EdgeCorrelationList& e_cor_list,
					      unsigned int& numReroutings) {
#ifndef NDEBUG
  cout << "allowMaintainingFlag is set to "; if (allowMaintainingFlag) cout << "true"; else cout << "false";
  cout << ", and ourAwarenessLevel is set to " << Elimination::AwarenessLevelToString(ourAwarenessLevel) << endl;
  cout << "Creating internal angel LCG...." << endl;
#endif

  // Create internal (angel) LCG from xaifBooster LCG
  vector<const LinearizedComputationalGraphVertex*> ourLCG_verts;
  c_graph_t angelLCG;
  list<EdgeRef_t> edge_ref_list;
  ourLCG_to_angelLCG (ourLCG, ourLCG_verts, angelLCG, edge_ref_list);

#ifndef NDEBUG
  cout << endl << "*************************************************************************************" << endl; 
  cout << "Determining a partial sequence of transformations..." << endl;
  cout << "*************************************************************************************" << endl; 
#endif

  // To begin with, the best transformation sequence is NO transformation sequence
  transformationSeq_cost_t *bestTransformationSequence = new transformationSeq_cost_t (num_nontrivial_edges(angelLCG, ourAwarenessLevel),
										       0,
										       0,
										       numIntermediateVertices(angelLCG),
										       numIntermediateVerticesWithoutUnitEdge(angelLCG),
										       0);
  transformationSeq_cost_t *currentTransformationSequence;

  refillDependenceMap_t refillDependences;
  vector<Transformation_t> allViableTransformationsV,
			   maintainingTransformationsV,
			   reducingTransformationsV,
			   reroutingConsiderateTransformationsV,
			   refillAvoidingTransformationsV,
			   lowestMarkowitzTransformationsV,
			   reverseModeTransformationsV;

  // determine a best transformation sequence
  unsigned int seqNum = 0;
  while (true) {
    c_graph_t angelLCG_copy (angelLCG);
    currentTransformationSequence = new transformationSeq_cost_t (num_nontrivial_edges(angelLCG_copy, ourAwarenessLevel),
								  0,
								  0,
								  numIntermediateVertices(angelLCG_copy),
								  numIntermediateVerticesWithoutUnitEdge(angelLCG),
								  0);

#ifndef NDEBUG
    cout << "++++++++++++++++++++++++" << endl << "TRYING A NEW COMPLETE TRANSFORMATION SEQUENCE" << "++++++++++++++++++++++++" << endl;
#endif

    // run currentTransformationSequence
    unsigned int elimNum = 0;
    while (true) {
#ifndef NDEBUG
      cout << "datapoint:" << seqNum << ":" << elimNum << ":" << num_nontrivial_edges(angelLCG_copy, ourAwarenessLevel) << endl;
#endif

      // run filters
      if (!all_viable_transformations (angelLCG_copy, currentTransformationSequence->transformationVector, allViableTransformationsV)) break;
      maintaining_transformations (allViableTransformationsV, angelLCG_copy, ourAwarenessLevel, maintainingTransformationsV);
      reducing_transformations (maintainingTransformationsV, angelLCG_copy, ourAwarenessLevel, reducingTransformationsV);
      rerouting_considerate_transformations (reducingTransformationsV, angelLCG_copy, currentTransformationSequence->transformationVector, reroutingConsiderateTransformationsV);
      refill_avoiding_transformations (reroutingConsiderateTransformationsV, angelLCG_copy, ourAwarenessLevel, refillDependences, refillAvoidingTransformationsV);
      lowest_markowitz_transformations (refillAvoidingTransformationsV, angelLCG_copy, lowestMarkowitzTransformationsV);
      reverse_mode_transformations (lowestMarkowitzTransformationsV, angelLCG_copy, reverseModeTransformationsV);

      Transformation_t chosenTransformation = reverseModeTransformationsV[0];
      currentTransformationSequence->transformationVector.push_back(chosenTransformation);

      if (!chosenTransformation.isRerouting) { // EDGE ELIMINATION
	// recover edge from ij representation
	c_graph_t::edge_t e;
	bool found_e;
	tie(e, found_e) = edge (chosenTransformation.myElim.i, chosenTransformation.myElim.j, angelLCG_copy);
	throw_exception (!found_e, consistency_exception, "edge could not be found from ij representation");

	bool isFront = chosenTransformation.myElim.front;
	currentTransformationSequence->cost += isFront ? frontEdgeElimination_noJAE (e, angelLCG_copy, ourAwarenessLevel, currentTransformationSequence, refillDependences)
						       : backEdgeElimination_noJAE (e, angelLCG_copy, ourAwarenessLevel, currentTransformationSequence, refillDependences);
      } // end edge elimination

      else { // REROUTING
	edge_reroute_t er = chosenTransformation.myRerouteElim;

	cout << "Chosen rerouting:" << endl;
	if (er.pivot_eliminatable) cout << "  -> is pivot eliminatable" << endl;
	if (er.increment_eliminatable) cout << "  -> is increment eliminatable" << endl;
	if (!er.type3EdgeElimVector.empty()) {
	  cout << "  -> is type 3 eliminatable:" << endl;
	  write_vector("type 3 edge elim vertices: ", er.type3EdgeElimVector);
	}

#ifndef NDEBUG
	if (er.isPre) cout << "pre"; else cout << "post";
	cout << "-routing edge " << er.e << " about pivot edge " << er.pivot_e << endl;
#endif
        currentTransformationSequence->cost += er.isPre ? prerouteEdge_noJAE (er, angelLCG_copy, ourAwarenessLevel)
                                                        : postrouteEdge_noJAE (er, angelLCG_copy, ourAwarenessLevel);
      } // end rerouting

      // check whether we've beaten our CURRENT best
      if (num_nontrivial_edges (angelLCG_copy, ourAwarenessLevel) < currentTransformationSequence->bestNumNontrivialEdges) {
        currentTransformationSequence->bestNumNontrivialEdges = num_nontrivial_edges (angelLCG_copy, ourAwarenessLevel);
        currentTransformationSequence->costAtBestEdgecount = currentTransformationSequence->cost;
	currentTransformationSequence->numIntermediatesAtBestEdgecount = numIntermediateVertices(angelLCG_copy);
	currentTransformationSequence->numIntermediatesWithoutUnitEdgeAtBestEdgecount = numIntermediateVerticesWithoutUnitEdge(angelLCG_copy);
        currentTransformationSequence->lastDesiredTransformation = currentTransformationSequence->transformationVector.size();
#ifndef NDEBUG
        cout << "** new best_num_edges for currentTransformationSequence: " << currentTransformationSequence->bestNumNontrivialEdges << endl;
#endif
      }

      elimNum++;
    } // end of transformation sequence

    bool notFinishedYet = currentTransformationSequence->revealedNewDependence;

#ifndef NDEBUG
    cout << "complete elim sequence complete.  This sequence achieved " << currentTransformationSequence->bestNumNontrivialEdges << " edges and ";
    if (currentTransformationSequence->revealedNewDependence) cout << "DID"; else cout << "DID NOT";
    cout << " add new dependence information to the dependence map" << endl;
    write_refillDependences (cout, refillDependences);
#endif
     
    // check whether we've beaten our OVERALL best, or MATCHED it with lower cost
    if (currentTransformationSequence->bestNumNontrivialEdges < bestTransformationSequence->bestNumNontrivialEdges
     || (currentTransformationSequence->bestNumNontrivialEdges == bestTransformationSequence->bestNumNontrivialEdges
      && currentTransformationSequence->costAtBestEdgecount < bestTransformationSequence->costAtBestEdgecount)) {
      delete bestTransformationSequence;
      bestTransformationSequence = currentTransformationSequence;
      currentTransformationSequence = NULL;
#ifndef NDEBUG
      cout << "This transformation sequence is best so far" << endl;
#endif
    }
    else { // latest transformation sequence isn't an improvement
#ifndef NDEBUG
      cout << "This transformation isn't an improvement" << endl;
#endif
      delete currentTransformationSequence;
    }
     
    // determine whether it's time to stop
    if (!notFinishedYet) break;

    seqNum++;
  } // end determine a best transformation sequence

#ifndef NDEBUG
  // Really, we output the number of intermediates with no incident unit edge (can be normalized)
  cout << "The best transformation sequence achieves a nontrivial edge count of " << bestTransformationSequence->bestNumNontrivialEdges
       << ", at which point there are " << bestTransformationSequence->numIntermediatesWithoutUnitEdgeAtBestEdgecount << " intermediate vertices" << endl;
       //<< ", at which point " << bestTransformationSequence->numIntermediatesWithoutUnitEdgeAtBestEdgecount << " of "
       //<< bestTransformationSequence->numIntermediatesAtBestEdgecount << " intermediate vertices have no incident unit edges" << endl;
#endif

/* AL: COMMENTED OUT BECAUSE DIVISIONS AND SUBTRACTIONS (REQUIRED FOR REROUTINGS) ARE NOT IMPLEMENTED AS JAES
#ifndef NDEBUG
  cout << endl << "*************************************************************************************" << endl; 
  cout << "Now performing the best partial sequence of transformations..." << endl;
  cout << "*************************************************************************************" << endl; 
#endif

  unsigned int cost_of_transformation_seq = 0;

  // Perform the best transformation sequence
  for (size_t i = 0; i < bestTransformationSequence->transformationVector.size(); i++) {

    if (bestTransformationSequence->transformationVector[i].isRerouting) { // rerouting followed by elimination(s)
      //perform the rerouting
      if (bestTransformationSequence->transformationVector[i].myRerouteElim.isPre) { // pre-routing
#ifndef NDEBUG
	cout << "pre-routing edge " << bestTransformationSequence->transformationVector[i].myRerouteElim.e
	     << " about pivot edge " << bestTransformationSequence->transformationVector[i].myRerouteElim.pivot_e;
#endif
	cost_of_elim_seq += preroute_edge_directly (bestTransformationSequence->transformationVector[i].myRerouteElim, angelLCG, ourAwarenessLevel, edge_ref_list, jae_list);
      } // end pre-routing
      else { //post-routing
#ifndef NDEBUG
	cout << "post-routing edge " << bestTransformationSequence->transformationVector[i].myRerouteElim.e
	     << " about pivot edge " << bestTransformationSequence->transformationVector[i].myRerouteElim.pivot_e;
#endif
	cost_of_elim_seq += postroute_edge_directly (bestTransformationSequence->transformationVector[i].myRerouteElim, angelLCG, ourAwarenessLevel, edge_ref_list, jae_list);
      } // end post-routing

    } // end rerouting followed by elimination(s)
    else { // just a single edge elimination

      // find the edge from i,j representation
      c_graph_t::edge_t e;
      bool found_e;
      tie(e, found_e) = edge(bestTransformationSequence->transformationVector[i].myElim.i, bestTransformationSequence->transformationVector[i].myElim.j, angelLCG);
      throw_exception (!found_e, consistency_exception, "edge in transformationVector could not be found in angelLCG for elimination");
      bool isFront = bestTransformationSequence->transformationVector[i].myElim.front;
#ifndef NDEBUG
      if (isFront) cout << "Front-eliminating edge " << e << "..." << endl; else cout << "Back-eliminating edge " << e << "..." << endl;
#endif
      cost_of_elim_seq += isFront ? front_eliminate_edge_directly (e, angelLCG, ourAwarenessLevel, edge_ref_list, jae_list)
				  : back_eliminate_edge_directly (e, angelLCG, ourAwarenessLevel, edge_ref_list, jae_list);
    } // end just a single edge elimination

    // break when we've reached our goal
    if (num_nontrivial_edges (angelLCG, ourAwarenessLevel) == bestTransformationSequence->bestNumNontrivialEdges) break;
  } // end iterate through 

#ifndef NDEBUG
    cout << "Goal of " << bestTransformationSequence->bestNumNontrivialEdges << " reached" << endl;
#endif
*/ 
  delete bestTransformationSequence; 

  populate_remainderGraph_and_correlationLists (angelLCG, ourLCG_verts, edge_ref_list, remainderLCG, v_cor_list, e_cor_list);

//#ifndef NDEBUG
  //cout << "compute_partial_transformation_sequence: cost " << cost_of_transformation_seq << endl;
//#endif

} // end compute_partial_transformation_sequence()

void compute_elimination_sequence (const LinearizedComputationalGraph& xgraph,
				   JacobianAccumulationExpressionList& JAElist,
				   LinearizedComputationalGraph& remainderLCG,
				   VertexCorrelationList& v_cor_list,
				   EdgeCorrelationList& e_cor_list) {
  c_graph_t cg;
  vector<const LinearizedComputationalGraphVertex*> av;
  vector<edge_address_t> ae;
  read_graph_xaif_booster (xgraph, cg, av, ae);

  typedef heuristic_pair_t<lowest_markowitz_vertex_t, reverse_mode_vertex_t>                   lm_rm_t;
  typedef heuristic_pair_t<lmmd_vertex_t, reverse_mode_vertex_t>                               lmmd_rm_t;
  typedef heuristic_triplet_t<momr_vertex_t, lowest_markowitz_vertex_t, reverse_mode_vertex_t> momr_lm_rm_t;
  lm_rm_t                       lm_rm_v (lowest_markowitz_vertex, reverse_mode_vertex); 
  lmmd_rm_t                     lmmd_rm_v (lmmd_vertex, reverse_mode_vertex);
  momr_lm_rm_t                  momr_lm_rm_v (momr_vertex, lowest_markowitz_vertex, reverse_mode_vertex); 

  edge_ij_elim_heuristic_t<forward_mode_edge_t>      fm_ij (forward_mode_edge);
  edge_ij_elim_heuristic_t<reverse_mode_edge_t>      rm_ij (reverse_mode_edge);
  emulated_vertex_heuristic_t<lm_rm_t>               lm_rm_e (lm_rm_v);
  emulated_vertex_heuristic_t<lmmd_rm_t>             lmmd_rm_e (lmmd_rm_v);
  emulated_vertex_heuristic_t<momr_lm_rm_t>          momr_lm_rm_e (momr_lm_rm_v);

  vector<c_graph_t::vertex_t>   vseq;
  vector<edge_ij_elim_t>        eseq; 

  if (vertex_eliminatable (cg)) {

#ifndef NDEBUG
    int costs= best_heuristic (cg, vseq, forward_mode_vertex, reverse_mode_vertex, 
			       lm_rm_v, lmmd_rm_v, momr_lm_rm_v);
    write_vector("Vertex elimination: sequence",vseq);
    cout << "Costs are " << costs << '\n';
#else
    best_heuristic (cg, vseq, forward_mode_vertex, reverse_mode_vertex, 
			       lm_rm_v, lmmd_rm_v, momr_lm_rm_v);
#endif

    convert_elimination_sequence (vseq, cg, eseq);

#ifndef NDEBUG
    write_vector("Same elimination sequence as edge eliminations", eseq);
#endif

  } else {
#ifndef NDEBUG
    int costs= best_heuristic (cg, eseq, fm_ij, rm_ij, lm_rm_e, lmmd_rm_e, momr_lm_rm_e);
    write_vector("Edge elimination: sequence",eseq);
    cout << "Costs are " << costs << '\n'; 
#else 
    best_heuristic (cg, eseq, fm_ij, rm_ij, lm_rm_e, lmmd_rm_e, momr_lm_rm_e);
#endif
  }

  line_graph_t lg (cg);
  vector<triplet_t>               tv;
  convert_elimination_sequence (eseq, lg, tv);

#ifndef NDEBUG
  write_vector("Same elimination sequence as face eliminations", tv);  
#endif

  accu_graph_t ac (cg, lg);
  for (size_t c= 0; c < tv.size(); c++) 
    face_elimination (tv[c], lg, ac);

#ifndef NDEBUG
  write_graph ("Empty line graph", lg);
  line_graph_t::evn_t            evn= get(vertex_name, lg);
  write_vertex_property (cout, "vertices of this edge graph", evn, lg);
#endif
  
  ac.set_jacobi_entries ();

#ifndef NDEBUG
  for (size_t c= 0; c < ac.accu_exp.size(); c++) {
    write_graph ("Accumulation graph", ac.accu_exp[c]);
    property_map<pure_accu_exp_graph_t, vertex_name_t>::type vprop= 
      get (vertex_name, ac.accu_exp[c]);
    write_vertex_property (cout, "Vertex props", vprop, ac.accu_exp[c]); 
    ad_edge_t my_jacobi= ac.jacobi_entries[c];
    if (my_jacobi.second == 0) cout << "isn't Jacobian entry\n";
    else cout << "is Jacoby entry: " << my_jacobi << std::endl; }
#endif

  write_graph_xaif_booster (ac, av, ae, JAElist, remainderLCG, v_cor_list, e_cor_list);
} // end of angel::compute_elimination_sequence()

void compute_elimination_sequence_lsa_face (const LinearizedComputationalGraph& xgraph,
					    int iterations, 
					    double gamma,
					    JacobianAccumulationExpressionList& JAElist,
					    LinearizedComputationalGraph& remainderLCG,
					    VertexCorrelationList& v_cor_list,
					    EdgeCorrelationList& e_cor_list) {
  c_graph_t                                            cg;
  vector<const LinearizedComputationalGraphVertex*>    av;
  vector<edge_address_t>                               ae;
  read_graph_xaif_booster (xgraph, cg, av, ae);
  line_graph_t                                         lg (cg);

  face_elimination_history_t                           feh (lg);
  typedef triplet_heuristic_t<reverse_mode_face_t>     rm_t;
  rm_t                                                 rm (reverse_mode_face);
  SA_elimination_cost_t<rm_t>                          cost (rm);
  neighbor_sequence_check_t                            neighbor;
  
  // int elim_costs= 
    LSA (feh, neighbor, cost, gamma, iterations);
  feh.complete_sequence (rm);

  accu_graph_t ac (cg, lg);
  for (size_t c= 0; c < feh.seq.size(); c++) 
    face_elimination (feh.seq[c], lg, ac);
  ac.set_jacobi_entries ();

  write_graph_xaif_booster (ac, av, ae, JAElist, remainderLCG, v_cor_list, e_cor_list);

} // end of angel::compute_elimination_sequence_lsa_face()

void compute_elimination_sequence_lsa_vertex (const LinearizedComputationalGraph& xgraph,
					      int iterations, 
					      double gamma,
					      JacobianAccumulationExpressionList& JAElist,
					      LinearizedComputationalGraph& remainderLCG,
					      VertexCorrelationList& v_cor_list,
					      EdgeCorrelationList& e_cor_list) {
  c_graph_t                                            cg;
  vector<const LinearizedComputationalGraphVertex*>    av;
  vector<edge_address_t>                               ae;
  read_graph_xaif_booster (xgraph, cg, av, ae);

  // Check if vertex elimination works
  for (size_t i= 0; i != cg.dependents.size(); i++)
    // version 1
    if (out_degree (cg.dependents[i], cg) > 0) {
      cerr << "Warning! Vertex elimination not possible with this graph, because at least one dependent vertex has at least one outedge.\n"
	   << "Calling LSA for face elimination with same parameters (may take longer)...\n";
      return compute_elimination_sequence_lsa_face (xgraph, iterations, gamma, JAElist, remainderLCG, v_cor_list, e_cor_list);}
    // version 2
    // throw_exception (out_degree (cg.dependents[i], cg) > 0, consistency_exception, "Vertex elimination not possible with these graph.");
      
  vertex_elimination_history_t                         veh (cg);
  SA_elimination_cost_t<reverse_mode_vertex_t>         cost (reverse_mode_vertex);
  neighbor_sequence_check_t                            neighbor;

  // int elim_costs= 
    LSA (veh, neighbor, cost, gamma, iterations);
  veh.complete_sequence (reverse_mode_vertex);

  vector<edge_ij_elim_t>                              eseq; 
  vector<triplet_t>                                   tv;
  line_graph_t                                        lg (cg);
  convert_elimination_sequence (veh.seq, cg, eseq);
  convert_elimination_sequence (eseq, lg, tv);

  accu_graph_t ac (cg, lg);
  for (size_t c= 0; c < tv.size(); c++) 
    face_elimination (tv[c], lg, ac);
  ac.set_jacobi_entries ();

  write_graph_xaif_booster (ac, av, ae, JAElist, remainderLCG, v_cor_list, e_cor_list);
} // end of angel::compute_elimination_sequence_lsa_vertex()

} // end namespace angel

namespace xaifBoosterCrossCountryInterface {

void xaifBoosterCrossCountryInterface::Elimination::eliminate() {

  try {
    if (myType == REGULAR_ELIMTYPE) {
      compute_elimination_sequence (getLCG(),
				    getEliminationResult().myJAEList,
				    getEliminationResult().myRemainderLCG,
				    getEliminationResult().myVertexCorrelationList,
				    getEliminationResult().myEdgeCorrelationList);
    }
    else if (myType == LSA_VERTEX_ELIMTYPE) {
      compute_elimination_sequence_lsa_vertex (getLCG(),
					       getNumIterations(),
					       getGamma(),
					       getEliminationResult().myJAEList,
					       getEliminationResult().myRemainderLCG,
					       getEliminationResult().myVertexCorrelationList,
					       getEliminationResult().myEdgeCorrelationList);
    }
    else if (myType == LSA_FACE_ELIMTYPE) {
      compute_elimination_sequence_lsa_face (getLCG(),
					     getNumIterations(),
					     getGamma(),
					     getEliminationResult().myJAEList,
					     getEliminationResult().myRemainderLCG,
					     getEliminationResult().myVertexCorrelationList,
					     getEliminationResult().myEdgeCorrelationList);
    }
    else if (myType == SCARCE_ELIMTYPE) {
      compute_partial_elimination_sequence_sa (getLCG(),
					    ourAwarenessLevel,
					    ourAllowMaintainingFlag,
					    getEliminationResult().myJAEList,
					    getEliminationResult().myRemainderLCG,
					    getEliminationResult().myVertexCorrelationList,
					    getEliminationResult().myEdgeCorrelationList);
    }
    else if (myType == SCARCE_TRANSFORMATION_TYPE) {
      compute_partial_transformation_sequence_sa (getLCG(),
					       ourAwarenessLevel,
					       ourAllowMaintainingFlag,
					       getEliminationResult().myJAEList,
					       getEliminationResult().myRemainderLCG,
					       getEliminationResult().myVertexCorrelationList,
					       getEliminationResult().myEdgeCorrelationList,
					       getEliminationResult().myNumReroutings);
    }
    else throw_exception (true, consistency_exception, "Missing or invalid elimination type");
  }
  catch (base_exception e) { 
    throw EliminationException(std::string("angel exception caught within Elimination::eliminate() : ")+e.what_reason());
  }

} // end of Elimination::eliminate()

} // end namespace xaifBoosterCrossCountryInterface

#endif // USEXAIFBOOSTER

