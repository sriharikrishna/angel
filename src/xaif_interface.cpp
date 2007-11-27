#ifdef USEXAIFBOOSTER

#include <set>

#include "xaif_interface.hpp"
#include "eliminations.hpp"
#include "reroutings.hpp"
#include "heuristics.hpp"
#include "angel_tools.hpp"

#include "angel_io.hpp"
#include "sa.hpp"

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
			       JacobianAccumulationExpressionList& elist) {
  typedef LinearizedComputationalGraphVertex      xlvertex_t;
  typedef JacobianAccumulationExpressionVertex    xavertex_t;
  // line_graph_t::const_evn_t evn= get (vertex_name, ag.lg);
      
  vector<xavertex_t*> exp_output_pr; // pointer to output vertex of expression
  for (size_t c= 0; c < ag.accu_exp.size(); c++) {
    const accu_exp_graph_t& my_exp= ag.accu_exp[c];
    property_map<pure_accu_exp_graph_t, vertex_name_t>::const_type vpr= get (vertex_name, my_exp);

    JacobianAccumulationExpression& new_exp= elist.addExpression();
    //exp_pr.push_back(&new_exp);
    vector<xavertex_t*>  vp (my_exp.v());
    for (size_t vc= 0; vc < (size_t) my_exp.v(); vc++) {      
      const accu_exp_t& prop= vpr[vc];
      xavertex_t& new_vertex= new_exp.addVertex();
      vp[vc]= &new_vertex;
      if (vc+1 == (size_t) my_exp.v()) exp_output_pr.push_back(&new_vertex);
      switch (prop.ref_kind) { 
      case accu_exp_t::nothing: throw_exception (true, consistency_exception, "Unset vertex"); break;
      case accu_exp_t::exp:    
	           throw_debug_exception (prop.ref.exp_nr >= int (c), consistency_exception, 
					  "Expression number too large")
	           new_vertex.setInternalReference (*exp_output_pr[prop.ref.exp_nr]); break;
      case accu_exp_t::lgn: {    
	  const LinearizedComputationalGraphEdge* ptr= xaif_edge_pr (prop.ref.node, ag, ae); 
	  throw_debug_exception (ptr == NULL, consistency_exception, "Unset reference");
	  new_vertex.setExternalReference (*ptr); } break;
      case accu_exp_t::isop:    
	new_vertex.setOperation (prop.ref.op == accu_exp_t::add ? xavertex_t::ADD_OP : 
				 xavertex_t::MULT_OP); } }
    
    graph_traits<pure_accu_exp_graph_t>::edge_iterator ei, e_end;   // set edges
    for (tie (ei, e_end)= edges (my_exp); ei != e_end; ei++)
      new_exp.addEdge (*vp[source (*ei, my_exp)], *vp[target (*ei, my_exp)]);

    ad_edge_t my_jacobi= ag.jacobi_entries[c];
    if (my_jacobi.second != 0)
      new_exp.setJacobianEntry (*av[my_jacobi.second], *av[my_jacobi.first]);
  } // end expression
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

/*
elimSeq_cost_t determine_edge_elimination_sequence (const c_graph_t angelLCG,
						    const Elimination::AwarenessLevel_E ourAwarenessLevel,
						    const bool allowMaintainingFlag) {

  elimSeq_cost_t bestElimSeqFound (num_nontrivial_edges(angelLCG, ourAwarenessLevel), 0, 0, 0);
  // while I eliminate, build up list of refill dependences.  This is STATIC, because I store the vertex dependences
  refillDependenceMap_t refillDependences;
  vector<edge_bool_t> bev1, bev2, bev3, bev4, bev5;

  unsigned int seqNum = 0;

  while (true) {

#ifndef NDEBUG
    cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++" << endl;
    cout << "TRYING A NEW COMPLETE ELIMINATION SEQUENCE" << endl;
    cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++" << endl;
#endif

    c_graph_t angelLCG_copy (angelLCG);
    elimSeq_cost_t currentElimSeq (num_nontrivial_edges (angelLCG_copy, ourAwarenessLevel), 0, 0, 0);

    unsigned int elimNum = 0;

    // perform a complete elimination sequence that preserves scarcity and tries to avoid refill
    while(true) {
      //cout << "datapoint:" << seqNum << ":" << elimNum << ":" << num_nontrivial_edges(angelLCG_copy, ourAwarenessLevel) << endl;

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

      if (bev5.empty()) break;

      c_graph_t::edge_t e = bev5[0].first;
      bool isFront = bev5[0].second;
      edge_ij_elim_t thisElim (source (e, angelLCG), target (e, angelLCG), isFront);
      currentElimSeq.edgeElimVector.push_back(thisElim);

#ifndef NDEBUG
      if (isFront) cout << "Front-eliminating edge " << e << "..." << endl; else cout << "Back-eliminating edge " << e << "..." << endl;
#endif
      currentElimSeq.cost += isFront ? front_elim (e, angelLCG_copy, ourAwarenessLevel, currentElimSeq, refillDependences)
				     : back_elim (e, angelLCG_copy, ourAwarenessLevel, currentElimSeq, refillDependences);

      // check whether we've beaten our CURRENT best
      if (num_nontrivial_edges (angelLCG_copy, ourAwarenessLevel) < currentElimSeq.bestNumNontrivialEdges) {
        currentElimSeq.bestNumNontrivialEdges = num_nontrivial_edges (angelLCG_copy, ourAwarenessLevel);
        currentElimSeq.costAtBestEdgecount = currentElimSeq.cost;
        currentElimSeq.lastDesiredElim = currentElimSeq.edgeElimVector.size();
#ifndef NDEBUG
        cout << "** new best_num_edges for currentElimSeq: " << currentElimSeq.bestNumNontrivialEdges << endl;
#endif
      }

#ifndef NDEBUG
	if (!refillDependences.empty()) {
          cout << endl << "current contents of refillDependences: " << endl;
	  for (refillDependenceMap_t::const_iterator di = refillDependences.begin(); di != refillDependences.end(); di++) {
	    cout <<  "(" << di->first.first << "," << di->first.second << ") -> { ";
	    for (vertex_set_t::const_iterator vsi = di->second.begin(); vsi != di->second.end(); vsi++)
	      cout << *vsi << " ";
	    cout << "}" << endl;
	  }
	  cout << endl;
	}
#endif

    elimNum++;

    } // end of elimination sequence

    // check whether we've beaten our OVERALL best
    if (currentElimSeq.bestNumNontrivialEdges < bestElimSeqFound.bestNumNontrivialEdges
	// also prefer MATCHING best_num_edges with a fewer edge count
	|| (currentElimSeq.bestNumNontrivialEdges == bestElimSeqFound.bestNumNontrivialEdges
	    && currentElimSeq.costAtBestEdgecount < bestElimSeqFound.costAtBestEdgecount)) {
      bestElimSeqFound = currentElimSeq;
#ifndef NDEBUG
      cout << "New bestElimSeqFound" << endl;
#endif
    }

#ifndef NDEBUG
    cout << "complete elim sequence complete.  This sequence achieved " << currentElimSeq.bestNumNontrivialEdges << " edges and ";
    if (currentElimSeq.revealedNewDependence) cout << "DID"; else cout << "DID NOT";
    cout << " add new dependence information to the dependence map" << endl;
#endif

    // determine whether it's time to stop
    if (!currentElimSeq.revealedNewDependence) break;

    seqNum++;
  } // end all elim sequences

  return bestElimSeqFound;
} // end of determine_elimination_sequence()
*/

/*
unsigned int perform_reroutings (c_graph_t& angelLCG,
				 const Elimination::AwarenessLevel_E ourAwarenessLevel,
				 const bool allowMaintainingFlag,
				 list<EdgeRef_t>& edge_ref_list,
				 JacobianAccumulationExpressionList& jae_list,
				 unsigned int& numReroutings) {
  unsigned int cost = 0;
  vector<edge_reroute_t> erv1, erv2;
  reroutable_edges (angelLCG, erv1);
  edge_reducing_rerouteElims_types12 (erv1, angelLCG, ourAwarenessLevel, allowMaintainingFlag, erv2);
#ifndef NDEBUG
  cout << "There are currently " << num_nontrivial_edges (angelLCG, ourAwarenessLevel) << " nontrivial edges in angelLCG" << endl;
  cout << "\n\nOf " << erv1.size() << " possible edge reroutings, " << erv2.size() << " reduce the edge count when followed by an edge elimination" << endl;
#endif

  //cout << "DATA:" << num_nontrivial_edges(angelLCG, ourAwarenessLevel) << endl;

  while (!erv2.empty()) {
    throw_exception (!erv2[0].pivot_eliminatable && !erv2[0].increment_eliminatable, consistency_exception, "rerouting allows neither pivot nor increment to be eliminated");
    c_graph_t::edge_t increment_e;
    bool found_increment_e;

    if (erv2[0].isPre) { // pre-routing
#ifndef NDEBUG
      cout << "prerouting edge " << erv2[0].e << " about pivot edge " << erv2[0].pivot_e;
#endif
      cost += preroute_edge_directly (erv2[0], angelLCG, ourAwarenessLevel, edge_ref_list, jae_list);

      if (erv2[0].increment_eliminatable) { // increment elimination
#ifndef NDEBUG
        cout << ", followed by back elimination of increment edge (" << source (erv2[0].e, angelLCG) << "," << source (erv2[0].pivot_e, angelLCG) << ")";
#endif
        tie (increment_e, found_increment_e) = edge (source (erv2[0].e, angelLCG), source (erv2[0].pivot_e, angelLCG), angelLCG);
        throw_exception (!found_increment_e, consistency_exception, "increment edge could not be found for back-elimination");
        back_eliminate_edge_directly (increment_e, angelLCG, ourAwarenessLevel, edge_ref_list, jae_list);
      }

      if (erv2[0].pivot_eliminatable) { // pivot elimination
#ifndef NDEBUG
        cout << ", followed by front-elimination of pivot edge " << erv2[0].pivot_e;
#endif
        front_eliminate_edge_directly (erv2[0].pivot_e, angelLCG, ourAwarenessLevel, edge_ref_list, jae_list);
      }
#ifndef NDEBUG
      cout << endl;
#endif
    } // end pre-routing
    else { // post-routing
#ifndef NDEBUG
      cout << "postrouting edge " << erv2[0].e << " about pivot edge " << erv2[0].pivot_e;
#endif
      cost += postroute_edge_directly (erv2[0], angelLCG, ourAwarenessLevel, edge_ref_list, jae_list);

      if (erv2[0].increment_eliminatable) { // increment elimination
#ifndef NDEBUG
        cout << ", followed by front elimination of increment edge (" << target (erv2[0].pivot_e, angelLCG) << "," << target (erv2[0].e, angelLCG) << ")";
#endif
        tie (increment_e, found_increment_e) = edge (target (erv2[0].pivot_e, angelLCG), target (erv2[0].e, angelLCG), angelLCG);
        throw_exception (!found_increment_e, consistency_exception, "increment edge could not be found for front elimination");
        front_eliminate_edge_directly (increment_e, angelLCG, ourAwarenessLevel, edge_ref_list, jae_list);
      }

      if (erv2[0].pivot_eliminatable) { // pivot elimination
#ifndef NDEBUG
        cout << ", followed by back-elimination of pivot edge " << erv2[0].pivot_e;
#endif
        back_eliminate_edge_directly (erv2[0].pivot_e, angelLCG, ourAwarenessLevel, edge_ref_list, jae_list);
      }
#ifndef NDEBUG
      cout << endl;
#endif
    } // end post-routing

    numReroutings++;

    reroutable_edges (angelLCG, erv1);
    edge_reducing_rerouteElims_types12 (erv1, angelLCG, ourAwarenessLevel, allowMaintainingFlag, erv2);
#ifndef NDEBUG
    cout << "There are currently " << num_nontrivial_edges (angelLCG, ourAwarenessLevel) << " nontrivial edges in angelLCG" << endl;
    cout << "\n\nOf " << erv1.size() << " possible edge reroutings, " << erv2.size() << " reduce the edge count when followed by an edge elimination" << endl;
#endif
    //cout << "DATA:" << num_nontrivial_edges(angelLCG, ourAwarenessLevel) << endl;
  }

  return cost;
} // end perform_reroutings()
*/

} // end namespace angel

using namespace angel;

namespace xaifBoosterCrossCountryInterface {

void compute_partial_elimination_sequence (const LinearizedComputationalGraph& ourLCG,
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

/* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
 * BUILD ANGELLCG FROM XAIFBOOSTER LCG
 * ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */

  c_graph_t angelLCG;

  // COPY VERTICES -------------------------------------------------------------
  vector<const LinearizedComputationalGraphVertex*> ourLCG_verts;
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
  list<EdgeRef_t> edge_ref_list;
  int edge_number = 0;
  boost::property_map<c_graph_t, EdgeType>::type eType = get(EdgeType(), angelLCG);
  LinearizedComputationalGraph::ConstEdgeIteratorPair eip (ourLCG.edges());
  for (LinearizedComputationalGraph::ConstEdgeIterator ei (eip.first), e_end (eip.second); ei != e_end; ++ei) {
    // locate source and target of edge in angelLCG
    c_graph_t::vertex_t source = which_index (& (ourLCG.getSourceOf (*ei)), ourLCG_verts);
    c_graph_t::vertex_t	target = which_index (& (ourLCG.getTargetOf (*ei)), ourLCG_verts);
    pair<c_graph_t::edge_t, bool> new_edge = add_edge (source, target, edge_number++, angelLCG);
    if ((*ei).getEdgeLabelType() == LinearizedComputationalGraphEdge::UNIT_LABEL)
      eType[new_edge.first] = UNIT_EDGE;
    else if ((*ei).getEdgeLabelType() == LinearizedComputationalGraphEdge::CONSTANT_LABEL) {
      //cout << "---------------------------------------------------------------- FOUND A CONSTANT EDGE ------------------------------------------" << endl;
      eType[new_edge.first] = CONSTANT_EDGE;
    }
    else
      eType[new_edge.first] = VARIABLE_EDGE;
    EdgeRef_t new_edge_ref (new_edge.first, &*ei);
    edge_ref_list.push_back(new_edge_ref);
  } // end for all LCG edges

#ifndef NDEBUG
  write_graph ("angelLCG (constructed from ourLCG): ", angelLCG);
#endif
// END READ GRAPH
//****************************************************************************************************************
/*
#ifndef NDEBUG
  cout << endl << "*************************************************************************************" << endl; 
  cout << "Performing total elim sequences and building up refill dependence information..." << endl;
  cout << "*************************************************************************************" << endl; 
#endif

  // Perform full elim sequences that attempt to avoid refill.
  elimSeq_cost_t bestElimSeqFound = determine_edge_elimination_sequence (angelLCG, ourAwarenessLevel, allowMaintainingFlag);

#ifndef NDEBUG
  cout << "heuristic phase complete.  bestElimSeqFound achieves a nontrivial edge count of " << bestElimSeqFound.bestNumNontrivialEdges << endl;
  cout << "contents of bestElimSeqFound.edgeElimVector: " << endl;
  for (size_t c = 0; c < bestElimSeqFound.edgeElimVector.size(); c++)
    cout << "((" << bestElimSeqFound.edgeElimVector[c].i << "," << bestElimSeqFound.edgeElimVector[c].j << ")," << bestElimSeqFound.edgeElimVector[c].front << ") ";
  cout << endl;

  // Now re-perform the sequence until we reach the best edge count
  cout << endl << "*************************************************************************************" << endl; 
  cout << "Now re-performing bestElimSeqFound until we reach our edge goal of " << bestElimSeqFound.bestNumNontrivialEdges << " edges" << endl;
  cout << "*************************************************************************************" << endl; 
#endif

  unsigned int cost_of_elim_seq = 0;

  if (num_nontrivial_edges (angelLCG, ourAwarenessLevel) == bestElimSeqFound.bestNumNontrivialEdges) {
#ifndef NDEBUG
    cout << "No eliminations necessary to reach the desired edge count of " << bestElimSeqFound.bestNumNontrivialEdges << endl;
#endif
  }
  else { //replay the elimination sequence until we reach edge count goal
    c_graph_t::edge_t e;
    bool found_e;
    for (size_t c = 0; c < bestElimSeqFound.edgeElimVector.size(); c++) {
      bool isFront = bestElimSeqFound.edgeElimVector[c].front;
      // find the edge from i,j representation
      tie (e, found_e) = edge (bestElimSeqFound.edgeElimVector[c].i, bestElimSeqFound.edgeElimVector[c].j, angelLCG);
      throw_exception (!found_e, consistency_exception, "edge in elims_performed could not be found in angelLCG for elimination");
#ifndef NDEBUG
      if (bestElimSeqFound.edgeElimVector[c].front) cout << "Front-eliminating edge " << e << "..." << endl; else cout << "Back-eliminating edge " << e << "..." << endl;
#endif
      cost_of_elim_seq += isFront ? front_eliminate_edge_directly (e, angelLCG, ourAwarenessLevel, edge_ref_list, jae_list)
				  : back_eliminate_edge_directly (e, angelLCG, ourAwarenessLevel, edge_ref_list, jae_list);

      if (num_nontrivial_edges (angelLCG, ourAwarenessLevel) == bestElimSeqFound.bestNumNontrivialEdges) {
#ifndef NDEBUG
	cout << "Goal of " << bestElimSeqFound.bestNumNontrivialEdges << " reached" << endl;
#endif
	break;
      }
    }
  }

#ifndef NDEBUG
  cout << endl << "*************************************************************************************" << endl; 
  cout << "Edge eliminations complete.  Now Performing scarcity-preserving edge reroutings..." << endl;
  cout << "*************************************************************************************" << endl; 
#endif

  // perform the desired reroutings
  //cost_of_elim_seq += perform_reroutings (angelLCG, ourAwarenessLevel, allowMaintainingFlag, edge_ref_list, jae_list, numReroutings);

#ifndef NDEBUG
  write_graph ("angelLCG after partial edge elimination (and rerouting) sequence (G prime): ", angelLCG);
  cout << endl << "*************************************************************************************" << endl; 
  cout << "Rerouting phase complete.  Now building the remainder graph..." << endl;
  cout << "*************************************************************************************" << endl; 
#endif
*/

/*
  cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++" << endl << "TESTING REACHABILITY QUERIES" << endl;
  cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++" << endl;

  property_map<pure_c_graph_t, VertexVisited>::type visited = get(VertexVisited(), angelLCG);
  c_graph_t::vi_t srci, src_end, tgti, tgt_end, cleari, clear_end;
  vertex_set_t upset;

  for (tie(srci, src_end) = vertices(angelLCG); srci != src_end; ++srci) {
    // generate upset
    vertex_upset (*srci, angelLCG, upset);

    // check every other vertex in the graph
    for (tie(tgti, tgt_end) = vertices(angelLCG); tgti != tgt_end; ++tgti) {
      if (*tgti == *srci) continue; // skip the src vertex we're considering

      // clear visited flag for all vertices
      for (tie(cleari, clear_end) = vertices(angelLCG); cleari != clear_end; ++cleari) visited[*cleari] = false;

      vertex_set_t::const_iterator upset_i = upset.find(*tgti);
      bool isReachable = reachable (*srci, *tgti, angelLCG);

      if (upset_i != upset.end()) { // target IS reachable from src
	if (isReachable) cout << "They agree that " << *tgti << " is reachable from " << *srci << endl;
	else cout << "Upset says reachable, but reachable says not" << endl;
      }
      else { // target NOT reachable from src
	if (!isReachable) cout << "They agree that " << *tgti << " is NOT reachable from " << *srci << endl;
	else cout << "Upset says NOT reachable, but reachable says yes" << endl;
      }
    } // end every other vertex
  } // end all vertices
*/

#ifndef NDEBUG
  cout << endl << "*************************************************************************************" << endl; 
  cout << "Determining a partial sequence of transformations..." << endl;
  cout << "*************************************************************************************" << endl; 
#endif

  // To begin with, the best transformation sequence is NO transformation sequence
  transformationSeq_cost_t *bestTransformationSequence = new transformationSeq_cost_t (num_nontrivial_edges(angelLCG, ourAwarenessLevel), 0, 0, 0);
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
    currentTransformationSequence = new transformationSeq_cost_t (num_nontrivial_edges(angelLCG_copy, ourAwarenessLevel), 0, 0, 0);

#ifndef NDEBUG
    cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++" << endl << "TRYING A NEW COMPLETE ELIMINATION SEQUENCE" << endl;
    cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++" << endl;
#endif

    // run currentTransformationSequence
    unsigned int elimNum = 0;
    while (true) {
      cout << "datapoint:" << seqNum << ":" << elimNum << ":" << num_nontrivial_edges(angelLCG_copy, ourAwarenessLevel) << endl;

/*
  vector<edge_reroute_t> allReroutingsV, noncyclicReroutingsV, erv2, erv3;
      reroutable_edges (angelLCG_copy, allReroutingsV);
      noncyclicReroutings (allReroutingsV, currentTransformationSequence->transformationVector, angelLCG_copy, noncyclicReroutingsV);
      edge_reducing_rerouteElims_types12 (noncyclicReroutingsV, angelLCG_copy, ourAwarenessLevel, allowMaintainingFlag, erv2);
      edge_reducing_rerouteElims_type3 (noncyclicReroutingsV, angelLCG_copy, ourAwarenessLevel, allowMaintainingFlag, erv3);
  vector<edge_bool_t> allEdgeElimsV, maintainingEdgeElimsV, reducingEdgeElimsV, lowestMarkowitzEdgeElimsV, reverseModeEdgeElimsV, refillAvoidingEdgeElimsV;
      eliminatable_objects (angelLCG_copy, allEdgeElimsV);
      count_maintain_edge_eliminations (allEdgeElimsV, angelLCG_copy, ourAwarenessLevel, maintainingEdgeElimsV);
      count_reduce_edge_eliminations (maintainingEdgeElimsV, angelLCG_copy, ourAwarenessLevel, reducingEdgeElimsV);
      refill_avoiding_edge_eliminations (reducingEdgeElimsV, angelLCG_copy, refillDependences, refillAvoidingEdgeElimsV);
      lowest_markowitz_edge (refillAvoidingEdgeElimsV, angelLCG_copy, lowestMarkowitzEdgeElimsV);
      reverse_mode_edge (lowestMarkowitzEdgeElimsV, angelLCG_copy, reverseModeEdgeElimsV);
      if (allEdgeElimsV.empty() && noncyclicReroutingsV.empty()) break;
*/

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

      // ELIMINATION
      if (!chosenTransformation.isRerouting) {
	// recover edge from ij representation
	c_graph_t::edge_t e;
	bool found_e;
	tie(e, found_e) = edge (chosenTransformation.myElim.i, chosenTransformation.myElim.j, angelLCG_copy);
	throw_exception (!found_e, consistency_exception, "edge could not be found from ij representation");

	bool isFront = chosenTransformation.myElim.front;
	if (isFront) cout << "Front-eliminating edge " << e << "..." << endl; else cout << "Back-eliminating edge " << e << "..." << endl;
	currentTransformationSequence->cost += isFront ? frontEdgeElimination_noJAE (e, angelLCG_copy, ourAwarenessLevel, currentTransformationSequence, refillDependences)
						       : backEdgeElimination_noJAE (e, angelLCG_copy, ourAwarenessLevel, currentTransformationSequence, refillDependences);
      }

      // REROUTING
      else { // rerouting
	edge_reroute_t er = chosenTransformation.myRerouteElim;
	if (er.isPre) {
	cout << "pre-routing edge " << er.e << " about pivot edge " << er.pivot_e << endl;
	  currentTransformationSequence->cost += prerouteEdge_noJAE (er, angelLCG_copy, ourAwarenessLevel);
/*
	  if (.pivot_eliminatable) {
#ifndef NDEBUG cout << "   ...followed by front-elimination of pivot edge " << .pivot_e << endl #endif
	      front_elim (??.pivot_e, angelLCG_copy, ourAwarenessLevel, currentElimSeq, refillDependences); }
	    if (.increment_eliminatable) {
#ifndef NDEBUG cout << "   ...followed by back-elimination of increment edge " << ?? << endl; #endif
	      back_elim (??, angelLCG_copy, ourAwarenessLevel, currentElimSeq, refillDependences); }
	    if (!.type3EdgeElimVector.empty()) {
	      for (size_t bei = 0; bei < .type3EdgeElimVector.size(); bei++) { #ifndef NDEBUG cout << "   ...followed by back-elimination of edge " << .type3EdgeElimVector[bei] << endl; #endif
		back_elim (??, angelLCG_copy, ourAwarenessLevel, currentElimSeq, refillDependences); } }
*/
	} // end pre-routing
	else { //post-routing
	cout << "post-routing edge " << er.e << " about pivot edge " << er.pivot_e << endl;
	  currentTransformationSequence->cost += postrouteEdge_noJAE (er, angelLCG_copy, ourAwarenessLevel);
	} // end post-routing
      } // end rerouting

      // check whether we've beaten our CURRENT best
      if (num_nontrivial_edges (angelLCG_copy, ourAwarenessLevel) < currentTransformationSequence->bestNumNontrivialEdges) {
        currentTransformationSequence->bestNumNontrivialEdges = num_nontrivial_edges (angelLCG_copy, ourAwarenessLevel);
        currentTransformationSequence->costAtBestEdgecount = currentTransformationSequence->cost;
        currentTransformationSequence->lastDesiredTransformation = currentTransformationSequence->transformationVector.size();
#ifndef NDEBUG
        cout << "** new best_num_edges for currentTransformationSequence: " << currentTransformationSequence->bestNumNontrivialEdges << endl;
#endif
      }

      elimNum++;
    } // end of elimination sequence

    bool notFinishedYet = currentTransformationSequence->revealedNewDependence;

#ifndef NDEBUG
    cout << "complete elim sequence complete.  This sequence achieved " << currentTransformationSequence->bestNumNontrivialEdges << " edges and ";
    if (currentTransformationSequence->revealedNewDependence) cout << "DID"; else cout << "DID NOT";
    cout << " add new dependence information to the dependence map" << endl;
#endif
     
    // check whether we've beaten our OVERALL best
    if (currentTransformationSequence->bestNumNontrivialEdges < bestTransformationSequence->bestNumNontrivialEdges
    // also prefer MATCHING best_num_edges with fewer operations
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
  cout << endl << "*************************************************************************************" << endl; 
  cout << "Now performing the best partial sequence of transformations..." << endl;
  cout << "*************************************************************************************" << endl; 
#endif

  // Perform the best transformation sequence
  unsigned int cost_of_elim_seq = 0;
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

    // check whether we've reached our goal
    if (num_nontrivial_edges (angelLCG, ourAwarenessLevel) == bestTransformationSequence->bestNumNontrivialEdges) break;
  } // end iterate through 

#ifndef NDEBUG
    cout << "Goal of " << bestTransformationSequence->bestNumNontrivialEdges << " reached" << endl;
#endif

  delete bestTransformationSequence; 

/* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
 * BUILD REMAINDER LCG AND CORRELATION LISTS FROM REDUCED ANGEL GRAPH
 * ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */

  remainderLCG.clear();

  // copy and correlate vertices
  v_cor_list.resize(0);
  c_graph_t::vi_t vi, v_end;
  for (tie (vi, v_end) = vertices (angelLCG); vi != v_end; ++vi) {
    // since vertices aren't removed from angelLCG, only copy non-isolated vertices
    if (in_degree (*vi, angelLCG) != 0 || out_degree (*vi, angelLCG) != 0) {
      LinearizedComputationalGraphVertex& new_rvert = remainderLCG.addVertex();
      // add a new correlation entry to the list
      VertexCorrelationEntry new_rvert_cor;
      new_rvert_cor.myOriginalVertex_p = ourLCG_verts[*vi];
      new_rvert_cor.myRemainderVertex_p = &new_rvert;
      v_cor_list.push_back(new_rvert_cor);
    }
  } // end all vertices

  // copy and correlate edges
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
    if(new_remainder_edge_ref_t == LCG_EDGE) {
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

  cout << "compute_partial_elimination_sequence: cost " << cost_of_elim_seq << endl;
} // end compute_partial_elimination_sequence()

 /* 	END DIRECT ELIMINATION
 * #####################################################################################################################################
 * #####################################################################################################################################
 */

void compute_elimination_sequence (const LinearizedComputationalGraph& xgraph,
				   JacobianAccumulationExpressionList& elist) {
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

  write_graph_xaif_booster (ac, av, ae, elist);
} // end of angel::compute_elimination_sequence()

void compute_elimination_sequence_lsa_face (const LinearizedComputationalGraph& xgraph,
					    int iterations, 
					    double gamma,
					    JacobianAccumulationExpressionList& expression_list) {
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

  write_graph_xaif_booster (ac, av, ae, expression_list);

} // end of angel::compute_elimination_sequence_lsa_face()

void compute_elimination_sequence_lsa_vertex (const LinearizedComputationalGraph& xgraph,
					      int iterations, 
					      double gamma,
					      JacobianAccumulationExpressionList& expression_list) {
  c_graph_t                                            cg;
  vector<const LinearizedComputationalGraphVertex*>    av;
  vector<edge_address_t>                               ae;
  read_graph_xaif_booster (xgraph, cg, av, ae);

  // Check if vertex elimination works
  for (size_t i= 0; i != cg.dependents.size(); i++)
    // version 1
    if (out_degree (cg.dependents[i], cg) > 0) {
      cerr << "Warning! Vertex elimination not possible with these graph.\n"
	   << "Call LSA for face elimination with same parameters (may take longer).\n";
      return compute_elimination_sequence_lsa_face (xgraph, iterations, gamma, expression_list);}
    // version 2
    // throw_exception (out_degree (cg.dependents[i], cg) > 0, consistency_exception, 
    //                  "Vertex elimination not possible with these graph.");
      
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

  write_graph_xaif_booster (ac, av, ae, expression_list);

} // end of angel::compute_elimination_sequence_lsa_vertex()

} // end namespace angel

namespace xaifBoosterCrossCountryInterface {

void xaifBoosterCrossCountryInterface::Elimination::eliminate() {

  try {
    if (myType == REGULAR_ELIMTYPE) {
      compute_elimination_sequence (getLCG(),
				    getEliminationResult().myJAEList);
    }
    else if (myType == LSA_VERTEX_ELIMTYPE) {
      compute_elimination_sequence_lsa_vertex (getLCG(),
					       getNumIterations(),
					       getGamma(),
					       getEliminationResult().myJAEList);
    }
    else if (myType == LSA_FACE_ELIMTYPE) {
      compute_elimination_sequence_lsa_face (getLCG(),
					     getNumIterations(),
					     getGamma(),
					     getEliminationResult().myJAEList);
    }
    else if (myType == SCARCE_ELIMTYPE) {
      compute_partial_elimination_sequence (getLCG(),
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






