// $Id: xaif_interface.cpp,v 1.13 2004/05/19 14:15:49 gottschling Exp $

#ifdef USEXAIFBOOSTER

#include "xaif_interface.hpp"
#include "eliminations.hpp"
#include "reroutings.hpp"
#include "heuristics.hpp"

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
  boost::property_map<c_graph_t, EdgeIsUnitType>::type eisunit = get(EdgeIsUnitType(), cg);
  xgraph_t::ConstEdgeIteratorPair eip (xg.edges());
  for (xgraph_t::ConstEdgeIterator ei (eip.first), e_end (eip.second); ei != e_end; ++ei) {
    vertex_t source= which_index (& (xg.getSourceOf (*ei)), av),
             target= which_index (& (xg.getTargetOf (*ei)), av);
    pair<c_graph_t::edge_t, bool> new_edge = add_edge (source, target, edge_number++, cg);
    ae.push_back (edge_address_t(source, target, &*ei));
    (*ei).hasUnitLabel() ? eisunit[new_edge.first] = true
			 : eisunit[new_edge.first] = false;

    //if(eisunit[new_edge.first]) cout << "is_unit label in angel graph seems to be labeled\n";
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

} // end namespace angel

using namespace angel;

namespace xaifBoosterCrossCountryInterface {

void compute_partial_elimination_sequence (const LinearizedComputationalGraph& ourLCG,
					   int tasks,
					   double, // for interface unification
					   JacobianAccumulationExpressionList& jae_list,
					   LinearizedComputationalGraph& remainderLCG,
					   VertexCorrelationList& v_cor_list,
					   EdgeCorrelationList& e_cor_list) {
//**************************************************************************************************
// Process LCG from xaifBooster into an angel c_graph_t

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
  boost::property_map<c_graph_t, EdgeIsUnitType>::type eisunit = get(EdgeIsUnitType(), angelLCG);
  LinearizedComputationalGraph::ConstEdgeIteratorPair eip (ourLCG.edges());
  for (LinearizedComputationalGraph::ConstEdgeIterator ei (eip.first), e_end (eip.second); ei != e_end; ++ei) {
    // locate source and target of edge in angelLCG
    c_graph_t::vertex_t source = which_index (& (ourLCG.getSourceOf (*ei)), ourLCG_verts);
    c_graph_t::vertex_t	target = which_index (& (ourLCG.getTargetOf (*ei)), ourLCG_verts);
    pair<c_graph_t::edge_t, bool> new_edge = add_edge (source, target, edge_number++, angelLCG);
    (*ei).hasUnitLabel() ? eisunit[new_edge.first] = true
			 : eisunit[new_edge.first] = false;
    //if (eisunit[new_edge.first]) cout << "is_unit label in angel graph seems to be labeled\n";
    EdgeRef_t new_edge_ref (new_edge.first, &*ei);
    edge_ref_list.push_back(new_edge_ref);
  } // end for all LCG edges

// END READ GRAPH
//****************************************************************************************************************
//
#ifndef NDEBUG
  write_graph ("angelLCG (constructed from ourLCG): ", angelLCG);
  cout << "\n###############################################################################"
       << "\n####################################### Performing partial edge elimination sequence on angelLCG...\n";
#endif

  vector<edge_bool_t> bev1, bev2, bev3, bev4;
  unsigned int cost_of_elim_seq = 0;

  eliminatable_objects (angelLCG, bev1);
  scarce_pres_edge_eliminations (bev1, angelLCG, bev2);
  lowest_markowitz_edge (bev2, angelLCG, bev3);
  reverse_mode_edge (bev3, angelLCG, bev4);
  cout << "of " << bev1.size() << " edge elimination objects, " << bev2.size() << " are scarcity preserving.  ";

  while(!bev4.empty()) {
    c_graph_t::edge_t e = bev3[0].first;
    bool isFront = bev3[0].second;

    if (isFront) cout << "Front-eliminating edge " << e << "..." << endl;
    else cout << "Back-eliminating edge " << e << "..." << endl;

    cost_of_elim_seq += isFront ? front_eliminate_edge_directly (e, angelLCG, edge_ref_list, jae_list)
				: back_eliminate_edge_directly (e, angelLCG, edge_ref_list, jae_list);

    eliminatable_objects (angelLCG, bev1);
    scarce_pres_edge_eliminations (bev1, angelLCG, bev2);
    lowest_markowitz_edge (bev2, angelLCG, bev3);
    reverse_mode_edge (bev3, angelLCG, bev4);
    cout << "of " << bev1.size() << " edge elimination objects, " << bev2.size() << " are scarcity preserving.  ";
  }
  cout << "\n********* No more scarcity-preserving edge eliminations remain.  Now Performing edge reroutings..." << endl;

  vector<edge_reroute_t> erv1, erv2, erv3;
  reroutable_edges (angelLCG, erv1);
  edge_reducing_reroutings (erv1, angelLCG, erv2);
  edge_reducing_rerouteElims (erv1, angelLCG, erv3);
  cout << "of " << erv1.size() << " possible edge reroutings, " << erv2.size() << " reduce the edge count "
       << "and " << erv3.size() << " reduce the edge count when followed by an edge elimination" << endl;

  while (!erv2.empty() || !erv3.empty()) {
    if (!erv2.empty()) { // an edge count reducing edge elimination can be performed
      if (erv2[0].isPre) cout << "pre"; else cout << "post";
      cout << "routing edge " << erv2[0].e << " about pivot edge " << erv2[0].pivot_e << "..." << endl;

      cost_of_elim_seq += erv2[0].isPre ? preroute_edge_directly (erv2[0], angelLCG, edge_ref_list, jae_list)
					: postroute_edge_directly (erv2[0], angelLCG, edge_ref_list, jae_list);
    }
    else { //rerouting followed by edge elim
      c_graph_t::edge_t increment_e;
      bool found_increment_e;

      if (erv3[0].isPre) {
	cout << "prerouting edge " << erv3[0].e << " about pivot edge " << erv3[0].pivot_e << endl;
	cout << "followed by back elimination of edge (" << source (erv3[0].e, angelLCG) << ","
							 << source (erv3[0].pivot_e, angelLCG) << ")" << endl;

	cost_of_elim_seq += preroute_edge_directly (erv3[0], angelLCG, edge_ref_list, jae_list);
	tie (increment_e, found_increment_e) = edge (source (erv3[0].e, angelLCG), source (erv3[0].pivot_e, angelLCG), angelLCG);
	throw_exception (!found_increment_e, consistency_exception, "increment edge could not be found for front elimination");
	back_eliminate_edge_directly (increment_e, angelLCG, edge_ref_list, jae_list);
      }
      else {
	cout << "postrouting edge " << erv3[0].e << " about pivot edge " << erv3[0].pivot_e << "...";
	cout << "followed by front elimination of edge (" << target (erv3[0].pivot_e, angelLCG) << ","
							  << target (erv3[0].e, angelLCG) << ")" << endl;
	cost_of_elim_seq += postroute_edge_directly (erv3[0], angelLCG, edge_ref_list, jae_list);
	tie (increment_e, found_increment_e) = edge (target (erv3[0].pivot_e, angelLCG), target (erv3[0].e, angelLCG), angelLCG);
	throw_exception (!found_increment_e, consistency_exception, "increment edge could not be found for front elimination");
	cout << "Now performing the front-elimination of " << increment_e << "..." << endl;
	front_eliminate_edge_directly (increment_e, angelLCG, edge_ref_list, jae_list);
      }
    }

    reroutable_edges (angelLCG, erv1);
    edge_reducing_reroutings (erv1, angelLCG, erv2);
    edge_reducing_rerouteElims (erv1, angelLCG, erv3);
    cout << "of " << erv1.size() << " possible edge reroutings, " << erv2.size() << " reduce the edge count "
         << "and " << erv3.size() << " reduce the edge count when followed by an edge elimination" << endl;
  }

  cout << "No more scarcity-preserving edge reroutings remain.  Now building the remainder graph..." << endl;

#ifndef NDEBUG
  write_graph ("angelLCG after partial edge elimination sequence (G prime): ", angelLCG);
#endif

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
}

 /* 	END DIRECT ELIMINATION
 * #####################################################################################################################################
 * #####################################################################################################################################
 */

void compute_elimination_sequence (const LinearizedComputationalGraph& xgraph,
				   int task,
				   double, // for interface unification
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
					     getEliminationResult().myJaeList);
    }
    else if (myType == SCARCE_ELIMTYPE) {
      compute_partial_elimination_sequence (getLCG(),
					    getEliminationResult().myJAEList,
					    getEliminationResult().myRemainderLCG,
					    getEliminationResult().myVertexCorList,
					    getEliminationResult().myEdgeCorList);
    }
    else throw_exception (true, consistency_exception, "Missing or invalid elimination type");
  }
  catch (base_exception e) { 
    throw EliminationException(std::string("angel exception caught within Elimination::eliminate() : ")+e.what_reason());
  }

} // end of Elimination::eliminate()

} // end namespace xaifBoosterCrossCountryInterface



#endif // USEXAIFBOOSTER






