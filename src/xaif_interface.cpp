// $Id: xaif_interface.cpp,v 1.13 2004/05/19 14:15:49 gottschling Exp $

#ifdef USEXAIFBOOSTER

#include "xaif_interface.hpp"
#include "eliminations.hpp"
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
}

void build_remainder_graph (const c_graph_t& cgp,
			    const vector<const LinearizedComputationalGraphVertex*> av,
			    LinearizedComputationalGraph& rg,
			    VertexCorrelationList& v_cor_list,
			    EdgeCorrelationList& e_cor_list){ 
  rg.clear();
  v_cor_list.resize(0);
  e_cor_list.resize(0);

  // copy (non-isolated) vertices
  c_graph_t::vi_t vi, v_end;
  for (tie(vi, v_end) = vertices(cgp); vi != v_end; ++vi) {
    if (in_degree(*vi, cgp) > 0 || out_degree(*vi, cgp) > 0) {

#ifndef NDEBUG
      cout << "adding vertex " << *vi << " to the remainder graph\n";
#endif

      LinearizedComputationalGraphVertex& rvert = rg.addVertex();
      VertexCorrelationEntry rvert_cor;
      rvert_cor.myOriginalVertex_p = av[*vi];
      rvert_cor.myRemainderVertex_p = &rvert;
      v_cor_list.push_back(rvert_cor);
    }

#ifndef NDEBUG
    else cout << "vertex " << *vi << " is isolated, it is not added to the remainder graph\n";
#endif

  } // end all vertices

  // copy edges
  c_graph_t::ei_t ei, e_end;
  for (tie(ei, e_end) = edges(cgp); ei != e_end; ++ei) {
    const LinearizedComputationalGraphVertex* o_src_p = av[source(*ei, cgp)];
    const LinearizedComputationalGraphVertex* o_tgt_p = av[target(*ei, cgp)];
    LinearizedComputationalGraphVertex* r_src_p = NULL;
    LinearizedComputationalGraphVertex* r_tgt_p = NULL;

    // correlate source and target with vertices in the remainder graph
    for (VertexCorrelationList::iterator vcori = v_cor_list.begin(); vcori != v_cor_list.end(); vcori++) {
      if (vcori->myOriginalVertex_p == o_src_p) r_src_p = vcori->myRemainderVertex_p;
      else if (vcori->myOriginalVertex_p == o_tgt_p) r_tgt_p = vcori->myRemainderVertex_p;
    } // end all vertex correlation entries
    throw_debug_exception (r_src_p == NULL || r_tgt_p == NULL, consistency_exception,
				"Vertex in remainder graph could not be correlated"); 

#ifndef NDEBUG
    cout << "Adding edge from " << source(*ei, cgp) << " to " << target(*ei, cgp) << " in remainder graph\n";
#endif

    LinearizedComputationalGraphEdge& redge = rg.addEdge(*r_src_p, *r_tgt_p);
    EdgeCorrelationEntry redge_cor_ent;
    redge_cor_ent.myRemainderGraphEdge_p = &redge;
    e_cor_list.push_back(redge_cor_ent);
  } // end all edges
} // end build_remainder_graph()
}

using namespace angel;

namespace xaifBoosterCrossCountryInterface {

void compute_partial_elimination_sequence (const LinearizedComputationalGraph& ourLCG,
					   int tasks,
					   double, // for interface unification
					   JacobianAccumulationExpressionList& jae_list,
					   LinearizedComputationalGraph& remainderLCG,
					   VertexCorrelationList& v_cor_list,
					   EdgeCorrelationList& e_cor_list) {
  try { 
  c_graph_t angelLCG;
  vector<edge_address_t> ourLCG_edges;
  vector<edge_bool_t> bev1, bev2, bev3, bev4;
  vector<edge_ij_elim_t> eij_elim_seq;
  //vector<edge_ij_elim_t> ev1, ev2, eij_elim_seq;

//**************************************************************************************************
// READ GRAPH

  vector<const LinearizedComputationalGraphVertex*> ourLCG_verts;
  int nv = ourLCG.numVertices ();

  // Add pointers to independent vertices to ourLCG_verts
  const LinearizedComputationalGraph::VertexPointerList& indeps_list = ourLCG.getIndependentList ();
  LinearizedComputationalGraph::VertexPointerList::const_iterator bi = indeps_list.begin(), be = indeps_list.end();
  for (; bi != be; bi++)
    ourLCG_verts.push_back (*bi);

  // remaining are sorted topologically
  LinearizedComputationalGraph::ConstVertexIteratorPair vip (ourLCG.vertices());
  while ((int) ourLCG_verts.size() < nv) {
    LinearizedComputationalGraph::ConstVertexIterator vi (vip.first), v_end (vip.second);
    for (; vi != v_end; ++vi) {
      if (which_index (&*vi, ourLCG_verts) != ourLCG_verts.size()) continue;
      LinearizedComputationalGraph::ConstInEdgeIteratorPair inedges (ourLCG.getInEdgesOf (*vi));
      LinearizedComputationalGraph::ConstInEdgeIterator ie = inedges.first, iend = inedges.second;
      bool all_num = true; // all predecessors numbered
      for (; ie != iend; ++ie)
        if (which_index (&(ourLCG.getSourceOf (*ie)), ourLCG_verts) == ourLCG_verts.size()) {
	  all_num = false; break;
	}
      if (all_num) ourLCG_verts.push_back (&*vi);
    } // end all vertices
  }

  // populate vector of independent vertices
  vector<c_graph_t::vertex_t> indeps;
  for (bi = indeps_list.begin(); bi != be; bi++)
    indeps.push_back (which_index (*bi, ourLCG_verts));

  // ensure that indeps occur in the beginning
  for (size_t c= 0; c < indeps.size(); c++)
    throw_exception (indeps[c] >= indeps.size(), consistency_exception, "Independent not at the beginning");

  // populate vector of dependent vertices
  vector<c_graph_t::vertex_t> deps;
  const LinearizedComputationalGraph::VertexPointerList&  deps_list = ourLCG.getDependentList ();
  bi = deps_list.begin(), be = deps_list.end();
  for (; bi != be; bi++) deps.push_back (which_index (*bi, ourLCG_verts)); 

  // copy edges
  list<EdgeRef_t> edge_ref_list;
  int edge_number = 0;
  boost::property_map<c_graph_t, EdgeIsUnitType>::type eisunit = get(EdgeIsUnitType(), angelLCG);
  LinearizedComputationalGraph::ConstEdgeIteratorPair eip (ourLCG.edges());
  for (LinearizedComputationalGraph::ConstEdgeIterator ei (eip.first), e_end (eip.second); ei != e_end; ++ei) {

    c_graph_t::vertex_t source = which_index (& (ourLCG.getSourceOf (*ei)), ourLCG_verts),
			target = which_index (& (ourLCG.getTargetOf (*ei)), ourLCG_verts);
    pair<c_graph_t::edge_t, bool> new_edge = add_edge (source, target, edge_number++, angelLCG);
    ourLCG_edges.push_back (edge_address_t(source, target, &*ei));
    (*ei).hasUnitLabel() ? eisunit[new_edge.first] = true
			 : eisunit[new_edge.first] = false;

    //if(eisunit[new_edge.first]) cout << "is_unit label in angel graph seems to be labeled\n";

    //add referece that points the new angel edge to the corresponding LCG edge
    EdgeRef_t new_edge_ref (new_edge.first, &*ei);
    edge_ref_list.push_back(new_edge_ref);
    //new_ref.my_angelLCG_edge_p = &new_edge.first;
    //new_ref.my_type = LCG_EDGE;
    //new_ref.my_ref_p.my_LCG_edge_p = &*ei;

  } // end for all LCG edges

  angelLCG.X = int (indeps.size());
  angelLCG.dependents = deps;

// END READ GRAPH
//****************************************************************************************************************
//
#ifndef NDEBUG
  write_graph ("angelLCG (constructed from ourLCG): ", angelLCG);
  cout << "\n###############################################################################"
       << "\n####################################### Performing partial edge elimination sequence on angelLCG_copy...\n";
#endif

  c_graph_t angelLCG_copy (angelLCG); // a partial edge elimination sequence will be performed on angelGcopy
  unsigned int cost_of_elim_seq = 0;

  eliminatable_objects (angelLCG_copy, bev1);
  scarce_pres_edge_eliminations (bev1, angelLCG_copy, bev2);
  lowest_markowitz_edge (bev2, angelLCG_copy, bev3);
  reverse_mode_edge (bev3, angelLCG_copy, bev4);
  while(!bev4.empty()) {
    //edge_ij_elim_t elim (source (bev4[0].first, angelLCG_copy), target (bev4[0].first, angelLCG_copy), bev4[0].second);
    //eij_elim_seq.push_back(elim);
    //eij_elim_seq.push_back(ev2[0];

    cout << "of " << bev1.size() << " edge elimination objects, " << bev2.size() << " are scarcity preserving\n";
    if (bev4[0].second) {
      cout << "Front-eliminating edge " << bev4[0].first << "...\n";
      cost_of_elim_seq += front_eliminate_edge_directly (bev4[0].first, angelLCG_copy, edge_ref_list, jae_list);
    }
    else {
      cout << "Back-eliminating edge " << bev4[0].first << "...\n";
      cost_of_elim_seq += back_eliminate_edge_directly (bev4[0].first, angelLCG_copy, edge_ref_list, jae_list);
    }

    eliminatable_objects (angelLCG_copy, bev1);
    scarce_pres_edge_eliminations (bev1, angelLCG_copy, bev2);
    lowest_markowitz_edge (bev2, angelLCG_copy, bev3);
    reverse_mode_edge (bev3, angelLCG_copy, bev4);
  }

#ifndef NDEBUG
  write_graph ("angelLCGcopy after partial edge elimination sequence (G prime): ", angelLCG_copy);
  cout << "\n###############################################################################"
       << "\n####################################### Building remainderLCG from angelLCGcopy...\n";
#endif


/* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
 * BUILD REMAINDER LCG AND CORRELATION LISTS FROM REDUCED ANGEL GRAPH
 * ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */
  remainderLCG.clear();

  // copy and correlate vertices (only non-isolated ones)
  v_cor_list.resize(0);
  c_graph_t::vi_t vi, v_end;
  for (tie (vi, v_end) = vertices (angelLCG_copy); vi != v_end; ++vi) {
    if (in_degree (*vi, angelLCG_copy) > 0 || out_degree (*vi, angelLCG_copy) > 0) {
      LinearizedComputationalGraphVertex& new_rvert = remainderLCG.addVertex();
      VertexCorrelationEntry new_rvert_cor;
      new_rvert_cor.myOriginalVertex_p = ourLCG_verts[*vi];
      new_rvert_cor.myRemainderVertex_p = &new_rvert;
      v_cor_list.push_back(new_rvert_cor);
    } // end if non-isolated
  } // end all vertices

  // copy and correlate edges
  e_cor_list.resize(0);
  c_graph_t::ei_t ei, e_end;
  for (tie(ei, e_end) = edges(angelLCG_copy); ei != e_end; ++ei) {
    const LinearizedComputationalGraphVertex* original_src_p = ourLCG_verts[source(*ei, angelLCG_copy)];
    const LinearizedComputationalGraphVertex* original_tgt_p = ourLCG_verts[target(*ei, angelLCG_copy)];
    LinearizedComputationalGraphVertex* remainder_src_p = NULL;
    LinearizedComputationalGraphVertex* remainder_tgt_p = NULL;

    // Find source and target in remainder LCG
    for (VertexCorrelationList::iterator vcori = v_cor_list.begin(); vcori != v_cor_list.end(); vcori++) {
      if (vcori->myOriginalVertex_p == original_src_p) remainder_src_p = vcori->myRemainderVertex_p;
      else if (vcori->myOriginalVertex_p == original_tgt_p) remainder_tgt_p = vcori->myRemainderVertex_p;
    } // end all vertex correlation entries
    throw_exception (remainder_src_p == NULL || remainder_tgt_p == NULL, consistency_exception,
					"Vertex in remainder graph could not be correlated");

    // create the edge and its correlation entry
    LinearizedComputationalGraphEdge& new_redge = remainderLCG.addEdge(*remainder_src_p, *remainder_tgt_p);
    EdgeCorrelationEntry new_redge_cor;
    new_redge_cor.myRemainderGraphEdge_p = &new_redge;

    // derive contents of correlation entry from the internal edge reference list
    EdgeRefType_E new_remainder_edge_ref_t = getRefType (*ei, angelLCG_copy, edge_ref_list);
    throw_exception (new_remainder_edge_ref_t == UNDEFINED, consistency_exception, "Edge reference is UNDEFINED");
    if(new_remainder_edge_ref_t == LCG_EDGE) {
      new_redge_cor.myEliminationReference.myOriginalEdge_p = getLCG_p (*ei, angelLCG_copy, edge_ref_list);
      new_redge_cor.myType = EdgeCorrelationEntry::LCG_EDGE;
    }
    else if (new_remainder_edge_ref_t == JAE_VERT) {
      new_redge_cor.myEliminationReference.myJAEVertex_p = getJAE_p (*ei, angelLCG, edge_ref_list);
      new_redge_cor.myType = EdgeCorrelationEntry::JAE_VERT;
    }
    e_cor_list.push_back(new_redge_cor);
  } // end all edges

/* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
 * ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */

  cout << "compute_partial_elimination_sequence: cost " << cost_of_elim_seq << endl;
  }
  }
  catch (base_exception e) { 
    throw EliminationException(std::string("angel exception caught within compute_partial_elimination_sequence : ")+e.what_reason());
  }
}

/* #####################################################################################################################################
 * #####################################################################################################################################
 * 		END DIRECT ELIMINATION
 */

void compute_elimination_sequence (const LinearizedComputationalGraph& xgraph,
				   int task,
				   double, // for interface unification
				   JacobianAccumulationExpressionList& elist) {
  try { 
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
  }
  catch (base_exception e) { 
    throw EliminationException(std::string("angel exception caught within compute_elimination_sequence : ")+e.what_reason());
  }
}

void compute_elimination_sequence_lsa_face (const LinearizedComputationalGraph& xgraph,
					    int iterations, 
					    double gamma,
					    JacobianAccumulationExpressionList& expression_list) {
  try { 
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
  }
  catch (base_exception e) { 
    throw EliminationException(std::string("angel exception caught within compute_elimination_sequence_lsa_face : ")+e.what_reason());
  }

}

void compute_elimination_sequence_lsa_vertex (const LinearizedComputationalGraph& xgraph,
					      int iterations, 
					      double gamma,
					      JacobianAccumulationExpressionList& expression_list) {
  try { 
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
  }
  catch (base_exception e) { 
    throw EliminationException(std::string("angel exception caught within compute_elimination_sequence_lsa_vertex : ")+e.what_reason());
  }

}

}



#endif // USEXAIFBOOSTER






