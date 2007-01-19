// $Id: xaif_interface.cpp,v 1.13 2004/05/19 14:15:49 gottschling Exp $

#ifdef USE_XAIF

#include "xaif_interface.hpp"
#include "eliminations.hpp"
#include "heuristics.hpp"

#include "angel_io.hpp"
#include "sa.hpp"

#include "xaifBooster/system/inc/GraphVizDisplay.hpp"

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
  xgraph_t::ConstEdgeIteratorPair eip (xg.edges());
  for (xgraph_t::ConstEdgeIterator ei (eip.first), e_end (eip.second); ei != e_end; ++ei) {
    vertex_t source= which_index (& (xg.getSourceOf (*ei)), av),
             target= which_index (& (xg.getTargetOf (*ei)), av);
    add_edge (source, target, edge_number++, cg);
    ae.push_back (edge_address_t(source, target, &*ei)); }


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

void build_jae_list_and_correlate_rg (const accu_graph_t& ag,
				      const vector<const LinearizedComputationalGraphVertex*>& av,
				      const vector<edge_address_t>& ae,
				      JacobianAccumulationExpressionList& jae_list,
				      LinearizedComputationalGraph& rg,
				      VertexCorrelationList& v_cor_list,
				      EdgeCorrelationList& e_cor_list) {

  typedef LinearizedComputationalGraphVertex      xlvertex_t;
  typedef JacobianAccumulationExpressionVertex    xavertex_t;
  
  // build Jacobian Accumulation Expressions one at a time
  vector<xavertex_t*> exp_output_pr; // pointer to output vertex of expression
  for (size_t c= 0; c < ag.accu_exp.size(); c++) {
    const accu_exp_graph_t& my_exp= ag.accu_exp[c];
    property_map<pure_accu_exp_graph_t, vertex_name_t>::const_type vpr = get(vertex_name, my_exp);

    JacobianAccumulationExpression& new_exp= jae_list.addExpression();
    vector<xavertex_t*>  vp (my_exp.v());
    // for all vertices in my_exp
    for (size_t vc= 0; vc < (size_t) my_exp.v(); vc++) {      
      const accu_exp_t& prop= vpr[vc];

      // create a new JAE vertex
      xavertex_t& new_vertex= new_exp.addVertex();
      vp[vc]= &new_vertex;

      // if it's the last vertex, save its address in exp_output_pr
      if (vc+1 == (size_t) my_exp.v()) exp_output_pr.push_back(&new_vertex);

      // set reference (for leaves) or set operation (non-leaves)
      switch (prop.ref_kind) { 
	case accu_exp_t::nothing:
	  throw_exception (true, consistency_exception, "Unset vertex"); break;
	case accu_exp_t::exp:    
	  throw_debug_exception (prop.ref.exp_nr >= int (c), consistency_exception, "Expression number too large")
	  new_vertex.setInternalReference (*exp_output_pr[prop.ref.exp_nr]); break;
	case accu_exp_t::lgn: {    
	  const LinearizedComputationalGraphEdge* ptr= xaif_edge_pr (prop.ref.node, ag, ae); 
	  throw_debug_exception (ptr == NULL, consistency_exception, "Unset reference");
	  new_vertex.setExternalReference (*ptr); } break;
	case accu_exp_t::isop:    
	  new_vertex.setOperation (prop.ref.op == accu_exp_t::add ? xavertex_t::ADD_OP : xavertex_t::MULT_OP);
      } // switch ref_kind

    } // for all vertices in expression
    
    // add edges to new Jacobian Accumulation Expression
    graph_traits<pure_accu_exp_graph_t>::edge_iterator ei, e_end;   // set edges
    for (tie (ei, e_end)= edges (my_exp); ei != e_end; ei++)
      new_exp.addEdge(*vp[source (*ei, my_exp)], *vp[target (*ei, my_exp)]);

  } // for all expressions
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
      rvert_cor.lcgVert = av[*vi];
      rvert_cor.rv = &rvert;
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
      if (vcori->lcgVert == o_src_p) r_src_p = vcori->rv;
      else if (vcori->lcgVert == o_tgt_p) r_tgt_p = vcori->rv;
    } // end all vertex correlation entries
    throw_debug_exception (r_src_p == NULL || r_tgt_p == NULL, consistency_exception,
				"Vertex in remainder graph could not be correlated"); 

#ifndef NDEBUG
    cout << "Adding edge from " << source(*ei, cgp) << " to " << target(*ei, cgp) << " in remainder graph\n";
#endif

    LinearizedComputationalGraphEdge& redge = rg.addEdge(*r_src_p, *r_tgt_p);
    EdgeCorrelationEntry redge_cor_ent;
    redge_cor_ent.re = &redge;
    e_cor_list.push_back(redge_cor_ent);
  } // end all edges
} // end build_remainder_graph()

void compute_partial_elimination_sequence (const LinearizedComputationalGraph& xgraph,
					   int tasks,
					   double, // for interface unification
					   JacobianAccumulationExpressionList& jae_list,
					   LinearizedComputationalGraph& rg,
					   VertexCorrelationList& v_cor_list,
                                           EdgeCorrelationList& e_cor_list) {
  c_graph_t cg;
  vector<const LinearizedComputationalGraphVertex*> av;
  vector<edge_address_t> ae;
  vector<edge_bool_t> bev1, bev2;
  vector<edge_ij_elim_t> eseq;
  //vector<edge_ij_elim_t> ev1, ev2, eseq;
  int cost = 0;

#ifndef NDEBUG
  cout << "\nBuilding cg, the internal LCG...\n";
#endif

  read_graph_xaif_booster (xgraph, cg, av, ae);

#ifndef NDEBUG
  write_graph ("cg ", cg);
  cout << "\nPerforming partial edge elimination sequence on cgp (copy of cg)...\n";
#endif

  c_graph_t cgp (cg); // a partial elimination sequence will reduce cgp to "cg prime"
  eliminatable_objects (cgp, bev1);
  scarce_pres_edge_eliminations (bev1, cgp, bev2);

  while(!bev2.empty()) {
    edge_ij_elim_t elim (target (bev2[0].first, cgp), source (bev2[0].first, cgp), bev2[0].second);
    eseq.push_back(elim);
    //eseq.push_back(ev2[0];

#ifndef NDEBUG
    cout << "of " << bev1.size() << " edge elimination objects, " << bev2.size() << " are scarcity preserving\n";
    if (bev2[0].second) { cout << "Front-eliminating edge from " << elim.j << " to " << elim.i << "...\n"; }
    else { cout << "Back-eliminating edge from " << elim.j << " to " << elim.i << "...\n"; }
#endif

    cost += eliminate (bev2[0], cgp);
    eliminatable_objects (cgp, bev1);
    scarce_pres_edge_eliminations (bev1, cgp, bev2);
  }
 
  //cgp.clear_graph(); // clears isolated intermediate vertices (and also renumbers vertices!)

#ifndef NDEBUG
  write_graph ("cgp ", cgp);
  cout << "\nBuilding remainder graph rg...\n";
#endif

  build_remainder_graph(cgp, av, rg, v_cor_list, e_cor_list);

#ifndef NDEBUG
  cout << "\nConverting edge elimination sequence in cg into face elimination sequence in lg...\n";
#endif

  // transform the partial elimination sequence into a sequence of face eliminations
  line_graph_t lg (cg);
  vector<triplet_t> tv;
  convert_elimination_sequence (eseq, lg, tv);

#ifndef NDEBUG
  write_vector("Same elimination sequence as face eliminations", tv);  
  cout << "\nPerforming face elimination seq. on lg and generating accumulation graph...\n";
#endif

  // build accumulation graph
  accu_graph_t ac (cg, lg);
  for (size_t c= 0; c < tv.size(); c++) 
    face_elimination (tv[c], lg, ac);

#ifndef NDEBUG
  write_graph ("Empty line graph", lg);
  line_graph_t::evn_t            evn= get(vertex_name, lg);
  write_vertex_property (cout, "vertices of this edge graph", evn, lg);
  
  for (size_t c= 0; c < ac.accu_exp.size(); c++) {
    write_graph ("Accumulation graph", ac.accu_exp[c]);
    property_map<pure_accu_exp_graph_t, vertex_name_t>::type vprop= 
      get (vertex_name, ac.accu_exp[c]);
    write_vertex_property (cout, "Vertex props", vprop, ac.accu_exp[c]); 
    ad_edge_t my_jacobi= ac.jacobi_entries[c];
    if (my_jacobi.second == 0) cout << "isn't Jacobian entry\n";
    else cout << "is Jacoby entry: " << my_jacobi << std::endl; }
  cout << "\nBuilding JAE list...\n";
#endif

  build_jae_list_and_correlate_rg(ac, av, ae, jae_list, rg, v_cor_list, e_cor_list);

}

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
}

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
}

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
}

} // namespace angel



#endif // USE_XAIF






