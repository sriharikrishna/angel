#ifdef USEXAIFBOOSTER

#include "reroutings.hpp"

using namespace std;
using namespace boost;
using namespace xaifBoosterCrossCountryInterface;

namespace angel {

void vertex_upset (const c_graph_t::vertex_t v,
		   const c_graph_t& angelLCG,
		   list<c_graph_t::vertex_t>& upset) {
  upset.clear();
  if (out_degree (v, angelLCG) == 0)
    upset.push_back(v); // base case: v is a dependent vertex
  else {
    vector<c_graph_t::vertex_t> succs_vec;
    sorted_successor_set (v, angelLCG, succs_vec);
    for (size_t i = 0; i < succs_vec.size(); i++) {
      list<c_graph_t::vertex_t> upset_of_succ;
      vertex_upset (succs_vec[i], angelLCG, upset_of_succ); // <-- recursion call
      upset.merge(upset_of_succ); // merge this succ's upset into upset
    }
  }
} // end up_vertex_set()

void vertex_downset (const c_graph_t::vertex_t v,
		     const c_graph_t& angelLCG,
		     list<c_graph_t::vertex_t>& downset) {
  downset.clear();
  if (in_degree (v, angelLCG) == 0)
    downset.push_back(v); // base case: v is an independent vertex
  else {
    vector<c_graph_t::vertex_t> preds_vec;
    sorted_predecessor_set (v, angelLCG, preds_vec);
    for (size_t i = 0; i < preds_vec.size(); i++) {
      list<c_graph_t::vertex_t> downset_of_pred;
      vertex_downset (preds_vec[i], angelLCG, downset_of_pred); // <-- recursion call
      downset.merge(downset_of_pred); // merge this pred's downset into downset
    }
  }
} // end down_vertex_set()

void reroutable_edges (const c_graph_t& angelLCG,
                       vector<edge_reroute_t>& erv) {
  erv.clear();
  list<c_graph_t::vertex_t> downset, upset;
  c_graph_t::ei_t ei, e_end;
  c_graph_t::iei_t iei, ie_end;
  c_graph_t::oei_t oei, oe_end;
  list<c_graph_t::vertex_t>::iterator vli, vl_end;

  for (tie (ei, e_end) = edges (angelLCG); ei != e_end; ++ei) {

    // check for preroutability
#ifndef NDEBUG
    cout << endl << "checking edge " << *ei << " for preroutability...";
#endif
    if (in_degree (target (*ei, angelLCG), angelLCG) > 1) {
      vertex_downset (source (*ei, angelLCG), angelLCG, downset);
      // iterate over inedges of edges target (possible pivots)
      for (tie (iei, ie_end) = in_edges (target (*ei, angelLCG), angelLCG); iei != ie_end; ++iei) {
	// skip the edge we're considering
	if (source (*iei, angelLCG) == source (*ei, angelLCG)) continue;
	// the source of the pivot edge can't be an independent (we add an edge into it)
	if (in_degree (source (*iei, angelLCG), angelLCG) == 0) continue;
	// ensure that the source of the pivot isnt in the down set of the source of the edge (would create cycle)
	for (vli = downset.begin(); vli != downset.end(); vli++)
	  if (*vli == source (*iei, angelLCG)) break;
	if (vli == downset.end()) { // source(pivot) is not in the downset of source(ei)
#ifndef NDEBUG
	  cout << " -> viable prerouting with pivot edge " << *iei;
#endif
	  erv.push_back (edge_reroute_t (*ei, *iei, true));
	}
#ifndef NDEBUG
	else cout << " -> no viable prerouting" << endl;
#endif
      } // end all pivot candidates
    } // end if possible pivots exist

    // check for postroutability
#ifndef NDEBUG
    cout << endl << "checking edge " << *ei << " for postroutability...";
#endif
    if (out_degree (source (*ei, angelLCG), angelLCG) > 1) {
      vertex_upset (target (*ei, angelLCG), angelLCG, upset);
      // iterate over outedges of source(ei) (possible pivots)
      for (tie (oei, oe_end) = out_edges (source (*ei, angelLCG), angelLCG); oei != oe_end; ++oei) {
	// skip the edge we're considering for rerouting
	if (target (*oei, angelLCG) == target (*ei, angelLCG)) continue;
	// the target of the pivot edge cant be a dependent vertex (we add an edge out of it)
	if (out_degree (target (*oei, angelLCG), angelLCG) == 0) continue;
	// ensure that the target of the pivot isnt in the upset of target(ei) (would create cycle)
	for (vli = upset.begin(); vli != upset.end(); vli++)
	  if (*vli == target (*oei, angelLCG)) break;
	if (vli == upset.end()) { // target(pivot) is not in the upset of target(ei)
#ifndef NDEBUG
	  cout << " -> viable postrouting with pivot edge " << *oei;
#endif
	  erv.push_back (edge_reroute_t (*ei, *oei, false));
	}
#ifndef NDEBUG
	else { cout << " -> no viable postrouting" << endl; }
#endif
      } // end all pivot candidates
    } // end if possible pivots exist

  } // end all edges in angelLCG
} // end reroutable_edges()

void edge_reducing_reroutings (vector<edge_reroute_t>& erv1,
			       const c_graph_t& angelLCG,
			       vector<edge_reroute_t>& erv2) {
  erv2.clear();
  c_graph_t::oei_t oei, oe_end;
  c_graph_t::iei_t iei, ie_end;
  c_graph_t::edge_t find_e;
  bool found_e;
  int fill;

#ifdef IGNORE_TRIVIAL_ELIMINATIONS
  boost::property_map<c_graph_t, EdgeIsUnitType>::const_type eIsUnit = get(EdgeIsUnitType(), angelLCG);
#endif

  for (size_t i = 0; i < erv1.size(); i++) {

#ifdef IGNORE_TRIVIAL_ELIMINATIONS
    // we must remove a nonunit edge to have a net DECREASE in overall nonunit edges
    if (eIsUnit[erv1[i].e]) continue;
    // from here on we assume e is nonunit, thus all fill is nonunit
#endif

    fill = -1;

    if (erv1[i].isPre) { // pre-routing
      // test for increment edge fill-in
      tie (find_e, found_e) = edge (source (erv1[i].e, angelLCG), source (erv1[i].pivot_e, angelLCG), angelLCG);
      if (!found_e) fill++;

      // test for decrement edge fill-in
      for (tie (oei, oe_end) = out_edges (source (erv1[i].pivot_e, angelLCG), angelLCG); oei != oe_end; ++oei) {
	// skip the pivot edge
	if (target (*oei, angelLCG) == target (erv1[i].pivot_e, angelLCG)) continue;
	tie (find_e, found_e) = edge (source (erv1[i].e, angelLCG), target (*oei, angelLCG), angelLCG);
	if (!found_e) fill++;
      }
    }
    else { // post-routing
      // test for increment edge fill-in
      tie (find_e, found_e) = edge (target (erv1[i].pivot_e, angelLCG), target (erv1[i].e, angelLCG), angelLCG);
      if (!found_e) fill++;

      // test for decrement edge fill-in
      for (tie (iei, ie_end) = in_edges (target (erv1[i].pivot_e, angelLCG), angelLCG); iei != ie_end; ++iei) {
	// skip the pivot edge
	if (source (*iei, angelLCG) == source (erv1[i].pivot_e, angelLCG)) continue;
	tie (find_e, found_e) = edge (source (*iei, angelLCG), target (erv1[i].e, angelLCG), angelLCG);
	if (!found_e) fill++;
      }
    } // end post-routing

    if (fill == -1) erv2.push_back(erv1[i]);

  } // end iterate over erv1
} // end nonunit_edge_reducing_reroutings()

// In this filter, we select pre-routings that maintain the edge count and can be
// followed by an edge count-reducing back-elimination of the increment edge, and
// post-routings that maintain the edge count and can be followed by an edge count-
// reducing front-elimination of the increment edge.
void edge_reducing_rerouteElims (vector<edge_reroute_t>& erv1,
				 const c_graph_t& angelLCG,
				 vector<edge_reroute_t>& erv2) {
#ifdef IGNORE_TRIVIAL_ELIMINATIONS
  boost::property_map<c_graph_t, EdgeIsUnitType>::const_type eIsUnit = get(EdgeIsUnitType(), angelLCG);
#endif

  erv2.clear();
  c_graph_t::iei_t iei, ie_end;
  c_graph_t::oei_t oei, oe_end;
  c_graph_t::edge_t find_e;
  bool found_e;
  int fill;

#ifndef NDEBUG
    cout << endl;
#endif
  
  for (size_t i = 0; i < erv1.size(); i++) {


#ifdef IGNORE_TRIVIAL_ELIMINATIONS
    if (eIsUnit[erv1[i].e]) fill = 0;
    else fill = -1;
#else
    fill = -2;
#endif

    if (erv1[i].isPre) { // pre-routing
      c_graph_t::iei_t e_iei, e_ie_end, pe_iei, pe_ie_end;

      // In order for the subsequent back-elimination of the increment edge to be edge count-reducing,
      // the predecessors of src(e) must be a subset of the predecessors of src(pe)

      // for all predecessors of src(e)
      for (tie (e_iei, e_ie_end) = in_edges (source (erv1[i].e, angelLCG), angelLCG); e_iei != e_ie_end; ++e_iei) {
	// search through predecessors of src(pe) to find absorbing edge
	for (tie (pe_iei, pe_ie_end) = in_edges (source (erv1[i].pivot_e, angelLCG), angelLCG); pe_iei != pe_ie_end; ++pe_iei) {
	  if (source (*e_iei, angelLCG) == source (*pe_iei, angelLCG)) break;
	}
	if (pe_iei == pe_ie_end) break; // no absorbing edge was found
      }
      // if some pred of src(pe) is not also a pred of src(e)
      if (e_iei != e_ie_end) continue;

      // test for increment edge fill-in
      tie (find_e, found_e) = edge (source (erv1[i].e, angelLCG), source (erv1[i].pivot_e, angelLCG), angelLCG);
#ifdef IGNORE_TRIVIAL_ELIMINATIONS
      if (!found_e && (!eIsUnit[erv1[i].e] || !eIsUnit[erv1[i].pivot_e])) fill++;
#else
      if (!found_e) fill++;
#endif

      // test for decrement edge fill-in
      for (tie (oei, oe_end) = out_edges (source (erv1[i].pivot_e, angelLCG), angelLCG); oei != oe_end; ++oei) {
	// skip the pivot edge
	if (target (*oei, angelLCG) == target (erv1[i].pivot_e, angelLCG)) continue;
	tie (find_e, found_e) = edge (source (erv1[i].e, angelLCG), target (*oei, angelLCG), angelLCG);
#ifdef IGNORE_TRIVIAL_ELIMINATIONS
	if (!found_e && (!eIsUnit[erv1[i].e] || !eIsUnit[erv1[i].pivot_e] || !eIsUnit[*oei])) fill++;
#else
	if (!found_e) fill++;
#endif
      }
    } // end pre-routing

    else { // post-routing
      c_graph_t::oei_t e_oei, e_oe_end, pe_oei, pe_oe_end;

      // In order for the subsequent front-elimination of the increment edge to be edge count-reducing,
      // the successors of tgt(e) must be a subset of the successors of tgt(pe)

      // for each successor of tgt(e)
      for (tie (e_oei, e_oe_end) = out_edges (target (erv1[i].e, angelLCG), angelLCG); e_oei != e_oe_end; ++e_oei) {
	// check each successor of tgt(pe)
	for (tie (pe_oei, pe_oe_end) = out_edges (target (erv1[i].pivot_e, angelLCG), angelLCG); pe_oei != pe_oe_end; ++pe_oei) {
	  if (target(*pe_oei, angelLCG) == target(*e_oei, angelLCG)) break; // we have found the absorption edge
	}
	if (pe_oei == pe_oe_end) break; // no absorption edge could be found
      }
      if (e_oei != e_oe_end) continue; // an absorption edge couldnt be found each time

      // test for increment edge fill-in
      tie (find_e, found_e) = edge (target (erv1[i].pivot_e, angelLCG), target (erv1[i].e, angelLCG), angelLCG);
#ifdef IGNORE_TRIVIAL_ELIMINATIONS
      if (!found_e && (!eIsUnit[erv1[i].e] || !eIsUnit[erv1[i].pivot_e])) fill++;
#else
      if (!found_e) fill++;
#endif

      // test for decrement edge fill-in
      for (tie (iei, ie_end) = in_edges (target (erv1[i].pivot_e, angelLCG), angelLCG); iei != ie_end; ++iei) {
	// skip the pivot edge
	if (source (*iei, angelLCG) == source (erv1[i].pivot_e, angelLCG)) continue;
        tie (find_e, found_e) = edge (source (*iei, angelLCG), target (erv1[i].e, angelLCG), angelLCG);
#ifdef IGNORE_TRIVIAL_ELIMINATIONS
	if (!found_e && (!eIsUnit[erv1[i].e] || !eIsUnit[erv1[i].pivot_e] || !eIsUnit[*iei])) fill++;
#else
	if (!found_e) fill++;
#endif
      }
    } // end post-routing

    if (fill == -1) erv2.push_back(erv1[i]);

  } // end iterate over erv1
} // end nonunit_edge_reducing_reroutings()

void perform_quotient_decrement_directly (c_graph_t::edge_t prerouted_e,
					  c_graph_t::edge_t pivot_e,
					  c_graph_t::vertex_t tgt,
					  c_graph_t& angelLCG,
					  list<EdgeRef_t>& edge_ref_list,
					  JacobianAccumulationExpressionList& jae_list) {

} // end perform_quotient_decrement_directly()

// pre-/post-routing an edge cannot isolate a vertex
unsigned int preroute_edge_directly (edge_reroute_t er,
				     c_graph_t& angelLCG,
				     list<EdgeRef_t>& edge_ref_list,
				     JacobianAccumulationExpressionList& jae_list) {
  unsigned int cost = 0;
  vector<c_graph_t::edge_t> v_succ;
  boost::property_map<c_graph_t, EdgeIsUnitType>::type eIsUnit = get(EdgeIsUnitType(), angelLCG);
  c_graph_t::iei_t iei, ie_end; 
  c_graph_t::oei_t oei, oe_end; 

  // Increment the edge from the source of e to to v by the quotient e/pivot_e (create it if it doesnt exist)
  JacobianAccumulationExpression& new_jae = jae_list.addExpression();

  JacobianAccumulationExpressionVertex& jaev_divide = new_jae.addVertex();
  //jaev_divide.setOperation (JacobianAccumulationExpressionVertex::DIVIDE_OP);
  jaev_divide.setOperation (JacobianAccumulationExpressionVertex::ADD_OP);

  JacobianAccumulationExpressionVertex& jaev_e = new_jae.addVertex();
  JacobianAccumulationExpressionVertex& jaev_pivot_e = new_jae.addVertex();
  setJaevRef (er.e, jaev_e, angelLCG, edge_ref_list);
  setJaevRef (er.pivot_e, jaev_pivot_e, angelLCG, edge_ref_list);
  new_jae.addEdge(jaev_e, jaev_divide);
  new_jae.addEdge(jaev_pivot_e, jaev_divide);

  //test for absorption
  bool found_increment_e;
  c_graph_t::edge_t increment_e;
  tie (increment_e, found_increment_e) = edge (source (er.e, angelLCG), source (er.pivot_e, angelLCG), angelLCG);
  if (found_increment_e) { // increment absorption
    cout << "---> Increment_e from " << source (er.e, angelLCG) << " to " << source (er.pivot_e, angelLCG) << " already present (absorb)" << endl;

    JacobianAccumulationExpressionVertex& jaev_increment_e = new_jae.addVertex();
    setJaevRef (increment_e, jaev_increment_e, angelLCG, edge_ref_list);
    JacobianAccumulationExpressionVertex& jaev_add = new_jae.addVertex();
    jaev_add.setOperation (JacobianAccumulationExpressionVertex::ADD_OP);
    new_jae.addEdge(jaev_increment_e, jaev_add);
    new_jae.addEdge(jaev_divide, jaev_add);

    //point increment_e at the top of the new JAE
    removeRef (increment_e, angelLCG, edge_ref_list);
    EdgeRef_t new_increment_e_ref (increment_e, &jaev_add);
    edge_ref_list.push_back(new_increment_e_ref);
  }
  else { //no increment edge was already present (fill-in)
    cout << "++> Increment_e from " << source (er.e, angelLCG) << " to " << source (er.pivot_e, angelLCG) << " NOT present (fill-in)...";
    tie (increment_e, found_increment_e) = add_edge (source (er.e, angelLCG),
						     source (er.pivot_e, angelLCG),
						     angelLCG.next_edge_number++,
						     angelLCG);
    if (eIsUnit[er.e] && eIsUnit[er.pivot_e]) {
      cout << "both " << er.e << " and " << er.pivot_e << "are unit => new fill edge " << increment_e << " is unit\n";
      eIsUnit[increment_e] = true;
    }
    else {
      cout << "new fill edge " << increment_e << " is NOT a unit edge";
      eIsUnit[increment_e] = false;
    }

    // point the new edge at the divide operation in the new JAE
    EdgeRef_t new_increment_e_ref (increment_e, &jaev_divide);
    edge_ref_list.push_back(new_increment_e_ref);
  }

  // Perform decrement operations
  // ---------------------------------------------------------------------------

  // for all successors of v (except the target of e), perform decrement operations on edges from src_of_e to 
  for (tie (oei, oe_end) = out_edges (source (er.pivot_e, angelLCG), angelLCG); oei != oe_end; oei++) {
    if (target (*oei, angelLCG) == target (er.e, angelLCG)) continue;
    JacobianAccumulationExpression& new_jae = jae_list.addExpression();
 
    JacobianAccumulationExpressionVertex& jaev_divide = new_jae.addVertex();
    //jaev_divide.setOperation (JacobianAccumulationExpressionVertex::DIVIDE_OP);
    jaev_divide.setOperation (JacobianAccumulationExpressionVertex::ADD_OP);

    JacobianAccumulationExpressionVertex& jaev_e = new_jae.addVertex();
    JacobianAccumulationExpressionVertex& jaev_pivot_e = new_jae.addVertex();
    setJaevRef (er.e, jaev_e, angelLCG, edge_ref_list);
    setJaevRef (er.pivot_e, jaev_pivot_e, angelLCG, edge_ref_list);
    new_jae.addEdge(jaev_e, jaev_divide);
    new_jae.addEdge(jaev_pivot_e, jaev_divide);

    // create mult vertex and connect it up
    JacobianAccumulationExpressionVertex& jaev_mult = new_jae.addVertex();
    jaev_mult.setOperation (JacobianAccumulationExpressionVertex::MULT_OP);
    new_jae.addEdge(jaev_divide, jaev_mult);

    JacobianAccumulationExpressionVertex& jaev_vout_e = new_jae.addVertex();
    setJaevRef (*oei, jaev_vout_e, angelLCG, edge_ref_list);
    new_jae.addEdge(jaev_vout_e, jaev_mult);
    
    // check for absorption
    bool found_decrement_e;
    c_graph_t::edge_t decrement_e;
    tie (decrement_e, found_decrement_e) = edge (source (er.e, angelLCG), target (*oei, angelLCG), angelLCG);

    if (found_decrement_e) { // absorption
      cout << "--> Decrement_e from " << source (er.e, angelLCG) << " to " << target (*oei, angelLCG)  << " already present (absorption)" << endl;
      JacobianAccumulationExpressionVertex& jaev_decrement_e = new_jae.addVertex();
      JacobianAccumulationExpressionVertex& jaev_subtract = new_jae.addVertex();
      //jaev_subtract.setOperation (JacobianAccumulationExpressionVertex::SUBTRACT_OP);
      jaev_subtract.setOperation (JacobianAccumulationExpressionVertex::ADD_OP);
      new_jae.addEdge(jaev_mult, jaev_subtract);
      new_jae.addEdge(jaev_decrement_e, jaev_subtract);

      // point the decrement edge at the divide operation in the new JAE
      removeRef (decrement_e, angelLCG, edge_ref_list);
      EdgeRef_t new_decrement_e_ref (decrement_e, &jaev_subtract);
      edge_ref_list.push_back(new_decrement_e_ref);
    }
    else { // fill-in
      cout << "--> Decrement_e from " << source (er.e, angelLCG) << " to " << target (*oei, angelLCG)  << " NOT already present (fill-in)" << endl;
      tie (decrement_e, found_decrement_e) = add_edge (source (er.e, angelLCG), target (*oei, angelLCG), angelLCG.next_edge_number++, angelLCG);

      if (eIsUnit[er.e] && eIsUnit[er.pivot_e] && eIsUnit[*oei]) eIsUnit[decrement_e] = true;
      else eIsUnit[decrement_e] = false;

      // point the new edge at the divide operation in the new JAE
      EdgeRef_t new_decrement_e_ref (decrement_e, &jaev_divide);
      edge_ref_list.push_back(new_decrement_e_ref);
    }

    //perform_quotient_decrement_directly (e, pivot_e, target (*oei, angelLCG), angelLCG, edge_ref_list, jae_list);
    cost++;
  } // end all decrements

  cout << "removing edge " << er.e << " from angelLCG" << endl;
  remove_edge (er.e, angelLCG);
  
  return cost;
} // end preroute_edge_directly()

unsigned int postroute_edge_directly (edge_reroute_t er,
				     c_graph_t& angelLCG,
				     list<EdgeRef_t>& edge_ref_list,
				     JacobianAccumulationExpressionList& jae_list) {
  unsigned int cost = 1;
  boost::property_map<c_graph_t, EdgeIsUnitType>::type eIsUnit = get(EdgeIsUnitType(), angelLCG);
  c_graph_t::iei_t iei, ie_end; 
  c_graph_t::oei_t oei, oe_end; 

  // Increment the edge from the source of e to to v by the quotient e/pivot_e (create it if it doesnt exist)
  JacobianAccumulationExpression& new_jae = jae_list.addExpression();

  JacobianAccumulationExpressionVertex& jaev_divide = new_jae.addVertex();
  //jaev_divide.setOperation (JacobianAccumulationExpressionVertex::DIVIDE_OP);
  jaev_divide.setOperation (JacobianAccumulationExpressionVertex::ADD_OP);

  JacobianAccumulationExpressionVertex& jaev_e = new_jae.addVertex();
  JacobianAccumulationExpressionVertex& jaev_pivot_e = new_jae.addVertex();
  setJaevRef (er.e, jaev_e, angelLCG, edge_ref_list);
  setJaevRef (er.pivot_e, jaev_pivot_e, angelLCG, edge_ref_list);
  new_jae.addEdge(jaev_e, jaev_divide);
  new_jae.addEdge(jaev_pivot_e, jaev_divide);

  //test for absorption for the increment edge
  bool found_increment_e;
  c_graph_t::edge_t increment_e;
  tie (increment_e, found_increment_e) = edge (target (er.pivot_e, angelLCG), target (er.e, angelLCG), angelLCG);
  if (found_increment_e) {
    cout << "+++> Increment_e from " << target (er.pivot_e, angelLCG) << " to " << target (er.e, angelLCG) << " already present (absorption)" << endl;

    JacobianAccumulationExpressionVertex& jaev_increment_e = new_jae.addVertex();
    setJaevRef (increment_e, jaev_increment_e, angelLCG, edge_ref_list);
    JacobianAccumulationExpressionVertex& jaev_add = new_jae.addVertex();
    jaev_add.setOperation (JacobianAccumulationExpressionVertex::ADD_OP);
    new_jae.addEdge(jaev_increment_e, jaev_add);
    new_jae.addEdge(jaev_divide, jaev_add);

    //point increment_e at the top of the new JAE
    removeRef (increment_e, angelLCG, edge_ref_list);
    EdgeRef_t new_increment_e_ref (increment_e, &jaev_add);
    edge_ref_list.push_back(new_increment_e_ref);
  }
  else { //no increment edge was already present
    cout << "+++> Increment_e from " << target (er.pivot_e, angelLCG) << " to " << target (er.e, angelLCG) << " NOT already present (fill-in)...";
    tie (increment_e, found_increment_e) = add_edge (target (er.pivot_e, angelLCG),
						     target (er.e, angelLCG),
						     angelLCG.next_edge_number++,
						     angelLCG);
    if (eIsUnit[er.e] && eIsUnit[er.pivot_e]) {
      cout << "Both " << er.e << " and " << er.pivot_e << "are unit => new fill edge " << increment_e << " is unit" << endl;
      eIsUnit[increment_e] = true;
    }
    else {
      cout << "new fill edge " << increment_e << " is NOT a unit edge" << endl;
      eIsUnit[increment_e] = false;
    }

    // point the new edge at the divide operation in the new JAE
    EdgeRef_t new_increment_e_ref (increment_e, &jaev_divide);
    edge_ref_list.push_back(new_increment_e_ref);
  }

  // Perform decrement operations
  // ---------------------------------------------------------------------------

  // for all predecessors of tgt(pivot_e) (except src(e)),
  // perform decrement operations on edges to tgt(e) 
  for (tie (iei, ie_end) = in_edges (target (er.pivot_e, angelLCG), angelLCG); iei != ie_end; iei++) {
    if (source (*iei, angelLCG) == source (er.pivot_e, angelLCG)) continue;
    JacobianAccumulationExpression& new_jae = jae_list.addExpression();
 
    JacobianAccumulationExpressionVertex& jaev_divide = new_jae.addVertex();
    //jaev_divide.setOperation (JacobianAccumulationExpressionVertex::DIVIDE_OP);
    jaev_divide.setOperation (JacobianAccumulationExpressionVertex::ADD_OP);

    JacobianAccumulationExpressionVertex& jaev_e = new_jae.addVertex();
    JacobianAccumulationExpressionVertex& jaev_pivot_e = new_jae.addVertex();
    setJaevRef (er.e, jaev_e, angelLCG, edge_ref_list);
    setJaevRef (er.pivot_e, jaev_pivot_e, angelLCG, edge_ref_list);
    new_jae.addEdge(jaev_e, jaev_divide);
    new_jae.addEdge(jaev_pivot_e, jaev_divide);

    // create mult vertex and connect it up
    JacobianAccumulationExpressionVertex& jaev_mult = new_jae.addVertex();
    jaev_mult.setOperation (JacobianAccumulationExpressionVertex::MULT_OP);
    new_jae.addEdge(jaev_divide, jaev_mult);

    JacobianAccumulationExpressionVertex& jaev_vin_e = new_jae.addVertex();
    setJaevRef (*iei, jaev_vin_e, angelLCG, edge_ref_list);
    new_jae.addEdge(jaev_vin_e, jaev_mult);
    
    // check for absorption
    bool found_decrement_e;
    c_graph_t::edge_t decrement_e;
    tie (decrement_e, found_decrement_e) = edge (source (*iei, angelLCG), target (er.e, angelLCG), angelLCG);
    if (found_decrement_e) { // absorption
      cout << "--> Decrement_e from " << source (*iei, angelLCG) << " to " << target (er.e, angelLCG) << " already present (absorption)" << endl;
      JacobianAccumulationExpressionVertex& jaev_decrement_e = new_jae.addVertex();
      JacobianAccumulationExpressionVertex& jaev_subtract = new_jae.addVertex();
      //jaev_subtract.setOperation (JacobianAccumulationExpressionVertex::SUBTRACT_OP);
      jaev_subtract.setOperation (JacobianAccumulationExpressionVertex::ADD_OP);
      new_jae.addEdge(jaev_mult, jaev_subtract);
      new_jae.addEdge(jaev_decrement_e, jaev_subtract);

      // point the decrement edge at the divide operation in the new JAE
      removeRef (decrement_e, angelLCG, edge_ref_list);
      EdgeRef_t new_decrement_e_ref (decrement_e, &jaev_subtract);
      edge_ref_list.push_back(new_decrement_e_ref);
    }
    else { // fill-in
      cout << "--> Decrement_e from " << source (*iei, angelLCG) << " to " << target (er.e, angelLCG) << " NOT already present (fill-in)" << endl;
      tie (decrement_e, found_decrement_e) = add_edge (source (*iei, angelLCG), target (er.e, angelLCG), angelLCG.next_edge_number++, angelLCG);
      if (eIsUnit[er.e] && eIsUnit[er.pivot_e] && eIsUnit[*oei])
	eIsUnit[decrement_e] = true;
      else
	eIsUnit[decrement_e] = false;

      // point the new edge at the divide operation in the new JAE
      EdgeRef_t new_decrement_e_ref (decrement_e, &jaev_divide);
      edge_ref_list.push_back(new_decrement_e_ref);
    }
    cost++;
  } // end all decrements

  cout << "removing edge " << er.e << " from angelLCG" << endl;
  remove_edge (er.e, angelLCG);

  return cost;
} // end postroute_edge_directly()

} // namespace angel

#endif // USEXAIFBOOSTER

