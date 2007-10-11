#ifdef USEXAIFBOOSTER

#include "reroutings.hpp"

using namespace std;
using namespace boost;
using namespace xaifBoosterCrossCountryInterface;

namespace angel {

void reroutable_edges (const c_graph_t& angelLCG,
                       vector<edge_reroute_t>& erv) {
#ifndef NDEBUG
  cout << "------Determining all possible reroutings------" << endl;
#endif
  
  erv.clear();
  set<c_graph_t::vertex_t> downset, upset;
  c_graph_t::ei_t ei, e_end;
  c_graph_t::iei_t iei, ie_end;
  c_graph_t::oei_t oei, oe_end;

  for (tie (ei, e_end) = edges (angelLCG); ei != e_end; ++ei) {
    c_graph_t::edge_t e = *ei;

#ifndef NDEBUG
    cout << "checking edge " << e << "...";
#endif

    // check for preroutability
    if (in_degree (target (e, angelLCG), angelLCG) > 1) {
      vertex_downset (source (e, angelLCG), angelLCG, downset);

      // iterate over possible pivots (inedges of tgt(e))
      for (tie (iei, ie_end) = in_edges (target (*ei, angelLCG), angelLCG); iei != ie_end; ++iei) {
	c_graph_t::edge_t pivot_e = *iei;

	// skip the edge we're considering for rerouting
	if (source (pivot_e, angelLCG) == source (e, angelLCG)) continue;

	// the source of the pivot edge can't be an independent (we add an edge into it)
	if (in_degree (source (pivot_e, angelLCG), angelLCG) == 0) continue;

	// ensure that src(pivot) isn't in the downset of src(e) (would create cycle)
	vertex_set_t::const_iterator downset_i = downset.find(source (pivot_e, angelLCG));
	if (downset_i != downset.end()) {
#ifndef NDEBUG
	  cout << "can't reroute " << e << " about pivot edge " << pivot_e << " because " << source (pivot_e, angelLCG) << " is in the downset of " << source (e, angelLCG) << endl;
#endif
	  continue;
	}

#ifndef NDEBUG
	cout << " -> viable prerouting about pivot edge " << pivot_e;
#endif
	erv.push_back (edge_reroute_t (e, pivot_e, true));

      } // end all pivot candidates
    } // end if possible pivots exist

    // check for postroutability
    if (out_degree (source (e, angelLCG), angelLCG) > 1) {
      vertex_upset (target (e, angelLCG), angelLCG, upset);

      // iterate over possible pivots (outedges of src(e))
      for (tie (oei, oe_end) = out_edges (source (e, angelLCG), angelLCG); oei != oe_end; ++oei) {
	c_graph_t::edge_t pivot_e = *oei;

	// skip the edge we're considering for rerouting
	if (target (pivot_e, angelLCG) == target (e, angelLCG)) continue;

	// tgt(pivot_e) can't be a dependent vertex (we add an edge out of it)
	if (out_degree (target (pivot_e, angelLCG), angelLCG) == 0) continue;

	// ensure that tgt(pivot_e) isn't in the upset of tgt(e) (would create cycle)
	vertex_set_t::const_iterator upset_i = upset.find(target (pivot_e, angelLCG));
	if (upset_i != upset.end()) {
#ifndef NDEBUG
	  cout << "can't reroute " << e << " about pivot edge " << pivot_e << " because " << source (pivot_e, angelLCG) << " is in the downset of " << source (e, angelLCG) << endl;
#endif
	}
	else {
#ifndef NDEBUG
	  cout << " -> viable postrouting about pivot edge " << pivot_e;
#endif
	  erv.push_back (edge_reroute_t (e, pivot_e, false));
	}
      } // end all pivot candidates
    } // end if possible pivots exist

#ifndef NDEBUG
  cout << endl;
#endif
    
  } // end all edges in angelLCG

#ifndef NDEBUG
  cout << endl;
#endif

} // end reroutable_edges()

unsigned int edge_reducing_reroutings (vector<edge_reroute_t>& erv1,
				       const c_graph_t& angelLCG,
				       const Elimination::AwarenessLevel_E ourAwarenessLevel,
				       const bool allowMaintainingFlag,
				       vector<edge_reroute_t>& erv2) {
  erv2.clear();
  c_graph_t::oei_t oei, oe_end;
  c_graph_t::iei_t iei, ie_end;
  c_graph_t::edge_t find_e;
  bool found_e;
  int fill;

  boost::property_map<c_graph_t, EdgeType>::const_type eType = get(EdgeType(), angelLCG);

  for (size_t i = 0; i < erv1.size(); i++) {

    // Unit awareness: we must remove a nonunit edge to have a net DECREASE in overall nonunit edges
    if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[erv1[i].e] == UNIT_EDGE) continue;
    // Constant awareness: we must remove a variable edge to have a net DECREASE in overall nonunit edges
    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[erv1[i].e] != VARIABLE_EDGE) continue;

    // fill starts at -1 because we know we are removing a nontrivial edge
    fill = -1;

    // because e is nontrivial, any fill created will be nontrivial
    if (erv1[i].isPre) { // pre-routing
      // test for increment edge fill-in
      tie (find_e, found_e) = edge (source (erv1[i].e, angelLCG), source (erv1[i].pivot_e, angelLCG), angelLCG);
      if (!found_e) fill++;
      else { // detect situation where trivial edge becomes nontrivial
	// Unit awareness: absorbed edge will not be unit, because we add to it.  detect found_e: unit -> nonunit
	if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[find_e] == UNIT_EDGE) fill++;
	// Constant awareness: absorbed edge will be variable, because e is variable.  detect found_e: nonvariable -> variable
	else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[erv1[i].e] != VARIABLE_EDGE) fill++;
      }

      // test for decrement edge fill-in
      for (tie (oei, oe_end) = out_edges (source (erv1[i].pivot_e, angelLCG), angelLCG); oei != oe_end; ++oei) {
	// skip the pivot edge
	if (target (*oei, angelLCG) == target (erv1[i].pivot_e, angelLCG)) continue;
	tie (find_e, found_e) = edge (source (erv1[i].e, angelLCG), target (*oei, angelLCG), angelLCG);
	if (!found_e) fill++;
	else { // detect situation where trivial edge becomes nontrivial
	  // Unit awareness: absorbed edge will not be unit, because we add to it.  detect found_e: unit -> nonunit
	  if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[find_e] == UNIT_EDGE) fill++;
	  // Constant awareness: absorbed edge will be variable, because e is variable.  detect found_e: nonvariable -> variable
	  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[erv1[i].e] != VARIABLE_EDGE) fill++;
	}
      }
    }
    else { // post-routing
      // test for increment edge fill-in
      tie (find_e, found_e) = edge (target (erv1[i].pivot_e, angelLCG), target (erv1[i].e, angelLCG), angelLCG);
      if (!found_e) fill++;
      else { // detect situation where trivial edge becomes nontrivial
	// Unit awareness: absorbed edge will not be unit, because we add to it.  detect found_e: unit -> nonunit
	if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[find_e] == UNIT_EDGE) fill++;
	// Constant awareness: absorbed edge will be variable, because e is variable.  detect found_e: nonvariable -> variable
	else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[erv1[i].e] != VARIABLE_EDGE) fill++;
      }

      // test for decrement edge fill-in
      for (tie (iei, ie_end) = in_edges (target (erv1[i].pivot_e, angelLCG), angelLCG); iei != ie_end; ++iei) {
	// skip the pivot edge
	if (source (*iei, angelLCG) == source (erv1[i].pivot_e, angelLCG)) continue;
	tie (find_e, found_e) = edge (source (*iei, angelLCG), target (erv1[i].e, angelLCG), angelLCG);
	if (!found_e) fill++;
	else { // detect situation where trivial edge becomes nontrivial
	  // Unit awareness: absorbed edge will not be unit, because we add to it.  detect found_e: unit -> nonunit
	  if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[find_e] == UNIT_EDGE) fill++;
	  // Constant awareness: absorbed edge will be variable, because e is variable.  detect found_e: nonvariable -> variable
	  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[erv1[i].e] != VARIABLE_EDGE) fill++;
	}
      }
    } // end post-routing

    if (fill == -1) erv2.push_back(erv1[i]);

  } // end iterate over erv1
  return erv2.size();
} // end nonunit_edge_reducing_reroutings()

unsigned int edge_reducing_rerouteElims (vector<edge_reroute_t>& erv1,
					 const c_graph_t& angelLCG,
					 const Elimination::AwarenessLevel_E ourAwarenessLevel,
					 const bool allowMaintainingFlag,
					 vector<edge_reroute_t>& erv2) {
  erv2.clear();
  if (erv1.empty()) return 0;
  boost::property_map<c_graph_t, EdgeType>::const_type eType = get(EdgeType(), angelLCG);

  c_graph_t::iei_t iei, ie_end;
  c_graph_t::oei_t oei, oe_end;
  c_graph_t::edge_t absorb_e, increment_absorb_e;
  bool found_absorb_e, found_increment_absorb_e;
  int nontrivialEdgeChange;

  for (size_t i = 0; i < erv1.size(); i++) {
    c_graph_t::edge_t e = erv1[i].e;
    c_graph_t::edge_t pe = erv1[i].pivot_e;
    nontrivialEdgeChange = 0;
	  
    // consider the loss of the rerouted edge
    if (ourAwarenessLevel == Elimination::NO_AWARENESS) nontrivialEdgeChange--;
    else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[e] != UNIT_EDGE) nontrivialEdgeChange--;
    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[e] == VARIABLE_EDGE) nontrivialEdgeChange--;

    if (erv1[i].isPre) { // pre-routing
#ifndef NDEBUG
      std::cout << "considering prerouting of edge " << e << " about pivot edge " << pe
	        << ", followed by back-elimination of edge (" << source (e, angelLCG) << "," << source (pe, angelLCG) << ")" << endl;
#endif
      // cant be followed by elimination if src(e) is independent
      if (in_degree (source (e, angelLCG), angelLCG) == 0) continue;
	    
      // decrement edges:
      for (tie (oei, oe_end) = out_edges (source(pe, angelLCG), angelLCG); oei != oe_end; ++oei) {
	if (*oei == pe) continue; // skip the pivot edge
	tie (absorb_e, found_absorb_e) = edge (source (e, angelLCG), target (*oei, angelLCG), angelLCG);
#ifndef NDEBUG
	std::cout << "     considering decrement edge (" << source (e, angelLCG) << "," << target (e, angelLCG) << ")" << endl;
#endif
	if (found_absorb_e) { //absorption: count when we go from trivial to non-trivial
	  if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[absorb_e] == UNIT_EDGE) nontrivialEdgeChange++;
	  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[absorb_e] != VARIABLE_EDGE)
	    if (eType[e] == VARIABLE_EDGE || eType[pe] == VARIABLE_EDGE || eType[*oei] == VARIABLE_EDGE) nontrivialEdgeChange++;
	}
	else break; // decrement fill-in has been found (not allowed)
      } // end all outedges of src(pivot_e)
      if (oei != oe_end) continue; // we move on to the next consideration if there's decrement fill-in

      // increment edge: change occurs only when a increment edge was nontrivial to begin with
      tie (increment_absorb_e, found_increment_absorb_e) = edge (source (e, angelLCG), source (pe, angelLCG), angelLCG);
      if (found_increment_absorb_e) { // increment absorption
	if (ourAwarenessLevel == Elimination::NO_AWARENESS) nontrivialEdgeChange--;
	else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[increment_absorb_e] != UNIT_EDGE) nontrivialEdgeChange--;
	else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[increment_absorb_e] == VARIABLE_EDGE) nontrivialEdgeChange--;
      }

      // examine effect of back-eliminating increment edge
      for (tie (iei, ie_end) = in_edges (source(e, angelLCG), angelLCG); iei != ie_end; ++iei) {
	tie (absorb_e, found_absorb_e) = edge (source (*iei, angelLCG), source (pe, angelLCG), angelLCG);
	if (found_absorb_e) { // absorption: count when the absorb_e goes from trivial to nontrivial
	  if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[absorb_e] == UNIT_EDGE)
	    nontrivialEdgeChange++;
	  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[absorb_e] != VARIABLE_EDGE)
	    if ((found_increment_absorb_e && eType[increment_absorb_e] == VARIABLE_EDGE)
		|| eType[*iei] == VARIABLE_EDGE
		|| eType[e] == VARIABLE_EDGE
		|| eType[pe] == VARIABLE_EDGE)
	      nontrivialEdgeChange++;
	} // end absorption
	else { // fill-in: is the fill-in trivial or not?
	  if (ourAwarenessLevel == Elimination::NO_AWARENESS)
	    nontrivialEdgeChange++;
	  else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS)
	    if (found_increment_absorb_e || eType[*iei] != UNIT_EDGE || eType[e] != UNIT_EDGE || eType[pe] != UNIT_EDGE)
	      nontrivialEdgeChange++;
	  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS)
	    if ((found_increment_absorb_e && eType[increment_absorb_e] == VARIABLE_EDGE)
		|| eType[*iei] == VARIABLE_EDGE
		|| eType[e] == VARIABLE_EDGE
		|| eType[pe] == VARIABLE_EDGE)
	      nontrivialEdgeChange++;
	} // end fill-in
      } // end all preds of src(e)
    } // end pre-routing followed by back-elimination of increment

    else { //post-routing
#ifndef NDEBUG
      std::cout << "considering postrouting of edge " << e << " about pivot edge " << pe
	        << ", followed by front-elimination of edge (" << target (pe, angelLCG) << "," << target (e, angelLCG) << ")" << endl;
#endif
      // cant be followed by elimination if target(e) is dependent
      if (out_degree (target (e, angelLCG), angelLCG) == 0) continue;
	    
      // decrement edges:
      for (tie (iei, ie_end) = in_edges (target (pe, angelLCG), angelLCG); iei != ie_end; ++iei) {
	if (*iei == pe) continue; // skip the pivot edge
	tie (absorb_e, found_absorb_e) = edge (source (*iei, angelLCG), target (e, angelLCG), angelLCG);
#ifndef NDEBUG
	std::cout << "     considering decrement edge (" << source (*iei, angelLCG) << "," << target (e, angelLCG) << ")" << endl;
#endif
	if (found_absorb_e) { //absorption: count when we go from trivial to non-trivial
	  if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[absorb_e] == UNIT_EDGE) nontrivialEdgeChange++;
	  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[absorb_e] != VARIABLE_EDGE)
	    if (eType[e] == VARIABLE_EDGE || eType[pe] == VARIABLE_EDGE || eType[*iei] == VARIABLE_EDGE) nontrivialEdgeChange++;
	}
	else break; // decrement fill-in has been found (not allowed)
      } // end all outedges of src(pivot_e)
      if (iei != ie_end) continue; // we move on to the next consideration if there's decrement fill-in

      // increment edge: change occurs only when a increment edge was nontrivial to begin with
      tie (increment_absorb_e, found_increment_absorb_e) = edge (target (pe, angelLCG), target (e, angelLCG), angelLCG);
      if (found_increment_absorb_e) { // increment absorption
	if (ourAwarenessLevel == Elimination::NO_AWARENESS) nontrivialEdgeChange--;
	else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[increment_absorb_e] != UNIT_EDGE) nontrivialEdgeChange--;
	else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[increment_absorb_e] == VARIABLE_EDGE) nontrivialEdgeChange--;
      }

      // examine effect of front-eliminating increment edge
      for (tie (oei, oe_end) = out_edges (target (e, angelLCG), angelLCG); oei != oe_end; ++oei) {
	tie (absorb_e, found_absorb_e) = edge (target (pe, angelLCG), target (*oei, angelLCG), angelLCG);
	if (found_absorb_e) { // absorption: count when the absorb_e goes from trivial to nontrivial
	  if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[absorb_e] == UNIT_EDGE)
	    nontrivialEdgeChange++;
	  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[absorb_e] != VARIABLE_EDGE)
	    if ((found_increment_absorb_e && eType[increment_absorb_e] == VARIABLE_EDGE)
		|| eType[*oei] == VARIABLE_EDGE
		|| eType[e] == VARIABLE_EDGE
		|| eType[pe] == VARIABLE_EDGE)
	      nontrivialEdgeChange++;
	} // end absorption
	else { // fill-in: is the fill-in trivial or not?
	  if (ourAwarenessLevel == Elimination::NO_AWARENESS)
	    nontrivialEdgeChange++;
	  else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS)
	    if (found_increment_absorb_e || eType[*oei] != UNIT_EDGE || eType[e] != UNIT_EDGE || eType[pe] != UNIT_EDGE)
	      nontrivialEdgeChange++;
	  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS)
	    if ((found_increment_absorb_e && eType[increment_absorb_e] == VARIABLE_EDGE)
		|| eType[*oei] == VARIABLE_EDGE
		|| eType[e] == VARIABLE_EDGE
		|| eType[pe] == VARIABLE_EDGE)
	      nontrivialEdgeChange++;
	} // end fill-in
      } // end all preds of src(e)
    } // end post-routing followed by front-elimination of increment
    
    if (nontrivialEdgeChange < 0) erv2.push_back(erv1[i]);
    else if (allowMaintainingFlag && nontrivialEdgeChange == 0) erv2.push_back(erv1[i]);

  } // end iterate through erv1
  
  return erv2.size();
} // end nonunit_edge_reducing_reroutings()

unsigned int perform_quotient_decrement_directly (c_graph_t::edge_t prerouted_e,
						  c_graph_t::edge_t pivot_e,
						  c_graph_t::vertex_t tgt,
						  c_graph_t& angelLCG,
						  const Elimination::AwarenessLevel_E ourAwarenessLevel,
						  list<EdgeRef_t>& edge_ref_list,
						  JacobianAccumulationExpressionList& jae_list) {
  unsigned int cost = 0;
  return cost;
} // end perform_quotient_decrement_directly()

// pre-/post-routing an edge cannot isolate a vertex
unsigned int preroute_edge_directly (edge_reroute_t er,
				     c_graph_t& angelLCG,
				     const Elimination::AwarenessLevel_E ourAwarenessLevel,
				     list<EdgeRef_t>& edge_ref_list,
				     list< std::pair<unsigned int,unsigned int> >& refillCheck,
				     JacobianAccumulationExpressionList& jae_list) {
  unsigned int cost = 0;
  vector<c_graph_t::edge_t> v_succ;
  boost::property_map<c_graph_t, EdgeType>::type eType = get(EdgeType(), angelLCG);
  c_graph_t::iei_t iei, ie_end; 
  c_graph_t::oei_t oei, oe_end; 

  refillCheck.push_back(std::pair<unsigned int,unsigned int>(source (er.e, angelLCG), target (er.e,angelLCG)));

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

    //set edge type for absorption increment edge
    if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE)	eType[increment_e] = VARIABLE_EDGE;
    else if (eType[increment_e] != VARIABLE_EDGE)				eType[increment_e] = CONSTANT_EDGE;
  }
  else { //no increment edge was already present (fill-in)
    tie (increment_e, found_increment_e) = add_edge (source (er.e, angelLCG), source (er.pivot_e, angelLCG), angelLCG.next_edge_number++, angelLCG);
    // point the new edge at the divide operation in the new JAE
    EdgeRef_t new_increment_e_ref (increment_e, &jaev_divide);
    edge_ref_list.push_back(new_increment_e_ref);

    //set edge type for fill-in increment edge
    if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE)	eType[increment_e] = VARIABLE_EDGE;
    else if (eType[er.e] == UNIT_EDGE && eType[er.pivot_e] == UNIT_EDGE)	eType[increment_e] = UNIT_EDGE;
    else									eType[increment_e] = CONSTANT_EDGE;

    // check whether we're causing refill
    for (std::list< std::pair<unsigned int,unsigned int> >::const_iterator re_i = refillCheck.begin(); re_i != refillCheck.end(); re_i++)
      if (source (er.e, angelLCG) == re_i->first && source (er.pivot_e, angelLCG) == re_i->second)
	cout << "!!!!!! refill of edge (" << re_i->first << "," << re_i->second << ") !!!!!" << endl;
  }

  if (ourAwarenessLevel == Elimination::NO_AWARENESS)
    cost++;
  else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && (eType[er.e] != UNIT_EDGE || eType[er.pivot_e] != UNIT_EDGE))
    cost++;
  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE))
    cost++;

  // Perform decrement operations
  // ---------------------------------------------------------------------------

  // for all successors of v (except the target of e), perform decrement operations on edges from src_of_e to 
  for (tie (oei, oe_end) = out_edges (source (er.pivot_e, angelLCG), angelLCG); oei != oe_end; oei++) {
    //perform_quotient_decrement_directly (e, pivot_e, target (*oei, angelLCG), angelLCG, edge_ref_list, jae_list);
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

      //set edge type for absorption decrement edge
      if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE || eType[*oei] == VARIABLE_EDGE)
	eType[decrement_e] = VARIABLE_EDGE;
      else if (eType[decrement_e] != VARIABLE_EDGE)
	eType[decrement_e] = CONSTANT_EDGE;
    }
    else { // fill-in decrement edge
      tie (decrement_e, found_decrement_e) = add_edge (source (er.e, angelLCG), target (*oei, angelLCG), angelLCG.next_edge_number++, angelLCG);

      // point the new edge at the divide operation in the new JAE
      EdgeRef_t new_decrement_e_ref (decrement_e, &jaev_divide);
      edge_ref_list.push_back(new_decrement_e_ref);

      //set edge type for fill-in decrement edge
      if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE || eType[*oei] == VARIABLE_EDGE)
	eType[decrement_e] = VARIABLE_EDGE;
      else if (eType[er.e] == UNIT_EDGE && eType[er.pivot_e] == UNIT_EDGE && eType[*oei] == UNIT_EDGE)
	eType[decrement_e] = UNIT_EDGE;
      else
	eType[decrement_e] = CONSTANT_EDGE;
    }

    if (ourAwarenessLevel == Elimination::NO_AWARENESS)
      cost++;
    else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && (eType[er.e] != UNIT_EDGE || eType[er.pivot_e] != UNIT_EDGE || eType[*oei] != UNIT_EDGE))
      cost++;
    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE|| eType[*oei] == VARIABLE_EDGE))
      cost++;

  } // end all decrements

  remove_edge (er.e, angelLCG);
  
  return cost;
} // end preroute_edge_directly()

unsigned int postroute_edge_directly (edge_reroute_t er,
				     c_graph_t& angelLCG,
				     const Elimination::AwarenessLevel_E ourAwarenessLevel,
				     list<EdgeRef_t>& edge_ref_list,
				     list< std::pair<unsigned int,unsigned int> >& refillCheck,
				     JacobianAccumulationExpressionList& jae_list) {
  unsigned int cost = 1;
  boost::property_map<c_graph_t, EdgeType>::type eType = get(EdgeType(), angelLCG);
  c_graph_t::iei_t iei, ie_end; 
  c_graph_t::oei_t oei, oe_end; 

  refillCheck.push_back(std::pair<unsigned int,unsigned int>(source (er.e, angelLCG), target (er.e,angelLCG)));

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

    //set edge type for absorption increment edge
    if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE)	eType[increment_e] = VARIABLE_EDGE;
    else if (eType[increment_e] != VARIABLE_EDGE)				eType[increment_e] = CONSTANT_EDGE;

  }
  else { //no increment edge was already present (fill-in)
    // point the new edge at the divide operation in the new JAE
    tie (increment_e, found_increment_e) = add_edge (target (er.pivot_e, angelLCG), target (er.e, angelLCG), angelLCG.next_edge_number++, angelLCG);
    EdgeRef_t new_increment_e_ref (increment_e, &jaev_divide);
    edge_ref_list.push_back(new_increment_e_ref);

    //set edge type for fill-in increment edge
    if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE)	eType[increment_e] = VARIABLE_EDGE;
    else if (eType[er.e] == UNIT_EDGE && eType[er.pivot_e] == UNIT_EDGE)	eType[increment_e] = UNIT_EDGE;
    else									eType[increment_e] = CONSTANT_EDGE;

    // check whether we're causing refill
    for (std::list< std::pair<unsigned int,unsigned int> >::const_iterator re_i = refillCheck.begin(); re_i != refillCheck.end(); re_i++)
      if (target (er.pivot_e, angelLCG) == re_i->first && target (er.e, angelLCG) == re_i->second)
	cout << "!!!!!! refill of edge (" << re_i->first << "," << re_i->second << ") !!!!!" << endl;
  }

  if (ourAwarenessLevel == Elimination::NO_AWARENESS)
    cost++;
  else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && (eType[er.e] != UNIT_EDGE || eType[er.pivot_e] != UNIT_EDGE))
    cost++;
  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE))
    cost++;

  // for all predecessors of tgt(pivot_e) (except src(e)), perform decrement operations on edges to tgt(e) 
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

      //set edge type for absorption decrement edge
      if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE || eType[*iei] == VARIABLE_EDGE)
	eType[decrement_e] = VARIABLE_EDGE;
      else if (eType[decrement_e] != VARIABLE_EDGE)
	eType[decrement_e] = CONSTANT_EDGE;
    }
    else { // fill-in
      // point the new edge at the divide operation in the new JAE
      tie (decrement_e, found_decrement_e) = add_edge (source (*iei, angelLCG), target (er.e, angelLCG), angelLCG.next_edge_number++, angelLCG);
      EdgeRef_t new_decrement_e_ref (decrement_e, &jaev_divide);
      edge_ref_list.push_back(new_decrement_e_ref);

      //set edge type for fill-in decrement edge
      if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE || eType[*iei] == VARIABLE_EDGE)
	eType[decrement_e] = VARIABLE_EDGE;
      else if (eType[er.e] == UNIT_EDGE && eType[er.pivot_e] == UNIT_EDGE && eType[*iei] == UNIT_EDGE)
	eType[decrement_e] = UNIT_EDGE;
      else
	eType[decrement_e] = CONSTANT_EDGE;
    }

    if (ourAwarenessLevel == Elimination::NO_AWARENESS)
      cost++;
    else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && (eType[er.e] != UNIT_EDGE || eType[er.pivot_e] != UNIT_EDGE || eType[*iei] != UNIT_EDGE))
      cost++;
    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE|| eType[*iei] == VARIABLE_EDGE))
      cost++;
  } // end all decrements

  remove_edge (er.e, angelLCG);

  return cost;
} // end postroute_edge_directly()

} // namespace angel

#endif // USEXAIFBOOSTER

