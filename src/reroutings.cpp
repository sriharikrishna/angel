#ifdef USEXAIFBOOSTER

#include "reroutings.hpp"

using namespace std;
using namespace boost;
using namespace xaifBoosterCrossCountryInterface;

namespace angel {

void reroutable_edges (c_graph_t& angelLCG,
                       vector<edge_reroute_t>& erv) {
  erv.clear();
  set<c_graph_t::vertex_t> downset, upset;
  c_graph_t::edge_t decrement_e;
  bool found_decrement_e;
  c_graph_t::ei_t ei, e_end;
  c_graph_t::iei_t iei, ie_end;
  c_graph_t::oei_t oei, oe_end;
  property_map<pure_c_graph_t, VertexVisited>::type visited = get(VertexVisited(), angelLCG);
  c_graph_t::vi_t cleari, clear_end;

  // iterate over all edges; consider each to be pre-routed and post-routed
  for (tie (ei, e_end) = edges (angelLCG); ei != e_end; ++ei) {
    c_graph_t::edge_t e = *ei;
    //cout << "checking edge " << e << "..." << endl;

    // check for preroutability
    if (in_degree (target (e, angelLCG), angelLCG) > 1) {
      // iterate over possible pivots (inedges of tgt(e))
      for (tie (iei, ie_end) = in_edges (target (*ei, angelLCG), angelLCG); iei != ie_end; ++iei) {
	c_graph_t::edge_t pivot_e = *iei;
	// skip the edge we're considering for rerouting
	if (source (pivot_e, angelLCG) == source (e, angelLCG)) continue;
	// the source of the pivot edge can't be an independent (we add an edge into it)
	if (in_degree (source (pivot_e, angelLCG), angelLCG) == 0) continue;
	// ensure that no decrement fill-in is created
	for (tie(oei, oe_end) = out_edges(source(pivot_e, angelLCG), angelLCG); oei != oe_end; ++oei) {
	  if (*oei == pivot_e) continue; // skip the pivot edge
	  tie(decrement_e, found_decrement_e) = edge(source(e, angelLCG), target(*oei, angelLCG), angelLCG);
	  if (!found_decrement_e) break; // decrement fill-in has been found (not allowed)
	}
        if (oei != oe_end) { // this will be true iff some decrement fill is detected
	  //cout << " ...can't pre-route about pivot edge " << pivot_e << " because of decrement fill-in" << endl;
	  continue;
	}

	// ensure that we cant reach src(e) from src(pivot_e) (would create cycle)
	// first clear visited list
	for (tie(cleari, clear_end) = vertices(angelLCG); cleari != clear_end; ++cleari) visited[*cleari] = false;
	if (reachable (source(pivot_e, angelLCG), source(e, angelLCG), angelLCG)) {
	  //cout << " ...can't pre-route about pivot edge " << pivot_e << " because " << source (e, angelLCG) << " is reachable from " << source (pivot_e, angelLCG) << endl;
	  continue;
	}
	//cout << " -> viable prerouting about pivot edge " << pivot_e << endl;
	erv.push_back (edge_reroute_t (e, pivot_e, true));

      } // end all pivot candidates
    } // end check for pre-routability

    // check for postroutability
    if (out_degree (source (e, angelLCG), angelLCG) > 1) {
      // iterate over possible pivots (outedges of src(e))
      for (tie (oei, oe_end) = out_edges (source (e, angelLCG), angelLCG); oei != oe_end; ++oei) {
	c_graph_t::edge_t pivot_e = *oei;
	// skip the edge we're considering for rerouting
	if (target (pivot_e, angelLCG) == target (e, angelLCG)) continue;
	// tgt(pivot_e) can't be a dependent vertex (we add an edge out of it)
	if (out_degree (target (pivot_e, angelLCG), angelLCG) == 0) continue;
	// ensure that no decrement fill-in is created
	for (tie(iei, ie_end) = in_edges(target(pivot_e, angelLCG), angelLCG); iei != ie_end; ++iei) {
	  if (*iei == pivot_e) continue; // skip the pivot edge
	  tie(decrement_e, found_decrement_e) = edge(source(*iei, angelLCG), target(e, angelLCG), angelLCG);
	  if (!found_decrement_e) break; // decrement fill-in has been found (not allowed)
	}
        if (iei != ie_end) { // this will be true iff some decrement fill is detected
	  //cout << " ...can't post-route about pivot edge " << pivot_e << " because of decrement fill-in" << endl;
	  continue;
	}

	// ensure that we cant reach tgt(pivot_e) from tgt(e) (would create cycle)
	// first clear visited list
	for (tie(cleari, clear_end) = vertices(angelLCG); cleari != clear_end; ++cleari) visited[*cleari] = false;
	if (reachable (target(e, angelLCG), target(pivot_e, angelLCG), angelLCG)) {
	  //cout << " ...can't post-route about pivot edge " << pivot_e << " because " << target(pivot_e, angelLCG) << " is reachable from " << target(e, angelLCG) << endl;
	  continue;
	}
	//cout << " -> viable postrouting about pivot edge " << pivot_e << endl;
	erv.push_back (edge_reroute_t (e, pivot_e, false));

      } // end all pivot candidates
    } // end check for postroutability
    //cout << endl;
    
  } // end all edges in angelLCG
  //cout << endl;

#ifndef NDEBUG
  cout << "	There are " << erv.size() << " reroutings in G" << endl;
#endif
  
} // end reroutable_edges()

bool edge_reducing_rerouteElims_types12 (const vector<edge_reroute_t>& erv1,
					 const c_graph_t& angelLCG,
					 const Elimination::AwarenessLevel_E ourAwarenessLevel,
					 bool allowMaintainingFlag,
					 vector<edge_reroute_t>& erv2) {
  erv2.clear();
  if (erv1.empty()) return 0;
  boost::property_map<c_graph_t, EdgeType>::const_type eType = get(EdgeType(), angelLCG);

  c_graph_t::iei_t iei, ie_end;
  c_graph_t::oei_t oei, oe_end;
  c_graph_t::edge_t absorb_e, increment_absorb_e, decrement_absorb_e;
  bool found_absorb_e, found_increment_absorb_e, found_decrement_absorb_e, incrementIsTrivial;

  for (size_t i = 0; i < erv1.size(); i++) {
    c_graph_t::edge_t e = erv1[i].e;
    c_graph_t::edge_t pe = erv1[i].pivot_e;
    erv1[i].pivot_eliminatable = false;
    erv1[i].increment_eliminatable = false;
    int nontrivialEdgeChange_rerouting = 0;
    int nontrivialEdgeChange_elimPivot = 0;
    int nontrivialEdgeChange_elimIncrement = 0;

    // consider the loss of the rerouted edge
    if (ourAwarenessLevel == Elimination::NO_AWARENESS)						nontrivialEdgeChange_rerouting--;
    else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[e] != UNIT_EDGE)		nontrivialEdgeChange_rerouting--;
    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[e] == VARIABLE_EDGE)	nontrivialEdgeChange_rerouting--;

    if (erv1[i].isPre) { // pre-routing
      //------------------------------------------------------------------------------------------------------------------------------------------------
      // determine nontrivialEdgeChange_rerouting
      //------------------------------------------------------------------------------------------------------------------------------------------------

      // DECREMENT EDGES
      // We don't allow decrement fill-in, but we allow when a decrement edge goes from trivial to nontrivial
      for (tie (oei, oe_end) = out_edges (source(pe, angelLCG), angelLCG); oei != oe_end; ++oei) {
	if (*oei == pe) continue; // skip the pivot edge
	tie (decrement_absorb_e, found_decrement_absorb_e) = edge (source (e, angelLCG), target (*oei, angelLCG), angelLCG);
	throw_exception (!found_decrement_absorb_e, consistency_exception, "Pre-routing passed to filter causes decrement fill-in");	
	// no awareness: no effect
	// unit awareness:
	if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[decrement_absorb_e] == UNIT_EDGE) nontrivialEdgeChange_rerouting++;
	// constant awareness:
	else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[decrement_absorb_e] != VARIABLE_EDGE)
	  if (eType[e] == VARIABLE_EDGE || eType[pe] == VARIABLE_EDGE || eType[*oei] == VARIABLE_EDGE) nontrivialEdgeChange_rerouting++;
      } // end all outedges of src(pivot_e)

      // INCREMENT EDGE	
      // change occurs only when increment edge was nontrivial to begin with
      tie (increment_absorb_e, found_increment_absorb_e) = edge (source (e, angelLCG), source (pe, angelLCG), angelLCG);
      if (found_increment_absorb_e) { // increment absorption
	// no awareness:
	if (ourAwarenessLevel == Elimination::NO_AWARENESS) incrementIsTrivial = false;
	// unit awareness: increase in nontriv iff increment edge was trivial to begin with
	else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS) {
	  incrementIsTrivial = false; // because of absorption (addition) it will be nontrivial no matter what
	  if (eType[increment_absorb_e] == UNIT_EDGE) nontrivialEdgeChange_rerouting++;
	} // end unit awareness
	// constant awareness: increase in nontriv iff increment was triv and any involved edge is variable
	else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS) {
	  // if ANY involved edge is variable, then increment edge is nontrivial
	  if (eType[increment_absorb_e] == VARIABLE_EDGE || eType[e] == VARIABLE_EDGE || eType[pe] == VARIABLE_EDGE)
	    incrementIsTrivial = false;
	  else incrementIsTrivial = true;
	  // if the result is nontrivial, but the increment edge WAS trivial to begin with, our nontriv count goes up
	  if (eType[increment_absorb_e] != VARIABLE_EDGE && !incrementIsTrivial) nontrivialEdgeChange_rerouting++;
	} // end constant awareness
      } // end increment absorption
      else { // increment fill-in
	// no awareness
	if (ourAwarenessLevel == Elimination::NO_AWARENESS) {
	  nontrivialEdgeChange_rerouting++;
	  incrementIsTrivial = false;
	}
	// unit awareness
	else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS) {
	  if (eType[e] != UNIT_EDGE || eType[pe] != UNIT_EDGE) {
	    nontrivialEdgeChange_rerouting++;
	    incrementIsTrivial = false;
	  }
	  else incrementIsTrivial = true;
	} // end unit awareness
	// constant awareness
	else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS) {
	  if (eType[e] == VARIABLE_EDGE || eType[pe] == VARIABLE_EDGE) {
	    nontrivialEdgeChange_rerouting++;
	    incrementIsTrivial = false;
	  }
	  else incrementIsTrivial = true;
	}
      } // end increment fill-in

      //------------------------------------------------------------------------------------------------------------------------------------------------
      // determine effect of back-eliminating the increment edge on the nontrivial edge count
      //------------------------------------------------------------------------------------------------------------------------------------------------

      // determine nontrivialEdgeChange_elimIncrement

      // cannot back-eliminate the increment edge if src(e) is an independent
      if (in_degree (source (e, angelLCG), angelLCG) > 0) {
	// determine effect of removing the increment edge
	if (!incrementIsTrivial) nontrivialEdgeChange_elimIncrement--;

	// examine effect of back-eliminating increment edge
	for (tie (iei, ie_end) = in_edges (source(e, angelLCG), angelLCG); iei != ie_end; ++iei) {
	  tie (absorb_e, found_absorb_e) = edge (source (*iei, angelLCG), source (pe, angelLCG), angelLCG);
	  if (found_absorb_e) { // absorption: count when the absorb_e goes from trivial to nontrivial
	    // no awareness: absorption has no effect on edge count
	    // unit awareness: the result is nonunit (addition), all we care about is if it was unit to begin with
	    if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[absorb_e] == UNIT_EDGE) nontrivialEdgeChange_elimIncrement++;
	    // constant awareness: if abrob edge is non variable and either *iei or increment edge is variable...
	    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[absorb_e] != VARIABLE_EDGE)
	      if (eType[*iei] == VARIABLE_EDGE || !incrementIsTrivial) nontrivialEdgeChange_elimIncrement++;
	  } // end absorption
	  else { // fill-in: is the fill-in trivial or not?
	    // no awareness: fill-in is fill-in
	    if (ourAwarenessLevel == Elimination::NO_AWARENESS) nontrivialEdgeChange_elimIncrement++;
	    // unit awareness: fill-in is nontriv if either *iei or increment edge is nontriv
	    else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS)
	      if (eType[*iei] != UNIT_EDGE || !incrementIsTrivial) nontrivialEdgeChange_elimIncrement++;
	    // constant awareness:
	    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS)
	      if (eType[*iei] == VARIABLE_EDGE || !incrementIsTrivial) nontrivialEdgeChange_elimIncrement++;
	  } // end fill-in
        } // end all preds of src(e)

	if (allowMaintainingFlag && nontrivialEdgeChange_rerouting + nontrivialEdgeChange_elimIncrement <= 0)
	    erv1[i].increment_eliminatable = true;
	else if (nontrivialEdgeChange_rerouting + nontrivialEdgeChange_elimIncrement < 0)
	    erv1[i].increment_eliminatable = true;
      } // end if increment edge can be back-eliminated

      //------------------------------------------------------------------------------------------------------------------------------------------------
      // determine effect of front-eliminating the pivot edge on the nontrivial edge count
      //------------------------------------------------------------------------------------------------------------------------------------------------

      // front-elimination of pivot edge MUST isolate the target
      if (in_degree (target (pe, angelLCG), angelLCG) == 2 && vertex_type (target (pe, angelLCG), angelLCG) != dependent) {

	// determine effect of eliminating the pivot edge
	if (ourAwarenessLevel == Elimination::NO_AWARENESS)						nontrivialEdgeChange_elimPivot--;
	else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[pe] != UNIT_EDGE)		nontrivialEdgeChange_elimPivot--;
	else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[pe] == VARIABLE_EDGE)	nontrivialEdgeChange_elimPivot--;

	// iterate over successors of tgt(pe)
	// the fill/absorb edges will have the same source as the pivot edge
	for (tie (oei, oe_end) = out_edges(target(pe, angelLCG), angelLCG); oei != oe_end; ++oei) {
	  // determine effect of removing the outedge
	  if (ourAwarenessLevel == Elimination::NO_AWARENESS)							nontrivialEdgeChange_elimPivot--;
	  else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[*oei] != UNIT_EDGE)		nontrivialEdgeChange_elimPivot--;
	  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[*oei] == VARIABLE_EDGE)	nontrivialEdgeChange_elimPivot--;

	  tie (absorb_e, found_absorb_e) = edge (source(pe, angelLCG), target(*oei, angelLCG), angelLCG);
	  if (found_absorb_e) { // absorption: we need to detect of it goes from trivial to nontrivial
	    // no awareness: absorption has no effect on edge count
	    // unit awareness
	    if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[absorb_e] == UNIT_EDGE) nontrivialEdgeChange_elimPivot++;
	    // constant awareness
	    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[absorb_e] != VARIABLE_EDGE)
	      if (eType[pe] == VARIABLE_EDGE || eType[*oei] == VARIABLE_EDGE) nontrivialEdgeChange_elimPivot++;
	  } // end absorption case
	  else { // fill-in
	    // no awareness: fill-in is fill-in
	    if (ourAwarenessLevel == Elimination::NO_AWARENESS) nontrivialEdgeChange_elimPivot++;
	    // unit awareness: fill is nontriv iff either pe or *oei is nonunit
	    else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS)
	      if (eType[pe] != UNIT_EDGE || eType[*oei] != UNIT_EDGE) nontrivialEdgeChange_elimPivot++;
	    // constant awareness: fill is nontriv iff either pe or *oei is variable
	    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS)
	      if (eType[pe] != VARIABLE_EDGE || eType[*oei] == VARIABLE_EDGE) nontrivialEdgeChange_elimPivot++;
	  } // end fill-in case

	} // end all successors of tgt(e)=tgt(pe)

	if (allowMaintainingFlag && nontrivialEdgeChange_rerouting + nontrivialEdgeChange_elimPivot <= 0)
	    erv1[i].pivot_eliminatable = true;
	else if (nontrivialEdgeChange_rerouting + nontrivialEdgeChange_elimPivot < 0)
	    erv1[i].pivot_eliminatable = true;
      } // end determine nontrivialEdgeChange_elimPivot

    } // end pre-routing

    else { //post-routing
      //------------------------------------------------------------------------------------------------------------------------------------------------
      // determine nontrivialEdgeChange_rerouting
      //------------------------------------------------------------------------------------------------------------------------------------------------

      // DECREMENT EDGES
      // We don't allow decrement fill-in, but we allow when a decrement edge goes from trivial to nontrivial
      for (tie(iei, ie_end) = in_edges(target(pe, angelLCG), angelLCG); iei != ie_end; ++iei) {
	if (*iei == pe) continue; // skip the pivot edge
	tie (decrement_absorb_e, found_decrement_absorb_e) = edge (source(*iei, angelLCG), target(e, angelLCG), angelLCG);
	throw_exception (!found_decrement_absorb_e, consistency_exception, "Post-routing passed to filter causes decrement fill-in");	
	// no awareness: no effect
	// unit awareness:
	if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[decrement_absorb_e] == UNIT_EDGE) nontrivialEdgeChange_rerouting++;
	// constant awareness:
	else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[decrement_absorb_e] != VARIABLE_EDGE)
	  if (eType[e] == VARIABLE_EDGE || eType[pe] == VARIABLE_EDGE || eType[*iei] == VARIABLE_EDGE) nontrivialEdgeChange_rerouting++;
      } // end all outedges of src(pivot_e)

      // INCREMENT EDGE: change occurs only when increment edge was nontrivial to begin with
      tie (increment_absorb_e, found_increment_absorb_e) = edge (target(pe, angelLCG), target(e, angelLCG), angelLCG);
      if (found_increment_absorb_e) { // increment absorption
	// no awareness:
	if (ourAwarenessLevel == Elimination::NO_AWARENESS) incrementIsTrivial = false;
	// unit awareness: increase in nontriv iff increment edge was trivial to begin with
	else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS) {
	  incrementIsTrivial = false; // because of absorption (addition) it will be nontrivial no matter what
	  if (eType[increment_absorb_e] == UNIT_EDGE) nontrivialEdgeChange_rerouting++;
	} // end unit awareness
	// constant awareness: increase in nontriv iff increment was triv and any involved edge is variable
	else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS) {
	  // if ANY involved edge is variable, then increment edge is nontrivial
	  if (eType[increment_absorb_e] == VARIABLE_EDGE || eType[e] == VARIABLE_EDGE || eType[pe] == VARIABLE_EDGE)
	    incrementIsTrivial = false;
	  else incrementIsTrivial = true;
	  // if the result is nontrivial, but the increment edge WAS trivial to begin with, our nontriv count goes up
	  if (eType[increment_absorb_e] != VARIABLE_EDGE && !incrementIsTrivial) nontrivialEdgeChange_rerouting++;
	} // end constant awareness
      } // end increment absorption
      else { // increment fill-in
	// no awareness
	if (ourAwarenessLevel == Elimination::NO_AWARENESS) {
	  nontrivialEdgeChange_rerouting++;
	  incrementIsTrivial = false;
	}
	// unit awareness
	else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS) {
	  if (eType[e] != UNIT_EDGE || eType[pe] != UNIT_EDGE) {
	    nontrivialEdgeChange_rerouting++;
	    incrementIsTrivial = false;
	  }
	  else incrementIsTrivial = true;
	} // end unit awareness
	// constant awareness
	else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS) {
	  if (eType[e] == VARIABLE_EDGE || eType[pe] == VARIABLE_EDGE) {
	    nontrivialEdgeChange_rerouting++;
	    incrementIsTrivial = false;
	  }
	  else incrementIsTrivial = true;
	}
      } // end increment fill-in

      //------------------------------------------------------------------------------------------------------------------------------------------------
      // determine effect of front-eliminating the increment edge on the nontrivial edge count
      //------------------------------------------------------------------------------------------------------------------------------------------------

      // cannot front-eliminate the increment edge if tgt(e) has no outedges
      if (out_degree(target(e, angelLCG), angelLCG) > 0) {
	// determine effect of removing the increment edge
	if (!incrementIsTrivial) nontrivialEdgeChange_elimIncrement--;

	// examine effect of front-eliminating increment edge
	for (tie (oei, oe_end) = out_edges(target(e, angelLCG), angelLCG); oei != oe_end; ++oei) {
	  tie (absorb_e, found_absorb_e) = edge(target(pe, angelLCG), target(*oei, angelLCG), angelLCG);
	  if (found_absorb_e) { // absorption: count when the absorb_e goes from trivial to nontrivial
	    // no awareness: absorption has no effect on edge count
	    // unit awareness: the result is nonunit (addition), all we care about is if it was unit to begin with
	    if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[absorb_e] == UNIT_EDGE) nontrivialEdgeChange_elimIncrement++;
	    // constant awareness: if absorb edge is non variable and either *oei or increment edge is variable...
	    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[absorb_e] != VARIABLE_EDGE)
	      if (eType[*oei] == VARIABLE_EDGE || !incrementIsTrivial) nontrivialEdgeChange_elimIncrement++;
	  } // end absorption
	  else { // fill-in: is the fill-in trivial or not?
	    // no awareness: fill-in is fill-in
	    if (ourAwarenessLevel == Elimination::NO_AWARENESS) nontrivialEdgeChange_elimIncrement++;
	    // unit awareness: fill-in is nontriv if either *oei or increment edge is nontriv
	    else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS)
	      if (eType[*oei] != UNIT_EDGE || !incrementIsTrivial) nontrivialEdgeChange_elimIncrement++;
	    // constant awareness:
	    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS)
	      if (eType[*oei] == VARIABLE_EDGE || !incrementIsTrivial) nontrivialEdgeChange_elimIncrement++;
	  } // end fill-in
        } // end all preds of src(e)

	if (allowMaintainingFlag && nontrivialEdgeChange_rerouting + nontrivialEdgeChange_elimIncrement <= 0)
	    erv1[i].increment_eliminatable = true;
	else if (nontrivialEdgeChange_rerouting + nontrivialEdgeChange_elimIncrement < 0)
	    erv1[i].increment_eliminatable = true;
      } // end if increment edge can be back-eliminated

      //------------------------------------------------------------------------------------------------------------------------------------------------
      // determine effect of back-eliminating the pivot edge on the nontrivial edge count
      //------------------------------------------------------------------------------------------------------------------------------------------------

      // front-elimination of pivot edge MUST isolate the target
      if (out_degree (source(pe, angelLCG), angelLCG) == 2 && in_degree (source(pe, angelLCG), angelLCG) > 0) {

	// determine effect of eliminating the pivot edge
	if (ourAwarenessLevel == Elimination::NO_AWARENESS)						nontrivialEdgeChange_elimPivot--;
	else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[pe] != UNIT_EDGE)		nontrivialEdgeChange_elimPivot--;
	else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[pe] == VARIABLE_EDGE)	nontrivialEdgeChange_elimPivot--;

	// iterate over predecessors of src(pe)
	// the fill/absorb edges will have the same target as the pivot edge
	for (tie (iei, ie_end) = in_edges(source(pe, angelLCG), angelLCG); iei != ie_end; ++iei) {
	  // determine effect of removing the outedge
	  if (ourAwarenessLevel == Elimination::NO_AWARENESS)							nontrivialEdgeChange_elimPivot--;
	  else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[*iei] != UNIT_EDGE)		nontrivialEdgeChange_elimPivot--;
	  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[*iei] == VARIABLE_EDGE)	nontrivialEdgeChange_elimPivot--;

	  tie (absorb_e, found_absorb_e) = edge (source(*iei, angelLCG), target(pe, angelLCG), angelLCG);
	  if (found_absorb_e) { // absorption: we need to detect of it goes from trivial to nontrivial
	    // no awareness: absorption has no effect on edge count
	    // unit awareness
	    if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[absorb_e] == UNIT_EDGE) nontrivialEdgeChange_elimPivot++;
	    // constant awareness
	    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[absorb_e] != VARIABLE_EDGE)
	      if (eType[pe] == VARIABLE_EDGE || eType[*iei] == VARIABLE_EDGE) nontrivialEdgeChange_elimPivot++;
	  } // end absorption case
	  else { // fill-in
	    // no awareness: fill-in is fill-in
	    if (ourAwarenessLevel == Elimination::NO_AWARENESS) nontrivialEdgeChange_elimPivot++;
	    // unit awareness: fill is nontriv iff either pe or *iei is nonunit
	    else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS)
	      if (eType[pe] != UNIT_EDGE || eType[*iei] != UNIT_EDGE) nontrivialEdgeChange_elimPivot++;
	    // constant awareness: fill is nontriv iff either pe or *iei is variable
	    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS)
	      if (eType[pe] != VARIABLE_EDGE || eType[*iei] == VARIABLE_EDGE) nontrivialEdgeChange_elimPivot++;
	  } // end fill-in case

	} // end all successors of tgt(e)=tgt(pe)

	if (allowMaintainingFlag && nontrivialEdgeChange_rerouting + nontrivialEdgeChange_elimPivot <= 0)
	    erv1[i].pivot_eliminatable = true;
	else if (nontrivialEdgeChange_rerouting + nontrivialEdgeChange_elimPivot < 0)
	    erv1[i].pivot_eliminatable = true;
      } // end determine nontrivialEdgeChange_elimPivot

    } // end post-routing

    if (erv1[i].increment_eliminatable || erv1[i].pivot_eliminatable)
      erv2.push_back(erv1[i]);

  } // end iterate through erv1
  
  if (erv2.empty()) {
    erv2 = erv1;
    return false;
  }
  else return true;
} // end edge_reducing_rerouteElims_types12()

int reroute_effect (const edge_reroute_t er,
		    const c_graph_t& angelLCG,
		    const Elimination::AwarenessLevel_E ourAwarenessLevel,
		    bool& incrementIsTrivial) {

  c_graph_t::edge_t e = er.e;
  c_graph_t::edge_t pe = er.pivot_e;
  c_graph_t::iei_t iei, ie_end;
  c_graph_t::oei_t oei, oe_end;
  boost::property_map<c_graph_t, EdgeType>::const_type eType = get(EdgeType(), angelLCG);
  c_graph_t::edge_t increment_e, decrement_e;
  bool found_increment_e, found_decrement_e;

  int nontrivial_edge_change = 0;

  // consider the loss of the rerouted edge
  if (ourAwarenessLevel == Elimination::NO_AWARENESS
  || (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[e] != UNIT_EDGE)
  || (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[e] == VARIABLE_EDGE)) nontrivial_edge_change--;

  if (er.isPre) { // pre-routing
    // DECREMENT EDGES: No fill-in, but we allow when a decrement edge goes from trivial to nontrivial
    for (tie(oei, oe_end) = out_edges(source(pe, angelLCG), angelLCG); oei != oe_end; ++oei) {
      if (*oei == pe) continue; // skip the pivot edge
      tie (decrement_e, found_decrement_e) = edge(source(e, angelLCG), target(*oei, angelLCG), angelLCG);
      throw_exception (!found_decrement_e, consistency_exception, "Pre-routing passed to filter causes decrement fill-in");	
      // no awareness: no effect
      // unit awareness:
      if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[decrement_e] == UNIT_EDGE) nontrivial_edge_change++;
      // constant awareness:
      else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[decrement_e] != VARIABLE_EDGE)
	if (eType[e] == VARIABLE_EDGE || eType[pe] == VARIABLE_EDGE || eType[*oei] == VARIABLE_EDGE) nontrivial_edge_change++;
    } // end all outedges of src(pivot_e)

    // INCREMENT EDGE: change occurs only when increment edge was nontrivial to begin with
    tie(increment_e, found_increment_e) = edge(target(pe, angelLCG), target(e, angelLCG), angelLCG);
    if (found_increment_e) { // increment absorption
      if (ourAwarenessLevel == Elimination::NO_AWARENESS) incrementIsTrivial = false;
      else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS) {
	incrementIsTrivial = false; // because of absorption (addition) it will be nontrivial no matter what
	if (eType[increment_e] == UNIT_EDGE) nontrivial_edge_change++;
      } // end unit awareness
      else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS) {
	// if ANY involved edge is variable, then increment edge is nontrivial
	if (eType[increment_e] == VARIABLE_EDGE || eType[e] == VARIABLE_EDGE || eType[pe] == VARIABLE_EDGE)
	  incrementIsTrivial = false;
	else incrementIsTrivial = true;
	// if the result is nontrivial, but the increment edge WAS trivial to begin with, our nontriv count goes up
	if (eType[increment_e] != VARIABLE_EDGE && !incrementIsTrivial) nontrivial_edge_change++;
      } // end constant awareness
    } // end increment absorption
    else { // increment fill-in
      if (ourAwarenessLevel == Elimination::NO_AWARENESS) {
	nontrivial_edge_change++;
	incrementIsTrivial = false;
      } // end no awareness
      else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS) {
	if (eType[e] != UNIT_EDGE || eType[pe] != UNIT_EDGE) {
	  nontrivial_edge_change++;
	  incrementIsTrivial = false;
	}
	else incrementIsTrivial = true;
      } // end unit awareness
      else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS) {
	if (eType[e] == VARIABLE_EDGE || eType[pe] == VARIABLE_EDGE) {
	  nontrivial_edge_change++;
	  incrementIsTrivial = false;
	}
	else incrementIsTrivial = true;
      } // end constant awareness
    } // end increment fill-in

  } // end pre-routing
  else { // post-routing

    // DECREMENT EDGES: No fill-in, but we allow when a decrement edge goes from trivial to nontrivial
    for (tie(iei, ie_end) = in_edges(target(pe, angelLCG), angelLCG); iei != ie_end; ++iei) {
      if (*iei == pe) continue; // skip the pivot edge
      tie (decrement_e, found_decrement_e) = edge (source(*iei, angelLCG), target(e, angelLCG), angelLCG);
      throw_exception (!found_decrement_e, consistency_exception, "Post-routing passed to filter causes decrement fill-in");	
      // no awareness: no effect
      // unit awareness:
      if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[decrement_e] == UNIT_EDGE) nontrivial_edge_change++;
      // constant awareness:
      else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[decrement_e] != VARIABLE_EDGE)
	if (eType[e] == VARIABLE_EDGE || eType[pe] == VARIABLE_EDGE || eType[*iei] == VARIABLE_EDGE) nontrivial_edge_change++;
    } // end all outedges of src(pivot_e)

    // INCREMENT EDGE: change occurs only when increment edge was nontrivial to begin with
    tie(increment_e, found_increment_e) = edge(target(pe, angelLCG), target(e, angelLCG), angelLCG);
    if (found_increment_e) { // increment absorption
      if (ourAwarenessLevel == Elimination::NO_AWARENESS) incrementIsTrivial = false;
      else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS) { // increase iff edge was trivial to begin with
	incrementIsTrivial = false; // because of absorption (addition) it will be nontrivial no matter what
	if (eType[increment_e] == UNIT_EDGE) nontrivial_edge_change++;
      } // end unit awareness
      else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS) {
	// if ANY involved edge is variable, then increment edge is nontrivial
	if (eType[increment_e] == VARIABLE_EDGE || eType[e] == VARIABLE_EDGE || eType[pe] == VARIABLE_EDGE) incrementIsTrivial = false;
	else incrementIsTrivial = true;
	// if the result is nontrivial, but the increment edge WAS trivial to begin with, our nontriv count goes up
	if (eType[increment_e] != VARIABLE_EDGE && !incrementIsTrivial) nontrivial_edge_change++;
      } // end constant awareness
    } // end increment absorption
    else { // increment fill-in
      if (ourAwarenessLevel == Elimination::NO_AWARENESS) {
	nontrivial_edge_change++;
	incrementIsTrivial = false;
      } // end no awareness
      else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS) {
	if (eType[e] != UNIT_EDGE || eType[pe] != UNIT_EDGE) {
	  nontrivial_edge_change++;
	  incrementIsTrivial = false;
	}
	else incrementIsTrivial = true;
      } // end unit awareness
      else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS) {
	if (eType[e] == VARIABLE_EDGE || eType[pe] == VARIABLE_EDGE) {
	  nontrivial_edge_change++;
	  incrementIsTrivial = false;
	}
	else incrementIsTrivial = true;
      } // end constant awareness
    } // end increment fill-in

  } // end post-routing

  return nontrivial_edge_change;
} // end reroute_effect()

bool edge_reducing_rerouteElims_type3 (const vector<edge_reroute_t>& erv1,
				       const c_graph_t& angelLCG,
				       const Elimination::AwarenessLevel_E ourAwarenessLevel,
				       const bool allowMaintainingFlag,
				       vector<edge_reroute_t>& erv2) {
  erv2.clear();
  if (erv1.empty()) return 0;
  boost::property_map<c_graph_t, EdgeType>::const_type eType = get(EdgeType(), angelLCG);
  c_graph_t::iei_t iei, ie_end;
  c_graph_t::oei_t oei, oe_end;
  c_graph_t::edge_t absorb_e;
  bool found_absorb_e;

  for (size_t i = 0; i < erv1.size(); i++) {
    bool incrementIsTrivial;
    int nontrivialEdgeChange_rerouting = reroute_effect (erv1[i], angelLCG, ourAwarenessLevel, incrementIsTrivial);
    c_graph_t::edge_t e = erv1[i].e;
    c_graph_t::edge_t pe = erv1[i].pivot_e;
    erv1[i].type3EdgeElimVector.clear();

    if (erv1[i].isPre) { // pre-routing

      // iterate over outedges of tgt(e), consider back-elimination of *oei
      for (tie(oei, oe_end) = out_edges(target(e, angelLCG), angelLCG); oei != oe_end; ++oei) {
	int nontrivialEdgeChange_backElimination = 0;

	// consider loss of *oei
	if (ourAwarenessLevel == Elimination::NO_AWARENESS
	|| (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[*oei] != UNIT_EDGE)
	|| (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[*oei] == VARIABLE_EDGE)) nontrivialEdgeChange_backElimination--;

	// consider fill/absorb effect of back-eliminating *oei
	for (tie(iei, ie_end) = in_edges(target(e, angelLCG), angelLCG); iei != ie_end; ++iei) {
	  if (*iei == e) continue; // skip the rerouted edge
	  tie(absorb_e, found_absorb_e) = edge(source(*iei, angelLCG), target(*oei, angelLCG), angelLCG);
	  if (found_absorb_e) { // absorption: only counts if it goes from trivial to nontrivial
	    // UNIT AWARENESS: result is nonunit no matter what, because of the addition
	    if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[absorb_e] == UNIT_EDGE) nontrivialEdgeChange_backElimination++;
	    // CONSTANT AWARENESS: if absorb_e is trivial, result is nontrivial iff either *oei or *iei is nontrivial
	    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[absorb_e] != VARIABLE_EDGE)
	      if (eType[*oei] == VARIABLE_EDGE || eType[*iei] == VARIABLE_EDGE) nontrivialEdgeChange_backElimination++;
	  }
	  else { // fill-in
	    if (ourAwarenessLevel == Elimination::NO_AWARENESS) nontrivialEdgeChange_backElimination++;
	    // UNIT AWARENESS: nontrivial iff either *oei or *iei is nonunit
	    else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS)
	      if (eType[*oei] != UNIT_EDGE || eType[*iei] != UNIT_EDGE) nontrivialEdgeChange_backElimination++;
	    // CONSTANT AWARENESS: nontrivial iff either *oei or *iei is variable
	    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS)
	      if (eType[*oei] == VARIABLE_EDGE || eType[*iei] == VARIABLE_EDGE) nontrivialEdgeChange_backElimination++;
	  }
	} // end all inedges of tgt(e)

	if (nontrivialEdgeChange_rerouting + nontrivialEdgeChange_backElimination < 0
	|| (allowMaintainingFlag && nontrivialEdgeChange_rerouting + nontrivialEdgeChange_backElimination <= 0))
	  erv1[i].type3EdgeElimVector.push_back(target(*oei, angelLCG));
      } // end all outedges of tgt(e)

    } // end pre-routing
    else { // post-routing

      // iterate over inedges of src(e), consider front-elimination of *iei
      for (tie(iei, ie_end) = in_edges(source(e, angelLCG), angelLCG); iei != ie_end; ++iei) {
	int nontrivialEdgeChange_frontElimination = 0;

	// consider loss of *iei
	if (ourAwarenessLevel == Elimination::NO_AWARENESS
	|| (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[*iei] != UNIT_EDGE)
	|| (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[*iei] == VARIABLE_EDGE)) nontrivialEdgeChange_frontElimination--;

	// consider fill/absorb effect of front-eliminating *iei
        for (tie(oei, oe_end) = out_edges(source(e, angelLCG), angelLCG); oei != oe_end; ++oei) {
	  if (*oei == e) continue; // skip the rerouted edge
	  tie(absorb_e, found_absorb_e) = edge(source(*iei, angelLCG), target(*oei, angelLCG), angelLCG);
	  if (found_absorb_e) { // absorption: only counts if it goes from trivial to nontrivial
	    // UNIT AWARENESS: result is nonunit no matter what, because of the addition
	    if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && eType[absorb_e] == UNIT_EDGE) nontrivialEdgeChange_frontElimination++;
	    // CONSTANT AWARENESS: if absorb_e is trivial, result is nontrivial iff either *oei or *iei is nontrivial
	    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && eType[absorb_e] != VARIABLE_EDGE)
	      if (eType[*oei] == VARIABLE_EDGE || eType[*iei] == VARIABLE_EDGE) nontrivialEdgeChange_frontElimination++;
	  }
	  else { // fill-in
	    if (ourAwarenessLevel == Elimination::NO_AWARENESS) nontrivialEdgeChange_frontElimination++;
	    // UNIT AWARENESS: nontrivial iff either *oei or *iei is nonunit
	    else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS)
	      if (eType[*oei] != UNIT_EDGE || eType[*iei] != UNIT_EDGE) nontrivialEdgeChange_frontElimination++;
	    // CONSTANT AWARENESS: nontrivial iff either *oei or *iei is variable
	    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS)
	      if (eType[*oei] == VARIABLE_EDGE || eType[*iei] == VARIABLE_EDGE) nontrivialEdgeChange_frontElimination++;
	  } // end fill-in
	} // end all outedges of src(e)

	if (nontrivialEdgeChange_rerouting + nontrivialEdgeChange_frontElimination < 0
	|| (allowMaintainingFlag && nontrivialEdgeChange_rerouting + nontrivialEdgeChange_frontElimination <= 0))
	  erv1[i].type3EdgeElimVector.push_back(source(*iei, angelLCG));
      } // end all inedges of src(e)

    } // end post-routing

    if (!erv1[i].type3EdgeElimVector.empty()) erv2.push_back(erv1[i]);

  } // end iterate over erv1

  if (erv2.empty()) {
    erv2 = erv1;
    return false;
  }
  else return true;
} // end  edge_reducing_rerouteElims_type3()

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
				     JacobianAccumulationExpressionList& jae_list) {
  unsigned int cost = 0;
  boost::property_map<c_graph_t, EdgeType>::type eType = get(EdgeType(), angelLCG);
  c_graph_t::iei_t iei, ie_end; 
  c_graph_t::oei_t oei, oe_end; 

  JacobianAccumulationExpression& new_jae = jae_list.addExpression();
  // Increment the edge from the source of e to to v by the quotient e/pivot_e (create it if it doesnt exist)
  JacobianAccumulationExpressionVertex& jaev_divide = new_jae.addVertex();
  //jaev_divide.setOperation (JacobianAccumulationExpressionVertex::DIVIDE_OP);
  jaev_divide.setOperation (JacobianAccumulationExpressionVertex::ADD_OP);
  JacobianAccumulationExpressionVertex& jaev_e = new_jae.addVertex();
  JacobianAccumulationExpressionVertex& jaev_pivot_e = new_jae.addVertex();
  setJaevRef (er.e, jaev_e, angelLCG, edge_ref_list);
  setJaevRef (er.pivot_e, jaev_pivot_e, angelLCG, edge_ref_list);
  new_jae.addEdge(jaev_e, jaev_divide);
  new_jae.addEdge(jaev_pivot_e, jaev_divide);

  // INCREMENT EDGE
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
  } // end increment absorption
  else { //no increment edge was already present (fill-in)
    tie (increment_e, found_increment_e) = add_edge (source (er.e, angelLCG), source (er.pivot_e, angelLCG), angelLCG.next_edge_number++, angelLCG);

    // point the new edge at the divide operation in the new JAE
    EdgeRef_t new_increment_e_ref (increment_e, &jaev_divide);
    edge_ref_list.push_back(new_increment_e_ref);

    //set edge type for fill-in increment edge
    if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE)	eType[increment_e] = VARIABLE_EDGE;
    else if (eType[er.e] == UNIT_EDGE && eType[er.pivot_e] == UNIT_EDGE)	eType[increment_e] = UNIT_EDGE;
    else									eType[increment_e] = CONSTANT_EDGE;
  }

  // determine cost of creating increment edge
  if (ourAwarenessLevel == Elimination::NO_AWARENESS)
    cost++;
  else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && (eType[er.e] != UNIT_EDGE || eType[er.pivot_e] != UNIT_EDGE))
    cost++;
  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE))
    cost++;

  // DECREMENT OPERATIONS

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

    bool found_decrement_e;
    c_graph_t::edge_t decrement_e;
    tie (decrement_e, found_decrement_e) = edge (source (er.e, angelLCG), target (*oei, angelLCG), angelLCG);

    if (found_decrement_e) { // decrement absorption
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
    } // end decrement absorption
    else { // decrement fill-in
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
				      JacobianAccumulationExpressionList& jae_list) {
  unsigned int cost = 0;
  boost::property_map<c_graph_t, EdgeType>::type eType = get(EdgeType(), angelLCG);
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

  // INCREMENT EDGE
  bool found_increment_e;
  c_graph_t::edge_t increment_e;
  tie (increment_e, found_increment_e) = edge (target (er.pivot_e, angelLCG), target (er.e, angelLCG), angelLCG);
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
  } // end increment absorption
  else { //no increment edge was already present (fill-in)
    tie (increment_e, found_increment_e) = add_edge (target (er.pivot_e, angelLCG), target (er.e, angelLCG), angelLCG.next_edge_number++, angelLCG);

    // point the new edge at the divide operation in the new JAE
    EdgeRef_t new_increment_e_ref (increment_e, &jaev_divide);
    edge_ref_list.push_back(new_increment_e_ref);

    //set edge type for fill-in increment edge
    if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE)	eType[increment_e] = VARIABLE_EDGE;
    else if (eType[er.e] == UNIT_EDGE && eType[er.pivot_e] == UNIT_EDGE)	eType[increment_e] = UNIT_EDGE;
    else									eType[increment_e] = CONSTANT_EDGE;
  }

  // determine cost of creating increment edge
  if (ourAwarenessLevel == Elimination::NO_AWARENESS)
    cost++;
  else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && (eType[er.e] != UNIT_EDGE || eType[er.pivot_e] != UNIT_EDGE))
    cost++;
  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE))
    cost++;

  // DECREMENT OPERATIONS

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

    bool found_decrement_e;
    c_graph_t::edge_t decrement_e;
    tie (decrement_e, found_decrement_e) = edge (source (*iei, angelLCG), target (er.e, angelLCG), angelLCG);
    if (found_decrement_e) { // decrement absorption
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
    } // end decrement absorption
    else { // decrement fill-in
      tie (decrement_e, found_decrement_e) = add_edge (source (*iei, angelLCG), target (er.e, angelLCG), angelLCG.next_edge_number++, angelLCG);

      // point the new edge at the divide operation in the new JAE
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

unsigned int prerouteEdge_noJAE (edge_reroute_t er,
                                 c_graph_t& angelLCG,
                                 const Elimination::AwarenessLevel_E ourAwarenessLevel) {
  unsigned int cost = 0;
  boost::property_map<c_graph_t, EdgeType>::type eType = get(EdgeType(), angelLCG);
  c_graph_t::iei_t iei, ie_end; 
  c_graph_t::oei_t oei, oe_end; 

  // INCREMENT EDGE
  bool found_increment_e;
  c_graph_t::edge_t increment_e;
  tie (increment_e, found_increment_e) = edge (source (er.e, angelLCG), source (er.pivot_e, angelLCG), angelLCG);
  if (found_increment_e) { // increment absorption
    //set edge type for absorption increment edge
    if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE)	eType[increment_e] = VARIABLE_EDGE;
    else if (eType[increment_e] != VARIABLE_EDGE)				eType[increment_e] = CONSTANT_EDGE;
  } // end increment absorption
  else { //no increment edge was already present (fill-in)
    tie (increment_e, found_increment_e) = add_edge (source (er.e, angelLCG), source (er.pivot_e, angelLCG), angelLCG.next_edge_number++, angelLCG);
    //set edge type for fill-in increment edge
    if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE)	eType[increment_e] = VARIABLE_EDGE;
    else if (eType[er.e] == UNIT_EDGE && eType[er.pivot_e] == UNIT_EDGE)	eType[increment_e] = UNIT_EDGE;
    else									eType[increment_e] = CONSTANT_EDGE;
  }
  // determine cost of creating increment edge
  if (ourAwarenessLevel == Elimination::NO_AWARENESS) cost++;
  else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && (eType[er.e] != UNIT_EDGE || eType[er.pivot_e] != UNIT_EDGE)) cost++;
  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE)) cost++;

  // DECREMENT EDGES
  for (tie (oei, oe_end) = out_edges (source (er.pivot_e, angelLCG), angelLCG); oei != oe_end; oei++) {
    if (target (*oei, angelLCG) == target (er.e, angelLCG)) continue;
    bool found_decrement_e;
    c_graph_t::edge_t decrement_e;
    tie (decrement_e, found_decrement_e) = edge (source (er.e, angelLCG), target (*oei, angelLCG), angelLCG);
    if (found_decrement_e) { // decrement absorption
      //set edge type for absorption decrement edge
      if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE || eType[*oei] == VARIABLE_EDGE)	eType[decrement_e] = VARIABLE_EDGE;
      else if (eType[decrement_e] != VARIABLE_EDGE)								eType[decrement_e] = CONSTANT_EDGE;
    } // end decrement absorption
    else { // decrement fill-in
      tie (decrement_e, found_decrement_e) = add_edge (source (er.e, angelLCG), target (*oei, angelLCG), angelLCG.next_edge_number++, angelLCG);
      //set edge type for fill-in decrement edge
      if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE || eType[*oei] == VARIABLE_EDGE)	eType[decrement_e] = VARIABLE_EDGE;
      else if (eType[er.e] == UNIT_EDGE && eType[er.pivot_e] == UNIT_EDGE && eType[*oei] == UNIT_EDGE)		eType[decrement_e] = UNIT_EDGE;
      else													eType[decrement_e] = CONSTANT_EDGE;
    }
    if (ourAwarenessLevel == Elimination::NO_AWARENESS) cost++;
    else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && (eType[er.e] != UNIT_EDGE || eType[er.pivot_e] != UNIT_EDGE || eType[*oei] != UNIT_EDGE)) cost++;
    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE|| eType[*oei] == VARIABLE_EDGE)) cost++;
  } // end all decrements
  remove_edge (er.e, angelLCG);
  return cost;
} // end prerouteEdge_noJAE()

unsigned int postrouteEdge_noJAE (edge_reroute_t er,
                                  c_graph_t& angelLCG,
                                  const Elimination::AwarenessLevel_E ourAwarenessLevel) {
  unsigned int cost = 0;
  boost::property_map<c_graph_t, EdgeType>::type eType = get(EdgeType(), angelLCG);
  c_graph_t::iei_t iei, ie_end; 
  c_graph_t::oei_t oei, oe_end; 

  // INCREMENT EDGE
  bool found_increment_e;
  c_graph_t::edge_t increment_e;
  tie (increment_e, found_increment_e) = edge (target (er.pivot_e, angelLCG), target (er.e, angelLCG), angelLCG);
  if (found_increment_e) { // increment absorption
    //set edge type for absorption increment edge
    if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE)	eType[increment_e] = VARIABLE_EDGE;
    else if (eType[increment_e] != VARIABLE_EDGE)				eType[increment_e] = CONSTANT_EDGE;
  } // end increment absorption
  else { //no increment edge was already present (fill-in)
    tie (increment_e, found_increment_e) = add_edge (target (er.pivot_e, angelLCG), target (er.e, angelLCG), angelLCG.next_edge_number++, angelLCG);
    //set edge type for fill-in increment edge
    if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE)	eType[increment_e] = VARIABLE_EDGE;
    else if (eType[er.e] == UNIT_EDGE && eType[er.pivot_e] == UNIT_EDGE)	eType[increment_e] = UNIT_EDGE;
    else									eType[increment_e] = CONSTANT_EDGE;
  }
  // determine cost of creating increment edge
  if (ourAwarenessLevel == Elimination::NO_AWARENESS) cost++;
  else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && (eType[er.e] != UNIT_EDGE || eType[er.pivot_e] != UNIT_EDGE)) cost++;
  else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE)) cost++;

  // DECREMENT EDGES
  for (tie (iei, ie_end) = in_edges (target (er.pivot_e, angelLCG), angelLCG); iei != ie_end; iei++) {
    if (source (*iei, angelLCG) == source (er.pivot_e, angelLCG)) continue;
    bool found_decrement_e;
    c_graph_t::edge_t decrement_e;
    tie (decrement_e, found_decrement_e) = edge (source (*iei, angelLCG), target (er.e, angelLCG), angelLCG);
    if (found_decrement_e) { // decrement absorption
      //set edge type for absorption decrement edge
      if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE || eType[*iei] == VARIABLE_EDGE)	eType[decrement_e] = VARIABLE_EDGE;
      else if (eType[decrement_e] != VARIABLE_EDGE)								eType[decrement_e] = CONSTANT_EDGE;
    } // end decrement absorption
    else { // decrement fill-in
      tie (decrement_e, found_decrement_e) = add_edge (source (*iei, angelLCG), target (er.e, angelLCG), angelLCG.next_edge_number++, angelLCG);
      //set edge type for fill-in decrement edge
      if (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE || eType[*iei] == VARIABLE_EDGE)	eType[decrement_e] = VARIABLE_EDGE;
      else if (eType[er.e] == UNIT_EDGE && eType[er.pivot_e] == UNIT_EDGE && eType[*iei] == UNIT_EDGE)		eType[decrement_e] = UNIT_EDGE;
      else													eType[decrement_e] = CONSTANT_EDGE;
    }
    if (ourAwarenessLevel == Elimination::NO_AWARENESS) cost++;
    else if (ourAwarenessLevel == Elimination::UNIT_AWARENESS && (eType[er.e] != UNIT_EDGE || eType[er.pivot_e] != UNIT_EDGE || eType[*iei] != UNIT_EDGE)) cost++;
    else if (ourAwarenessLevel == Elimination::CONSTANT_AWARENESS && (eType[er.e] == VARIABLE_EDGE || eType[er.pivot_e] == VARIABLE_EDGE|| eType[*iei] == VARIABLE_EDGE)) cost++;
  } // end all decrements
  remove_edge (er.e, angelLCG);
  return cost;
} // end postrouteEdge_noJAE()

} // namespace angel

#endif // USEXAIFBOOSTER

