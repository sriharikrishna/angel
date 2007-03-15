// $Id: eliminations.cpp,v 1.12 2003/07/28 23:56:50 uwe_naumann Exp $

#include "eliminations.hpp"

#include "angel_tools.hpp"

#include "angel_io.hpp"

namespace angel {

using namespace std;
using namespace boost;

// =========================================================================
// eliminations in c-graph
// =========================================================================

// -------------------------------------------------------------------------
// elimination of a single vertex in compute graph
// -------------------------------------------------------------------------

int vertex_elimination (c_graph_t::vertex_t v, c_graph_t& cg) {
  // vector used since eliminations invalidate iterators
  vector<c_graph_t::edge_t> ev;
  c_graph_t::oei_t oei, oe_end;
  for (tie (oei, oe_end)= out_edges (v, cg); oei != oe_end; ++oei)
    ev.push_back (*oei);

  int costs= 0;
  for (size_t n= 0; n < ev.size(); n++)
    costs+= back_edge_elimination (ev[n], cg);
  // UN: print graph after elimination
  // graphviz_display(cg);
  return costs;
}

// -------------------------------------------------------------------------
// elimination of a single egde in compute graph
// -------------------------------------------------------------------------

int front_edge_elimination (c_graph_t::edge_t edge_ij, c_graph_t& cg) {
  using boost::tie;

  typedef c_graph_t::vertex_t          vertex_t;
  typedef c_graph_t::edge_t            edge_t;
  typedef c_graph_t::oei_t             oei_t;
  c_graph_t::ew_t                      ew= get(edge_weight, cg);
  boost::property_map<c_graph_t, EdgeIsUnitType>::type eUnit = get(EdgeIsUnitType(), cg);
  // write_edge_property (std::cout, "edge weights ", ew, cg);

  vertex_t i= source (edge_ij, cg), j= target (edge_ij, cg);

  if (cg.vertex_type (j) == dependent) return 0;

  int c_ji= ew[edge_ij];
  // safe edges in vector because iterators will be invalidated
  oei_t oei, oe_end;
  std::vector<edge_t> ev;
  for (tie (oei, oe_end)= out_edges (j, cg); oei != oe_end; ++oei)
    ev.push_back (*oei);

  int nnt= 0; // number of non-trivial eliminations
  for (size_t n= 0; n < ev.size(); n++) {
    edge_t edge_jk= ev[n];
    vertex_t k= target (edge_jk, cg);
    int d= c_ji * ew[edge_jk];

    bool   found_ik;
    edge_t edge_ik;
    tie (edge_ik, found_ik)= edge (i, k, cg);
  
    // test whether elimination induces op, i.e. += || *
    // nnt+= found_ik || ew[edge_jk] != 1 && c_ji != 1; 
    if (!eUnit[edge_ij]
	&&
	!eUnit[edge_jk]) 
      nnt++;
    if (found_ik) { 
      ew[edge_ik]+= d;
      eUnit[edge_ik]=false; 
    } 
    else {
      tie (edge_ik, found_ik)= add_edge (i, k, cg.next_edge_number++, cg);
      ew[edge_ik]= d; 
      if (eUnit[edge_ij]
	  &&
	  eUnit[edge_jk]) 
	eUnit[edge_ik]=true;
      else
	eUnit[edge_ik]=false;
    }
  }
  remove_edge (edge_ij, cg);

  // if ij was the last in_edge of j then all out-edges (stored in ev) become unreachable
  // targets of out-edges shall be reachable by the set of edge_ik's
  if (in_degree (j, cg) == 0)
    for (size_t n= 0; n < ev.size(); n++)
    remove_edge (ev[n], cg);
  // is overkill: remove_unreachable_edges (j, cg);

#ifdef IGNORE_TRIVIAL_ELIMINATIONS
  return nnt;
#else
  return ev.size();
#endif
}

int back_edge_elimination (c_graph_t::edge_t edge_ij, c_graph_t& cg) {
  using namespace boost;
  using boost::tie;

  typedef c_graph_t::vertex_t          vertex_t;
  typedef c_graph_t::edge_t            edge_t;
  typedef c_graph_t::iei_t             iei_t;
  c_graph_t::ew_t                      ew= get(edge_weight, cg);
  boost::property_map<c_graph_t, EdgeIsUnitType>::type eUnit = get(EdgeIsUnitType(), cg);

  vertex_t i= source (edge_ij, cg), j= target (edge_ij, cg);

  if (cg.vertex_type (i) == independent) return 0;

  int c_ji= ew[edge_ij];
  // safe edges in vector because iterators will be invalidated
  iei_t iei, ie_end;
  std::vector<edge_t> ev;
  for (tie (iei, ie_end)= in_edges (i, cg); iei != ie_end; ++iei)
    ev.push_back (*iei);

  int nnt= 0; // number of non-trivial in-edges
  for (size_t n= 0; n < ev.size(); n++) {
    edge_t edge_ki= ev[n];
    vertex_t k= source (edge_ki, cg);
    int d= c_ji * ew[edge_ki];

    bool   found_kj;
    edge_t edge_kj;
    tie (edge_kj, found_kj)= edge (k, j, cg);
  
    // test whether elimination induces op, i.e. += || *
    // nnt+= found_kj || ew[edge_ki] != 1 && c_ji != 1; 
    if (!eUnit[edge_ij]
	&&
	!eUnit[edge_ki]) 
      nnt++;

    if (found_kj) { 
      ew[edge_kj]+= d;
      eUnit[edge_kj]=false; 
    }
    else {
      tie (edge_kj, found_kj)= add_edge (k, j, cg.next_edge_number++, cg);
      ew[edge_kj]= d; 
      if (eUnit[edge_ij]
	  &&
	  eUnit[edge_ki]) 
	eUnit[edge_kj]=true;
      else
	eUnit[edge_kj]=false;

    }
  }
  remove_edge (edge_ij, cg);

  // if ij was the last out_edge of i then all in-edges (stored in ev) become irrelevant
  // except if i is a dependent vertex
  // sources of in-edges shall be relevant due to the set of edge_ik's
  if (out_degree (i, cg) == 0 && vertex_type (i, cg) != dependent)
    for (size_t n= 0; n < ev.size(); n++)
      remove_edge (ev[n], cg); 
  // is overkill: remove_irrelevant_edges (i, cg);

#ifdef IGNORE_TRIVIAL_ELIMINATIONS
  return nnt;
#else
  return ev.size();
#endif
}





// =========================================================================
// eliminations in line graph
// =========================================================================

// -------------------------------------------------------------------------
// elimination of a single vertex in line graph
// -------------------------------------------------------------------------

int vertex_elimination (int j, line_graph_t& lg) {
  vector<line_graph_t::face_t> fv;
  line_graph_t::evn_t evn= get(vertex_name, lg);
  line_graph_t::ei_t        ei, eend;
  for (tie (ei, eend)= vertices (lg); ei != eend; ++ei) 
    if (evn[*ei].second == j) {
      line_graph_t::ofi_t ofi, of_end;
      for (tie (ofi, of_end)= out_edges (*ei, lg); ofi != of_end; ++ofi) 
	fv.push_back (*ofi);
    }
  int costs= 0;
  for (size_t c= 0; c < fv.size(); c++)
    costs+= face_elimination (fv[c], lg);
  return costs;
}  

// -------------------------------------------------------------------------
// elimination of a single egde in line graph
// -------------------------------------------------------------------------

int front_edge_elimination (int i, int j, line_graph_t& lg) {
  vector<line_graph_t::edge_t>    ev;
  find_edge (i, j, lg, ev);
  int costs= 0;
  for (size_t c= 0; c < ev.size(); c++)
    costs+= front_edge_elimination (ev[c], lg);

  return costs;
}

int front_edge_elimination (line_graph_t::edge_t vij, line_graph_t& lg) { 
  std::vector<line_graph_t::face_t> fv;
  line_graph_t::ofi_t oi, oend;
  for (boost::tie (oi, oend)= out_edges (vij, lg); oi != oend; ++oi)
    fv.push_back (*oi);

  int costs= 0;
  for (size_t n= 0; n < fv.size(); n++)
    costs+= face_elimination (fv[n], lg);

  return costs;
}


int back_edge_elimination (int i, int j, line_graph_t& lg) {
  vector<line_graph_t::edge_t>    ev;
  find_edge (i, j, lg, ev);
  int costs= 0;
  for (size_t c= 0; c < ev.size(); c++)
    costs+= back_edge_elimination (ev[c], lg);
  return costs;
}

int back_edge_elimination (line_graph_t::edge_t vij,
			   line_graph_t& lg) {
  std::vector<line_graph_t::face_t> fv;
  line_graph_t::ifi_t ii, iend;
  for (boost::tie (ii, iend)= in_edges (vij, lg); ii != iend; ++ii)
    fv.push_back (*ii);

  int costs= 0;
  for (size_t n= 0; n < fv.size(); n++)
    costs+= face_elimination (fv[n], lg);

  return costs;
}

// -------------------------------------------------------------------------
// elimination of a single face in line graph
// -------------------------------------------------------------------------

int face_elimination (line_graph_t::face_t f, int kr, line_graph_t& lg, accu_graph_t& ac) {

  typedef line_graph_t::edge_t edge_t;
  edge_t                       i= source (f, lg), j= target (f, lg);
  vector<edge_t>               pi, sj, same_p, same_s, same;

  if ((int) i >= lg.v() || (int) j >= lg.v()) {
    return -1;}

  same_predecessors (i, lg, same_p); // same pred. as i
  same_successors (j, lg, same_s);
  same.resize (max (same_p.size(), same_s.size()));
  vector<edge_t>::iterator se= set_intersection (same_p.begin(), same_p.end(), same_s.begin(),
						 same_s.end(), same.begin());
  throw_debug_exception (se-same.begin() >= 2, consistency_exception,
			 "More than one mergeable vertex in face elimination"); 

  if (kr != -1) {
    if (se != same.begin()) { // if matching vertex found, it must be kr (k requested)
      if (same[0] != edge_t (kr)) return -1;
    } else {
      if (kr < lg.v()) {
	edge_t e= vertex (kr, lg);
	if (out_degree (e, lg) > 0 || in_degree (e, lg) > 0) {
	  return -1; } }
      // insert enough empty vertices
      for (; kr > lg.v();) {add_vertex (lg); ac.exp_nr.push_back (-1); }
    } }

  line_graph_t::ed_t   el= get(vertex_degree, lg);  // edge label
  int d= el[i] * el[j];

  throw_debug_exception ((int) ac.exp_nr.size() != lg.v(), consistency_exception,
			 "Array exp_nr has wrong size"); 
  edge_t k;
  if (se != same.begin()) { // absorption
    k= same[0]; el[k]+= d; 
    ac.accu_exp.resize (ac.accu_exp.size() + 1);
    ac.accu_exp[ac.accu_exp.size()-1].set_graph (k, i, j, ac.exp_nr);
    ac.exp_nr[k]= ac.accu_exp.size()-1;
  } else {                  // new or empty edge
    if (kr == -1 || kr == lg.v()) {
      k= add_vertex (lg); ac.exp_nr.push_back(-1); }
    else k= vertex (kr, lg);             // this is an empty edge

    ac.accu_exp.resize (ac.accu_exp.size() + 1);
    ac.accu_exp[ac.accu_exp.size()-1].set_graph(accu_exp_t::mult, i, j, ac.exp_nr);
    ac.exp_nr[k]= ac.accu_exp.size()-1;
    line_graph_t::evn_t evn= get(vertex_name, lg);
    // assert (evn[i].second == evn[j].first); // adjacent edges ?
    throw_debug_exception (evn[i].second != evn[j].first, consistency_exception,
			   "Adjacency corrupted in line graph"); 
    evn[k]= make_pair (evn[i].first, evn[j].second);

    sorted_predecessor_set (i, lg, pi); sorted_successor_set (j, lg, sj);
    for (size_t c= 0; c < pi.size(); c++)
      add_edge (pi[c], k, lg);
    for (size_t c= 0; c < sj.size(); c++)
      add_edge (k, sj[c], lg);
    el[k]= d;
    lg.cons_ok= false;
  }
  throw_debug_exception (kr != -1 && edge_t (kr) != k, consistency_exception,
			 "Inserted Vertex has wrong number"); 

  remove_edge (f, lg);

  if (remove_irrelevant_edges (i, lg, true) > 0) // i is isolated
    lg.cons_ok= false;
  else {
    throw_debug_exception (in_degree (i, lg) == 0 || out_degree (i, lg) == 0, consistency_exception,
			   "Undetected isolated vertex"); 
    vector<edge_t> same;
    same_neighbors (i, lg, same);
    throw_debug_exception (same.size() >= 2, consistency_exception,
			   "More than one mergeable vertex in face elimination"); 
    if (same.size() > 0) { // mergeable vertex (edge in c-graph)
      edge_t i2= same[0];
      el[i]+= el[i2];
      clear_vertex (i2, lg); 
      ac.accu_exp.resize (ac.accu_exp.size() + 1);
      ac.accu_exp[ac.accu_exp.size()-1].set_graph (accu_exp_t::add, i, i2, ac.exp_nr);
      ac.exp_nr[i]= ac.accu_exp.size()-1;
      lg.cons_ok= false;}
  }
    
  if (remove_unreachable_edges (j, lg, true) > 0)  // j is isolated
    lg.cons_ok= false;
  else {
    throw_debug_exception (in_degree (j, lg) == 0 || out_degree (j, lg) == 0, consistency_exception,
			   "Undetected isolated vertex"); 
    vector<edge_t> same;
    same_neighbors (j, lg, same);
    throw_debug_exception (same.size() >= 2, consistency_exception,
			   "More than one mergeable vertex in face elimination"); 
    if (same.size() > 0) { // mergeable vertex (edge)
      edge_t j2= same[0];
      el[j]+= el[j2];
      clear_vertex (j2, lg); 
      ac.accu_exp.resize (ac.accu_exp.size() + 1);
      ac.accu_exp[ac.accu_exp.size()-1].set_graph (accu_exp_t::add, j, j2, ac.exp_nr);
      ac.exp_nr[j]= ac.accu_exp.size()-1;
      lg.cons_ok= false; }
  }
 
  return k;
}

// =========================================================================
// which vertices, edges or faces can be eliminated
// =========================================================================

int eliminatable_vertices (const c_graph_t& cg, vector<c_graph_t::vertex_t>& vv) {
  vv.resize (0);
  c_graph_t::vi_t vi, v_end;
  for (tie(vi, v_end)= vertices(cg); vi != v_end; ++vi)
    if (cg.vertex_type (*vi) == intermediate) // only intermediate vertices can be eliminated
      vv.push_back (*vi);
  return vv.size();
}

int semi_eliminatable_vertices (const c_graph_t& cg, vector<c_graph_t::vertex_t>& vv) {
  vv.resize (0);
  c_graph_t::vi_t vi, v_end;
  for (tie(vi, v_end)= vertices(cg); vi != v_end; ++vi)
    // either intermediate or dependent with outgoing edges
    if (cg.vertex_type (*vi) == intermediate 
	|| cg.vertex_type (*vi) == dependent && out_degree (*vi, cg) > 0)
      vv.push_back (*vi);
  return vv.size();
}

int eliminatable_edges (const c_graph_t& cg, 
			std::vector<c_graph_t::edge_t>& ev) {
  // in fact it only copies the edges into a vector for better treatment
  ev.resize(0);
  c_graph_t::ei_t      ei, e_end;
  for (tie (ei, e_end)= edges (cg); ei != e_end; ++ei)
    ev.push_back (*ei);
  return ev.size();
}

int front_eliminatable_edges (const c_graph_t& cg, 
			      std::vector<c_graph_t::edge_t>& ev) {
  // in fact it only copies the edges into a vector for better treatment
  ev.resize(0);
  c_graph_t::ei_t      ei, e_end;
  for (tie (ei, e_end)= edges (cg); ei != e_end; ++ei)
    if (vertex_type (target (*ei, cg), cg) != dependent)
      ev.push_back (*ei);
  return ev.size();
}

int back_eliminatable_edges (const c_graph_t& cg, 
			     std::vector<c_graph_t::edge_t>& ev) {
  // in fact it only copies the edges into a vector for better treatment
  ev.resize(0);
  c_graph_t::ei_t      ei, e_end;
  for (tie (ei, e_end)= edges (cg); ei != e_end; ++ei)
    if (vertex_type (source (*ei, cg), cg) != independent)
      ev.push_back (*ei);
  return ev.size();
}

int eliminatable_edges (const c_graph_t& cg,
			std::vector<edge_bool_t>& ev) {
  ev.resize(0);
  c_graph_t::ei_t      ei, e_end;
  for (tie (ei, e_end)= edges (cg); ei != e_end; ++ei) {
    // can edge be back-eliminated ?
    if (vertex_type (source (*ei, cg), cg) != independent)
      ev.push_back (std::pair<c_graph_t::edge_t,bool> (*ei, false)); 
    // can edge be front-eliminated ?
    if (vertex_type (target (*ei, cg), cg) != dependent)
      ev.push_back (std::pair<c_graph_t::edge_t,bool> (*ei, true)); 
  }
  return ev.size();
}

int eliminatable_edges (const c_graph_t& cg,
                        std::vector<edge_ij_elim_t>& ev) {
  ev.resize(0);
  c_graph_t::ei_t      ei, e_end;
  for (tie (ei, e_end)= edges (cg); ei != e_end; ++ei) {
    edge_ij_elim_t ee (source (*ei, cg), target (*ei, cg), false);
    // can edge be back-eliminated ?
    if (vertex_type (source (*ei, cg), cg) != independent)
      ev.push_back (ee); 
    // can edge be front-eliminated ?
    if (vertex_type (target (*ei, cg), cg) != dependent) {
      ee.front= true; ev.push_back (ee); } 
  }
  return ev.size();
}

int eliminatable_faces (const line_graph_t& lg, 
			std::vector<line_graph_t::face_t>& fv) {
  // in fact it only copies the edges into a vector for better treatment
  fv.resize(0);
  graph_traits<line_graph_t>::edge_iterator      ei, e_end;
  for (tie (ei, e_end)= edges (lg); ei != e_end; ++ei) {
    line_graph_t::vertex_descriptor s= source (*ei, lg), t= target (*ei, lg);
    if (vertex_type (s, lg) != independent && vertex_type (t, lg) != dependent)
      fv.push_back (*ei);
  }
  return fv.size();
}

bool convert_elimination_sequence (const vector<c_graph_t::vertex_t>& vv, 
				   const c_graph_t& cg,
				   vector<edge_ij_elim_t>& ev) {
  c_graph_t cgc (cg);
  ev.resize (0);
  for (size_t c= 0; c < vv.size(); c++) {
    c_graph_t::iei_t  iei, ie_end;
    // cout << "conv_elim_seq: eliminate vertex " << vv[c];
    // write_graph ("from graph", cgc);
    for (tie (iei, ie_end)= in_edges (vv[c], cgc); iei != ie_end; ++iei) {
      edge_ij_elim_t ee (source (*iei, cgc), target (*iei, cgc), true);
      // cout << "new edge " << ee;
      ev.push_back (ee); }
    // cout << endl;
    vertex_elimination (vv[c], cgc); }
  return true;
}

bool convert_elimination_sequence (const vector<edge_ij_elim_t>& ev, 
				   const line_graph_t& lg,
				   vector<triplet_t>& tv) {
  line_graph_t lgc (lg);
  tv.resize (0);
  for (size_t c= 0; c < ev.size(); c++) {
    edge_ij_elim_t ee = ev[c];
    vector<line_graph_t::edge_t> lev;
    line_graph_t::edge_t ledge;

#ifndef NDEBUG
    cout << endl;
    cout << "convert_elimination_sequence: eliminate edge " << ee;
    write_graph ("from line graph: ", lgc);
    line_graph_t::evn_t evn = get(vertex_name, lgc);
    write_vertex_property (cout, "Labels of vertices in this line graph: ", evn, lgc);
#endif

    bool found = find_edge (ee.i, ee.j, lgc, lev);
    throw_exception (!found || lev.empty(), consistency_exception, "LCG edge has no corresponding line graph node");

    if (lev.size() == 1) { ledge = lev[0]; }
    else { // if lev.size() != 1
      cout << lev.size() << " line graph nodes correspond to LCG edge (" << ee.i << ", " << ee.j << ")."
			 << "  Determining the correct one...";
      vector<line_graph_t::edge_t> candidates;
      // iterate through corresponding line graph vertices to ensure only one of them isn't isolated
      for (size_t l = 0; l < lev.size(); l++) {
        if (in_degree(lev[l], lgc) > 0 || out_degree(lev[l], lgc) > 0) candidates.push_back(lev[l]);
      }
      throw_exception (candidates.empty(), consistency_exception, "all corresponding line graph nodes are isolated");
      throw_exception (candidates.size() > 1, consistency_exception, "multiple non-isolated corresponding line graph nodes");

      cout << " Unique correlation found!\n";
      ledge = candidates[0];
    } // end lev.size() != 1

    if (ee.front) {
      line_graph_t::ofi_t oi, oend;
      for (boost::tie (oi, oend) = out_edges (ledge, lgc); oi != oend; ++oi) {
        triplet_t t (ledge, target (*oi, lgc), -1); tv.push_back (t);
#ifndef NDEBUG
        cout << "new face " << t;
#endif
      }
      front_edge_elimination (ee.i, ee.j, lgc);
    } else {
      line_graph_t::ifi_t ii, iend;
      for (boost::tie (ii, iend) = in_edges (ledge, lgc); ii != iend; ++ii) {
        triplet_t t (source (*ii, lgc), ledge, -1); tv.push_back (t);
#ifndef NDEBUG
        cout << "new face " << t;
#endif
      }
      back_edge_elimination (ee.i, ee.j, lgc); }
  } // end all edge eliminations
  return true;
} // end convert_elimination_sequence()

} // namespace angel

