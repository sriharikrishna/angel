// $Id: heuristics.cpp,v 1.10 2005/03/22 05:08:40 jean_utke Exp $

#include "heuristics.hpp"

#include <limits.h>
#include <algorithm>

#include "angel_exceptions.hpp"
#include "angel_tools.hpp"

namespace angel {

using namespace std;
using namespace boost;

// =====================================================
// for vertex elimination
// =====================================================

int forward_mode_vertex_t::operator() (const vector<c_graph_t::vertex_t>& vv1,
				       const c_graph_t& cg, 
				       vector<c_graph_t::vertex_t>& vv2) {
  vv2.resize (0);
  if (vv1.size() == 0) {set_empty_objective (); return 0; }
  vv2.push_back (vv1[0]);

  for (size_t c= 1; c < vv1.size(); c++) 
    if (vv1[c] < vv2[0]) vv2[0]= vv1[c];
  set_objective (vv2[0]);
  return 1;
}

forward_mode_vertex_t forward_mode_vertex;

// -------------------------------------------------------------------------
// reverse mode
// -------------------------------------------------------------------------

int reverse_mode_vertex_t::operator() (const vector<c_graph_t::vertex_t>& vv1,
				       const c_graph_t& cg, 
				       vector<c_graph_t::vertex_t>& vv2) {
  vv2.resize (0);
  if (vv1.size() == 0) {set_empty_objective (); return 0; }
  vv2.push_back (vv1[0]);

  for (size_t c= 1; c < vv1.size(); c++)
    if (vv1[c] > vv2[0]) vv2[0]= vv1[c];
  set_objective (vv2[0]);
  return 1;
}

reverse_mode_vertex_t reverse_mode_vertex;

// -------------------------------------------------------------------------
// Lowest Markowitz 
// -------------------------------------------------------------------------

// operator for lowest Markowitz on vertices 
struct lmv_op_t {
  int operator() (c_graph_t::vertex_t v, const c_graph_t& cg) {
    return in_degree (v, cg) * out_degree (v, cg); }
};

int lowest_markowitz_vertex_t::operator() (const vector<c_graph_t::vertex_t>& vv1,
					   const c_graph_t& cg, 
					   vector<c_graph_t::vertex_t>& vv2) {
  lmv_op_t   lmv_op;
  return standard_heuristic_op (vv1, cg, vv2, lmv_op, *this);
}

lowest_markowitz_vertex_t lowest_markowitz_vertex;

// -------------------------------------------------------------------------
// Lowest relative Markowitz
// -------------------------------------------------------------------------

// operator for lowest relative Markowitz on vertices and edges
struct lrm_op_t {
  vector<int> indep, dep;
  lrm_op_t (const c_graph_t& cg) : indep (num_vertices (cg)), dep (num_vertices (cg)) {
    number_independent_vertices (cg, indep); number_dependent_vertices (cg, dep); }
  int operator() (bool front, c_graph_t::edge_t edge, const c_graph_t& cg) {
    return front ? out_degree (target (edge, cg), cg) - dep[target (edge, cg)]
                 : in_degree (source (edge, cg), cg) - indep[source (edge, cg)]; }
  int operator() (edge_bool_t eb, const c_graph_t& cg) {
    return eb.second ? out_degree (target (eb.first, cg), cg) - dep[target (eb.first, cg)]
                     : in_degree (source (eb.first, cg), cg) - indep[source (eb.first, cg)]; }
  int operator() (c_graph_t::vertex_t v, const c_graph_t& cg) {
    return in_degree (v, cg) * out_degree (v, cg) - indep[v] * dep[v]; }
};

int lowest_relative_markowitz_vertex_t::operator() (const vector<c_graph_t::vertex_t>& vv1,
						    const c_graph_t& cg, 
						    vector<c_graph_t::vertex_t>& vv2) {
  lrm_op_t   lrm_op (cg);
  return standard_heuristic_op (vv1, cg, vv2, lrm_op, *this);
}

lowest_relative_markowitz_vertex_t lowest_relative_markowitz_vertex;

// -------------------------------------------------------------------------
// subroutine of Lowest fill-in
// -------------------------------------------------------------------------

// how many new in_edges has j:target(e) by back-eliminating e
int new_in_edges (c_graph_t::edge_t e, const c_graph_t& cg) {

  typedef c_graph_t::vertex_t        vertex_t;
  typedef c_graph_t::iei_t           iei_t;

  iei_t    siei, sie_end, tiei, tie_end;
  tie (siei, sie_end)= in_edges (source (e, cg), cg);
  tie (tiei, tie_end)= in_edges (target (e, cg), cg);
  int new_edges= 0;

  vector<vertex_t> nsl; // list of new sources to check double insertions

  for (; siei != sie_end; ++siei) {
    vertex_t ss= source (*siei, cg);
    iei_t i= tiei;
    for (; i != tie_end; ++i)
      if (source (*i, cg) == ss) break;
    if (i == tie_end
	&& find (nsl.begin(), nsl.end(), ss) == nsl.end()) {
      nsl.push_back (ss); new_edges++; }
  }

  return new_edges;
}

// how many new out_edges has j:=source(e) by front-eliminating e
int new_out_edges (c_graph_t::edge_t e, const c_graph_t& cg) {

  typedef c_graph_t::vertex_t        vertex_t;
  typedef c_graph_t::oei_t           oei_t;

  oei_t    soei, soe_end, toei, toe_end;
  tie (soei, soe_end)= out_edges (source (e, cg), cg);
  tie (toei, toe_end)= out_edges (target (e, cg), cg);
  int new_edges= 0;

  vector<vertex_t> ntl; // list of new targets to check double insertions

  for (; toei != toe_end; ++toei) {
    vertex_t tt= target (*toei, cg);
    oei_t i= soei;
    for (; i != soe_end; ++i)
      if (target (*i, cg) == tt) break;
    if (i == soe_end
	&& find (ntl.begin(), ntl.end(), tt) == ntl.end()) {
      ntl.push_back (tt); new_edges++; }
  }

  return new_edges;
}


// -------------------------------------------------------------------------
// Lowest fill-in
// -------------------------------------------------------------------------


// operator for lowest fill-in on vertices 
struct fiv_op_t {
  int operator() (c_graph_t::vertex_t v, const c_graph_t& cg) {
    int                  fill_ins= 0;
    c_graph_t::iei_t     iei, ie_end;
    for (tie (iei, ie_end)= in_edges (v, cg); iei != ie_end; ++iei)
      fill_ins+= new_out_edges (*iei, cg);
    return fill_ins; }
};

int lowest_fill_in_vertex_t::operator() (const vector<c_graph_t::vertex_t>& vv1,
					 const c_graph_t& cg, 
					 vector<c_graph_t::vertex_t>& vv2) {
  fiv_op_t   fiv_op;
  return standard_heuristic_op (vv1, cg, vv2, fiv_op, *this);
}

lowest_fill_in_vertex_t lowest_fill_in_vertex;

// -------------------------------------------------------------------------
// subroutines of LMMD MOMR
// -------------------------------------------------------------------------

// how much the markowitz degree of j:=source(e) is enlarged by front-eliminating e
// this is in_degree(j) * #new out_edges(j) 
int markowitz_enlargement_front (c_graph_t::edge_t e, const c_graph_t& cg,
				 bool eliminate_parallel_edges= false) {
  int ee= 0; // number of eliminated edges
  c_graph_t::vertex_t s= source (e, cg), t= target (e, cg);
  if (vertex_type (t, cg) == intermediate) // if dependent edges are not eliminated
    if (eliminate_parallel_edges) {
      c_graph_t::oei_t soei, soe_end;
      for (tie (soei, soe_end)= out_edges (s, cg); soei != soe_end; soei++)
	ee+= target (*soei, cg) == t;
    } else ee= 1;

  return in_degree (source (e, cg), cg) * (new_out_edges (e, cg) - ee);
}

// how much is the markowitz degree of j:=target(e2) enlarged by front-eliminating e
int markowitz_enlargement_front (c_graph_t::edge_t e, c_graph_t::edge_t e2, 
				 const c_graph_t& cg) {

  throw_debug_exception (target (e, cg) != source (e2, cg), consistency_exception,
			 "e and e2 does not match"); 

  c_graph_t::vertex_t j= target (e2, cg), se= source (e, cg), te= target (e, cg);

  // if e is last in_edge of te than e2 will be eliminated -> j has one in_edge less
  // int in_edge_change= in_degree (te, cg) == 1 ? -1 : 0; 

  // if e is last in_edge of te than e2 and its parallel edges will be eliminated 
  // -> j has one or more in_edges less
  int in_edge_change= in_degree (te, cg) == 1 ? - count_parallel_edges (e2, cg) : 0; 

  // if source(e) is not source of an in_edge of j -> j has one in_edge more
  c_graph_t::iei_t  iei, ie_end;
  for (tie (iei, ie_end)= in_edges (j, cg); iei != ie_end; ++iei)
    if (source (*iei, cg) == se) break;
  if (iei == ie_end) in_edge_change++;

  return in_edge_change * out_degree (j, cg);
}

// how much the markowitz degree of j:=target(e) is enlarged by back-eliminating e
// this is out_degree(j) * #new in_edges(j) 
int markowitz_enlargement_back (c_graph_t::edge_t e, const c_graph_t& cg,
				bool eliminate_parallel_edges= false) {

  int ee= 0; // number of eliminated edges
  if (eliminate_parallel_edges) {
    c_graph_t::vertex_t s= source (e, cg), t= target (e, cg);
    c_graph_t::iei_t tiei, tie_end;
    for (tie (tiei, tie_end)= in_edges (t, cg); tiei != tie_end; ++tiei)
      ee+= source (*tiei, cg) == s;
  } else ee= 1;

  return out_degree (target (e, cg), cg) * (new_in_edges (e, cg) - ee);
}

// how much is the markowitz degree of j:=source(e2) enlarged by back-eliminating e
int markowitz_enlargement_back (c_graph_t::edge_t e, c_graph_t::edge_t e2, 
				const c_graph_t& cg) {

  // assert (source (e, cg) == target (e2, cg));
  throw_debug_exception (source (e, cg) != target (e2, cg), consistency_exception,
			 "e and e2 does not match"); 

  c_graph_t::vertex_t j= source (e2, cg), se= source (e, cg), te= target (e, cg);

  // if e is last out_edge of se than e2 will be eliminated -> j has one out_edge less
  int out_edge_change= out_degree (se, cg) == 1 ? -1 : 0; 

  // if target(e) is not target of an out_edge of j -> j has one out_edge more
  c_graph_t::oei_t    oei, oe_end;
  for (tie (oei, oe_end)= out_edges (j, cg); oei != oe_end; ++oei)
    if (target (*oei, cg) == te) break;
  if (oei == oe_end) out_edge_change++;

  return out_edge_change * in_degree (j, cg);
}

// how much is the markowitz degree of all neighbors of v increased by its elimination
// multiply occurred neighbors are counted only once
int markowitz_enlargement_all_neighbors (c_graph_t::vertex_t v, const c_graph_t& cg) {

  using namespace std;

  typedef c_graph_t::vertex_t              vertex_t;

  int enl= 0;

  // parallel edges does not cause multiple Markowitz changes
  vector<vertex_t> cv; // already checked vertices
  cv.reserve (10);     // reduce mallocs

  c_graph_t::iei_t     iei, ie_end;
  tie (iei, ie_end)= in_edges (v, cg);
  for (; iei != ie_end; ++iei) {
    vertex_t v= source (*iei, cg);
    if (find (cv.begin(), cv.end(), v) == cv.end()) {
      enl+= markowitz_enlargement_front (*iei, cg, true);
      cv.push_back (v); } }

  cv.resize (0);             // reduce search space
  c_graph_t::oei_t     oei, oe_end;
  tie (oei, oe_end)= out_edges (v, cg);
  for (; oei != oe_end; ++oei) {
    vertex_t v= target (*oei, cg);    
    if (find (cv.begin(), cv.end(), v) == cv.end()) {
      enl+= markowitz_enlargement_back (*oei, cg, true);
      cv.push_back (v); } }
  return enl;
}

struct markowitz_enlargement_front_t {
  c_graph_t::edge_t _e;                  // first edge is stored
  markowitz_enlargement_front_t (c_graph_t::edge_t e) : _e (e) {}
  int operator() (c_graph_t::edge_t e2, const c_graph_t& cg) const {
    return markowitz_enlargement_front (_e, e2, cg); }
};

struct markowitz_enlargement_back_t {
  c_graph_t::edge_t _e;                  // first edge is stored
  markowitz_enlargement_back_t (c_graph_t::edge_t e) : _e (e) {}
  int operator() (c_graph_t::edge_t e2, const c_graph_t& cg) const {
    return markowitz_enlargement_back (_e, e2, cg); }
};


// -------------------------------------------------------------------------
// LMMD
// -------------------------------------------------------------------------

// operator that computes LMMD value for a single vertex
struct lmmdv_op_t {
  double w; // weight
  lmmdv_op_t (double _w) : w (_w) {}
  int operator() (c_graph_t::vertex_t v, const c_graph_t& cg) {
    int markowitz= in_degree (v, cg) * out_degree (v, cg),
      damage= markowitz_enlargement_all_neighbors (v, cg);
    return int (double (markowitz) + w * double (damage)); }
};

int lmmd_vertex_t::operator() (const vector<c_graph_t::vertex_t>& vv1,
			       const c_graph_t& cg, 
			       vector<c_graph_t::vertex_t>& vv2) {
  lmmdv_op_t      lmmdv_op (weight);
  return standard_heuristic_op (vv1, cg, vv2, lmmdv_op, *this);
}
  
lmmd_vertex_t lmmd_vertex (1.0);

// -------------------------------------------------------------------------
// MOMR
// -------------------------------------------------------------------------

// operator that computes MOMR value for a single vertex
struct momrv_op_t {
  int operator() (c_graph_t::vertex_t v, const c_graph_t& cg) {
    int momr= in_degree (v, cg) * out_degree (v, cg)
              - markowitz_enlargement_all_neighbors (v, cg);
#ifndef NDEBUG
    c_graph_t         gtmp (cg);  vertex_elimination (v, gtmp);
    throw_debug_exception (overall_markowitz_degree (cg) - overall_markowitz_degree (gtmp) != momr, 
			   consistency_exception, "momr not correct"); 
#endif
    return momr; }
};

int momr_vertex_t::operator() (const vector<c_graph_t::vertex_t>& vv1,
			       const c_graph_t& cg, 
			       vector<c_graph_t::vertex_t>& vv2) {
  momrv_op_t      momrv_op;
  return standard_heuristic_op (vv1, cg, vv2, momrv_op, *this);
}

momr_vertex_t momr_vertex;

// -------------------------------------------------------------------------
// subroutines of Maximal overall path length reduction
// -------------------------------------------------------------------------

// overall path length reduction of face (e1, e2)
inline int oplr_face (c_graph_t::edge_t e1, c_graph_t::edge_t e2,
		      const vector<int>& vni, const vector<int>& vli, 
		      const vector<int>& vno, const vector<int>& vlo, 
		      const c_graph_t& cg) {

  // assert (target (e1, cg) == source (e2, cg));
  throw_debug_exception (target (e1, cg) != source (e2, cg), consistency_exception,
			 "e1 and e2 does not match"); 

  c_graph_t::vertex_t p= source (e1, cg), s= target (e2, cg);

  c_graph_t::edge_t e;
  bool found;
  boost::tie (e, found)= edge (p, s, cg);

  return found ? vno[s] * (vni[p] + vli[p]) + vni[p] * (vno[s] + vlo[s])
               : vni[p] * vno[s];
}

int oplr_edge_front (c_graph_t::edge_t e,
		     const vector<int>& vni, const vector<int>& vli, 
		     const vector<int>& vno, const vector<int>& vlo, 
		     const c_graph_t& cg) {

  int oplr= 0;
  graph_traits<c_graph_t>::out_edge_iterator    oei, oe_end;
  tie (oei, oe_end)= out_edges (target (e, cg), cg);

  for (; oei != oe_end; ++oei)
    oplr+= oplr_face (e, *oei, vni, vli, vno, vlo, cg);

  return oplr;
}

int oplr_edge_back (c_graph_t::edge_t e,
		    const vector<int>& vni, const vector<int>& vli, 
		    const vector<int>& vno, const vector<int>& vlo, 
		    const c_graph_t& cg) {

  int oplr= 0;
  graph_traits<c_graph_t>::in_edge_iterator    iei, ie_end;
  tie (iei, ie_end)= in_edges (source (e, cg), cg);

  for (; iei != ie_end; ++iei)
    oplr+= oplr_face (*iei, e, vni, vli, vno, vlo, cg);

  return oplr;
}

// -------------------------------------------------------------------------
// Maximal overall path length reduction
// -------------------------------------------------------------------------

// operator that computes path length reduction for a single vertex
struct oplrv_op_t {
  vector<int> vni, vli, vno, vlo;
  oplrv_op_t (const c_graph_t& cg) {
    in_out_path_lengths (cg, vni, vli, vno, vlo); }
  int operator () (c_graph_t::vertex_t v, const c_graph_t& cg) {
    int oplr= 0;
    c_graph_t::iei_t    iei, ie_end;
    for (tie (iei, ie_end)= in_edges (v, cg); iei != ie_end; ++iei)
      oplr+= oplr_edge_front (*iei, vni, vli, vno, vlo, cg);
    return oplr; }
};

int moplr_vertex_t::operator() (const vector<c_graph_t::vertex_t>& vv1,
				const c_graph_t& cg, 
				vector<c_graph_t::vertex_t>& vv2) {
  oplrv_op_t oplrv_op (cg);
  return standard_heuristic_op (vv1, cg, vv2, oplrv_op, *this);
}

moplr_vertex_t moplr_vertex;

// =====================================================
// for edge elimination (in c-graph)
// =====================================================

int forward_mode_edge_f (const vector<c_graph_t::edge_t>& ev1,
			 bool front,
			 const c_graph_t& cg,
			 vector<c_graph_t::edge_t>& ev2) {
  ev2.resize (0);

  if (ev1.size() == 0) return 0;
  ev2.push_back (ev1[0]);

  for (size_t c= 1; c < ev1.size(); c++)
    if (front ? inv_lex_less (ev1[c], ev2[0], cg) : lex_less (ev1[c], ev2[0], cg)) 
      ev2[0]= ev1[c];

  return 1;
}

// objective function for forward mode in edge elimination
// works up to 47 million vertices in IEEE arithmetic
inline double fme_obj (edge_bool_t eb, const c_graph_t& cg) {
  c_graph_t::edge_t   edge= eb.first;
  // front is prefered -> add something if not front because we minimize
  int high, low, notfront;
  if (eb.second) high= target (edge, cg), low= source (edge, cg), notfront= 0;
  else high= source (edge, cg), low= target (edge, cg), notfront= 1;
  return (2 * high + notfront) * double (cg.x()) + low;
}

int forward_mode_edge_t::operator() (const vector<edge_bool_t>& ev1,
				     const c_graph_t& cg,
				     vector<edge_bool_t>& ev2) {
  ev2.resize (0);
  if (ev1.size() == 0) {set_empty_objective (); return 0; }
  ev2.push_back (ev1[0]);

  for (size_t c= 1; c < ev1.size(); c++) {
    throw_debug_exception (fme_obj (ev1[c], cg) < fme_obj (ev2[0], cg) != lex_less (ev1[c], ev2[0], cg),
			   consistency_exception, "objective function and comparator does not match");
    if (lex_less (ev1[c], ev2[0], cg)) ev2[0]= ev1[c]; }
  set_objective (fme_obj (ev2[0], cg));
  return 1;
}

forward_mode_edge_t forward_mode_edge;

// remark fm: if all eliminatable edges are considered than only front elimination is used
//            this way one can force same sequences in vertex, edge and face elimination
//            when forward mode is used as sole criterion

// -------------------------------------------------------------------------
// reverse mode
// -------------------------------------------------------------------------

int reverse_mode_edge_f (const vector<c_graph_t::edge_t>& ev1,
			 bool front,
			 const c_graph_t& cg,
			 vector<c_graph_t::edge_t>& ev2) {
  ev2.resize (0);

  if (ev1.size() == 0) return 0;
  ev2.push_back (ev1[0]);

  for (size_t c= 1; c < ev1.size(); c++)
    if (front ? inv_lex_greater (ev1[c], ev2[0], cg) : lex_greater (ev1[c], ev2[0], cg)) 
      ev2[0]= ev1[c];

  return 1;
}

// objective function for reverse mode in edge elimination
// works up to 47 million vertices in IEEE arithmetic
inline double rme_obj (edge_bool_t eb, const c_graph_t& cg) {
  c_graph_t::edge_t   edge= eb.first;
  // front is prefered -> add something if front because we maximize
  int high, low, front;
  if (eb.second) high= target (edge, cg), low= source (edge, cg), front= 1;
  else high= source (edge, cg), low= target (edge, cg), front= 0;
  return (2 * high + front) * double (cg.x()) + low;
}

int reverse_mode_edge_t::operator() (const vector<edge_bool_t>& ev1,
				     const c_graph_t& cg,
				     vector<edge_bool_t>& ev2) {
  ev2.resize (0);

  if (ev1.size() == 0) {set_empty_objective (); return 0; }
  ev2.push_back (ev1[0]);

  for (size_t c= 1; c < ev1.size(); c++) {
    throw_debug_exception ((rme_obj (ev1[c], cg) > rme_obj (ev2[0], cg)) != lex_greater (ev1[c], ev2[0], cg),
			   consistency_exception, "objective function and comparator does not match");
    if (lex_greater (ev1[c], ev2[0], cg)) ev2[0]= ev1[c]; }
    set_objective (rme_obj (ev2[0], cg));
  return 1;
}

reverse_mode_edge_t reverse_mode_edge;

// remark rm: if all eliminatable edges are considered than only front elimination is used
//            this way one can force same sequences in vertex, edge and face elimination
//            when reverse mode is used as sole criterion

// -------------------------------------------------------------------------
// Lowest Markowitz
// -------------------------------------------------------------------------

int lowest_markowitz_edge_f (const vector<c_graph_t::edge_t>& ev1,
			     bool front,
			     const c_graph_t& cg,
			     vector<c_graph_t::edge_t>& ev2) {
  ev2.resize (0);

  if (ev1.size() == 0) return 0;
  int min_degree= front ? out_degree (target (ev1[0], cg), cg)
                        : in_degree (source (ev1[0], cg), cg);
  ev2.push_back (ev1[0]);

  for (size_t c= 1; c < ev1.size(); c++) {
    c_graph_t::edge_t e= ev1[c];
    int degree= front ? out_degree (target (e, cg), cg)
                      : in_degree (source (e, cg), cg);
    if (degree < min_degree) ev2.resize (0);
    if (degree <= min_degree) {
      ev2.push_back (e); min_degree= degree;}
  }
  return ev2.size();
}

// operator that computes the Markowitz degree for a single edge elimination
struct lme_op_t {
  int operator() (edge_bool_t eb, const c_graph_t& cg) {
    return eb.second ? out_degree (target (eb.first, cg), cg)
                     : in_degree (source (eb.first, cg), cg); }
};

int lowest_markowitz_edge_t::operator() (const vector<edge_bool_t>& ev1,
					 const c_graph_t& cg,
					 vector<edge_bool_t>& ev2) {
  lme_op_t      lme_op;
  return standard_heuristic_op (ev1, cg, ev2, lme_op, *this);
}

// -------------------------------------------------------------------------
// Lowest relative Markowitz
// -------------------------------------------------------------------------

int lowest_relative_markowitz_edge_f (const vector<c_graph_t::edge_t>& ev1,
				      bool front,
				      const c_graph_t& cg,
				      vector<c_graph_t::edge_t>& ev2) {
  ev2.resize (0);
  if (ev1.size() == 0) return 0;
  lrm_op_t   lrm_op (cg);
  int min_degree= lrm_op (front, ev1[0], cg);
  ev2.push_back (ev1[0]);

  for (size_t c= 1; c < ev1.size(); c++) {
    int degree= lrm_op (front, ev1[c], cg); 
    if (degree < min_degree) ev2.resize (0);
    if (degree <= min_degree) {
      ev2.push_back (ev1[c]); min_degree= degree;} }
  return ev2.size();
}

int lowest_relative_markowitz_edge_t::operator() (const vector<edge_bool_t>& ev1,
						  const c_graph_t& cg,
						  vector<edge_bool_t>& ev2) {
  lrm_op_t   lrm_op (cg);
  return standard_heuristic_op (ev1, cg, ev2, lrm_op, *this);
}

lowest_relative_markowitz_edge_t lowest_relative_markowitz_edge;

// -------------------------------------------------------------------------
// Lowest fill-in
// -------------------------------------------------------------------------

inline int fill_in_front (c_graph_t::edge_t e, const c_graph_t& cg) {
  return new_out_edges (e, cg);
}

inline int fill_in_back (c_graph_t::edge_t e, const c_graph_t& cg) {
  return new_in_edges (e, cg);
}


int lowest_fill_in_edge_f (const vector<c_graph_t::edge_t>& ev1,
			   bool front,
			   const c_graph_t& cg,
			   vector<c_graph_t::edge_t>& ev2) {
  ev2.resize (0);

  if (ev1.size() == 0) return 0;
  int min_degree= front ? fill_in_front (ev1[0], cg)
                        : fill_in_back (ev1[0], cg);
  ev2.push_back (ev1[0]);

  for (size_t c= 1; c < ev1.size(); c++) {
    c_graph_t::edge_t e= ev1[c];
    int degree= front ? fill_in_front (e, cg)
                      : fill_in_back (e, cg);
    if (degree < min_degree) ev2.resize (0);
    if (degree <= min_degree) {
      ev2.push_back (e); min_degree= degree;}
  }

  return ev2.size();
}


// -------------------------------------------------------------------------
// LMMD
// -------------------------------------------------------------------------

lmmd_edge_t lmmd_edge (1.0);

inline int lmmd_edge_front (c_graph_t::edge_t e, double w, const c_graph_t& cg) {
  int markowitz= out_degree (target (e, cg), cg); 
  markowitz_enlargement_front_t me (e);
  int damage= markowitz_enlargement_front (e, cg)
              + sum_over_all_out_edges (target (e, cg), cg, me);
  return int (double (markowitz) + w * double (damage));
}

inline int lmmd_edge_back (c_graph_t::edge_t e, double w, const c_graph_t& cg) {
  int markowitz= in_degree (source (e, cg), cg);
  markowitz_enlargement_back_t me (e);
  int damage= markowitz_enlargement_back (e, cg)
              + sum_over_all_in_edges (source (e, cg), cg, me);
  return int (double (markowitz) + w * double (damage));
}

struct lmmde_op_t {
  double w; // weight
  lmmde_op_t (double _w) : w (_w) {}
  int operator() (edge_bool_t eb, const c_graph_t& cg) {
    return eb.second ? lmmd_edge_front (eb.first, w, cg)
                     : lmmd_edge_back (eb.first, w, cg); }
};

int lmmd_edge_t::operator() (const vector<edge_bool_t>& ev1,
			     const c_graph_t& cg,
			     vector<edge_bool_t>& ev2) {
  lmmde_op_t      lmmde_op (weight);
  return standard_heuristic_op (ev1, cg, ev2, lmmde_op, *this);
}


// -------------------------------------------------------------------------
// MOMR
// -------------------------------------------------------------------------

inline int momr_edge_front (c_graph_t::edge_t e, const c_graph_t& cg) {

  markowitz_enlargement_front_t me (e);
  int momr= out_degree (target (e, cg), cg) - markowitz_enlargement_front (e, cg)
           - sum_over_all_out_edges (target (e, cg), cg, me);

#ifndef NDEBUG
  c_graph_t         gtmp (cg);

  // eliminating e in gtmp does not work -> edge_descriptor from gtmp needed
  c_graph_t::edge_t   etmp;
  c_graph_t::ei_t     ei, e_end;
  c_graph_t::vertex_t s= source (e, cg), t= target (e, cg);
  for (boost::tie (ei, e_end)= edges (gtmp); ei != e_end; ++ei)
    if (source (*ei, gtmp) == s && target (*ei, gtmp) == t) {
      etmp= *ei; break; }
  // assert (ei != e_end); // otherwise edge not found
  throw_debug_exception (ei == e_end, consistency_exception, "No matching edge found"); 

  front_edge_elimination (etmp, gtmp);
  // assert (overall_markowitz_degree (cg) - overall_markowitz_degree (gtmp) == momr);
  throw_debug_exception (overall_markowitz_degree (cg) - overall_markowitz_degree (gtmp) != momr, 
			 consistency_exception, "momr not correct"); 
#endif
  return momr;
}

inline int momr_edge_back (c_graph_t::edge_t e, const c_graph_t& cg) {
  // reduction of markowitz degree in vertex source (e)
  int momr= in_degree (source (e, cg), cg);
  // target (e) can get a larger markowitz degree due to new in_edges
  momr-= markowitz_enlargement_back (e, cg);

  // the predecessors of source (e) can get a larger markowitz degree
  // due to a new out_edge to target (e)
  c_graph_t::iei_t    iei, ie_end;
  tie (iei, ie_end)= in_edges (source (e, cg), cg);
  for (; iei != ie_end; ++iei)
    momr-= markowitz_enlargement_back (e, *iei, cg);
#ifndef NDEBUG
  markowitz_enlargement_back_t me (e);
  int momr2= in_degree (source (e, cg), cg) - markowitz_enlargement_back (e, cg)
            - sum_over_all_in_edges (source (e, cg), cg, me);
  // assert (momr == momr2);
  throw_debug_exception (momr2 != momr, consistency_exception, "momr not correct"); 

  c_graph_t         gtmp (cg);
  c_graph_t::vi_t   vi, v_end;
  int old_overall_markowitz= 0, new_overall_markowitz= 0;
  for (boost::tie (vi, v_end)= vertices (gtmp); vi != v_end; ++vi)
    old_overall_markowitz+= in_degree (*vi, gtmp) * out_degree (*vi, gtmp);

  // eliminating e in gtmp does not work -> edge_descriptor from gtmp needed
  c_graph_t::edge_t   etmp;
  c_graph_t::ei_t     ei, e_end;
  c_graph_t::vertex_t s= source (e, cg), t= target (e, cg);
  for (boost::tie (ei, e_end)= edges (gtmp); ei != e_end; ++ei)
    if (source (*ei, gtmp) == s && target (*ei, gtmp) == t) {
      etmp= *ei; break; }
  // assert (ei != e_end); // otherwise edge not found
  throw_debug_exception (ei == e_end, consistency_exception, "No matching edge found"); 

  back_edge_elimination (etmp, gtmp);
  for (boost::tie (vi, v_end)= vertices (gtmp); vi != v_end; ++vi)
    new_overall_markowitz+= in_degree (*vi, gtmp) * out_degree (*vi, gtmp);
  // assert (old_overall_markowitz-new_overall_markowitz == momr);
  throw_debug_exception (old_overall_markowitz-new_overall_markowitz != momr, 
			 consistency_exception, "momr not correct"); 
#endif
  return momr;
}

// operator for MOMR on edges
struct momre_op_t {
  int operator() (bool front, c_graph_t::edge_t edge, const c_graph_t& cg) {
    return front ? momr_edge_front (edge, cg) : momr_edge_back (edge, cg); }
  int operator() (edge_bool_t eb, const c_graph_t& cg) {
    return eb.second ? momr_edge_front (eb.first, cg) : momr_edge_back (eb.first, cg); }
};

int momr_edge_f (const vector<c_graph_t::edge_t>& ev1,
		 bool front,
		 const c_graph_t& cg,
		 vector<c_graph_t::edge_t>& ev2) {
  ev2.resize (0);
  if (ev1.size() == 0) return 0;
  momre_op_t momre_op;
  int max_momr= momre_op (front, ev1[0], cg);
  ev2.push_back (ev1[0]);

  for (size_t c= 1; c < ev1.size(); c++) {
    int momr= momre_op (front, ev1[c], cg); 
    if (momr > max_momr) ev2.resize (0);
    if (momr >= max_momr) {
      ev2.push_back (ev1[c]); max_momr= momr;}
  }
  return ev2.size();
}

int momr_edge_t::operator() (const vector<edge_bool_t>& ev1, const c_graph_t& cg,
			     vector<edge_bool_t>& ev2) {
  momre_op_t   momre_op;
  return standard_heuristic_op (ev1, cg, ev2, momre_op, *this);
}

momr_edge_t momr_edge;

// -------------------------------------------------------------------------
// Minimal distance 
// -------------------------------------------------------------------------

// operator for minimal distances on faces
struct diste_op_t {
  int operator() (edge_bool_t eb, const c_graph_t& cg) {
    c_graph_t::vertex_t           i= source (eb.first, cg), j= target (eb.first, cg), dist= 0;
    vector<c_graph_t::vertex_t>   nb;
    if (eb.second) {
      successor_set (j, cg, nb);
      for (size_t c= 0; c < nb.size(); c++)
	if (nb[c] - i > dist) dist= nb[c] - i;
    } else {
      predecessor_set (j, cg, nb);
      for (size_t c= 0; c < nb.size(); c++)
	if (j - nb[c] > dist) dist= j - nb[c]; }
    throw_debug_exception (dist <= 0, consistency_exception, "Wrong distance in edge elimination");
    return dist; }
};

int minimal_distance_edge_t::operator() (const vector<edge_bool_t>& ev1, const c_graph_t& cg,
					 vector<edge_bool_t>& ev2) {
  return standard_heuristic_op (ev1, cg, ev2, diste_op_t(), *this);
}

minimal_distance_edge_t minimal_distance_edge;

// -------------------------------------------------------------------------
// Maximal overall path length reduction
// -------------------------------------------------------------------------

int moplr_edge (const vector<c_graph_t::edge_t>& ev1,
		bool front,
		const c_graph_t& cg,
		vector<c_graph_t::edge_t>& ev2) {
  ev2.resize (0);
  if (ev1.size() == 0) return 0;

  vector<int> vni, vli, vno, vlo;
  in_out_path_lengths (cg, vni, vli, vno, vlo);

  int max_oplr= front ? oplr_edge_front (ev1[0], vni, vli, vno, vlo, cg)
                      : oplr_edge_back (ev1[0], vni, vli, vno, vlo, cg);
  ev2.push_back (ev1[0]);

  for (size_t c= 1; c < ev1.size(); c++) {
    c_graph_t::edge_t e= ev1[c];
    int oplr= front ? oplr_edge_front (e, vni, vli, vno, vlo, cg)
                    : oplr_edge_back (e, vni, vli, vno, vlo, cg);
    if (oplr > max_oplr) ev2.resize (0);
    if (oplr >= max_oplr) {
      ev2.push_back (e); max_oplr= oplr;}
  }

  return ev2.size();
}



// =====================================================
// for face elimination
// =====================================================

// objective function for forward and reverse mode in face elimination
// works up to 165 thousands vertices in IEEE arithmetic
inline double fmf_obj (line_graph_t::face_t f, const line_graph_t& lg) {
  int i, j, k, x= lg.x();
  face_vertex_name (f, lg, i, j, k);
  return ((double (j) * double (x)) + double (i)) * double (x) + double (k);
}

int forward_mode_face_t::operator() (const vector<line_graph_t::face_t>& fv1,
				     const line_graph_t& lg,
				     vector<line_graph_t::face_t>& fv2) {
  fv2.resize (0);
  if (fv1.size() == 0) {set_empty_objective (); return 0; }
  fv2.push_back (fv1[0]);

  for (size_t c= 1; c < fv1.size(); c++) {
    throw_debug_exception (fmf_obj (fv1[c], lg) < fmf_obj (fv2[0], lg) != lex_less_face (fv1[c], fv2[0], lg),
			   consistency_exception, "objective function and comparator does not match");
    if (lex_less_face (fv1[c], fv2[0], lg)) fv2[0]= fv1[c]; }
  set_objective (fmf_obj (fv2[0], lg));
  return 1;
}

forward_mode_face_t forward_mode_face;

// -------------------------------------------------------------------------
// reverse mode
// -------------------------------------------------------------------------

int reverse_mode_face_t::operator() (const vector<line_graph_t::face_t>& fv1,
				     const line_graph_t& lg,
				     vector<line_graph_t::face_t>& fv2) {
  fv2.resize (0);
  if (fv1.size() == 0) {set_empty_objective (); return 0; }
  fv2.push_back (fv1[0]);

  for (size_t c= 1; c < fv1.size(); c++) {
    throw_debug_exception (fmf_obj (fv1[c], lg) < fmf_obj (fv2[0], lg) != lex_less_face (fv1[c], fv2[0], lg),
			   consistency_exception, "objective function and comparator does not match");
    if (!lex_less_face (fv1[c], fv2[0], lg)) fv2[0]= fv1[c]; }
  set_objective (fmf_obj (fv2[0], lg));
  return 1;
}

reverse_mode_face_t reverse_mode_face;

int reverse_mode_face_whole_vertex_t::operator() (const vector<line_graph_t::face_t>& fv1,
						  const line_graph_t& lg,
						  vector<line_graph_t::face_t>& fv2) {
  fv2.resize (0);
  if (fv1.size() == 0) return 0;
  fv2.push_back (fv1[0]);
  line_graph_t::const_evn_t evn= get(boost::vertex_name, lg);

  int maxv= evn[source(fv1[0], lg)].second;

  for (size_t c= 1; c < fv1.size(); c++) {
    line_graph_t::face_t f= fv1[c];
    int v= evn[source(f, lg)].second;
    if (v > maxv) {fv2.resize (0); maxv= v;}
    if (v == maxv) fv2.push_back (f); }

  return fv2.size();
}

reverse_mode_face_whole_vertex_t reverse_mode_face_whole_vertex;

// -------------------------------------------------------------------------
// subroutine of Lowest Markowitz on line graph
// -------------------------------------------------------------------------

void markowitz_on_line_graph (const line_graph_t& lg,
			      vector<int>& mdegree) {

  line_graph_t::const_evn_t   evn= get(vertex_name, lg);
  int                         max_vertex_cg= 0;
  line_graph_t::ei_t          ei, e_end;
  for (boost::tie (ei, e_end)= vertices (lg); ei != e_end; ++ei)
    if (max_vertex_cg < evn[*ei].second) max_vertex_cg= evn[*ei].second;
    
  // number of faces in which vertex j occurs in the center
  // filter out independent and dependent vertices (i,i,k) or (i,k,k)
  mdegree.resize (0); mdegree.resize (max_vertex_cg+1);
  line_graph_t::fi_t          fi, f_end;
  for (boost::tie (fi, f_end)= edges (lg); fi != f_end; ++fi) {
    line_graph_t::edge_t s= source (*fi, lg), t= target (*fi, lg);
    if (evn[s].first != evn[s].second && evn[t].first != evn[t].second)
	mdegree[evn[s].second]++; }
}



// -------------------------------------------------------------------------
// Lowest Markowitz
// -------------------------------------------------------------------------

// operator for lowest Markowitz on faces
struct lmf_op_t {
  vector<int> mdegree;
  lmf_op_t (const line_graph_t& lg) {
    markowitz_on_line_graph (lg, mdegree); }
  int operator() (line_graph_t::face_t f, const line_graph_t& lg) {
    int i, j, k; face_vertex_name (f, lg, i, j, k);
    throw_debug_exception (mdegree[j] == 0, consistency_exception, "Un-eliminatable face in fv1"); 
    return mdegree[j]; }
};

int lowest_markowitz_face_t::operator() (const vector<line_graph_t::face_t>& fv1,
					 const line_graph_t& lg,
					 vector<line_graph_t::face_t>& fv2) {
  lmf_op_t      lmf_op (lg);
  return standard_heuristic_op (fv1, lg, fv2, lmf_op, *this);
}


// -------------------------------------------------------------------------
// MOMR
// -------------------------------------------------------------------------

// will a face (p,i,k) from (i,j)'s predecessor (p,i) to (i,k) be inserted ?
// or does it already exist
class new_pik_t {
  int i, k;
public:
  new_pik_t (int _i, int _k) : i (_i), k (_k) {}
  int operator() (line_graph_t::face_t pij, const line_graph_t& lg) const {
    line_graph_t::edge_t pi= source (pij, lg);
    // for independent edges, new faces doesn't affect Mark. -> stop
    if (vertex_type (pi, lg) == independent) return 0; 
    line_graph_t::ofi_t ofi, of_end;
    for (tie (ofi, of_end)= out_edges (pi, lg); ofi != of_end; ++ofi) {
      int v1, v2;
      edge_vertex_name (target (*ofi, lg), lg, v1, v2); 
      // assert (v1 == i);
      throw_debug_exception (v1 != i, consistency_exception, "Adjacency corrupted in line graph"); 
      if (v2 == k) return 0; } // (p,i,k) found
    return 1;
  }
};

struct source_not_independent_t {
  int operator() (line_graph_t::face_t f, const line_graph_t& lg) const {
    return (vertex_type (source (f, lg), lg) != independent); }
};

// will a face (i,k,s) to (j,k)'s successor (k,s) from (i,k) be inserted ?
// or does it already exist
class new_iks_t {
  int i, k;
public:
  new_iks_t (int _i, int _k) : i (_i), k (_k) {}
  int operator() (line_graph_t::face_t jks, const line_graph_t& lg) const {
    line_graph_t::edge_t ks= target (jks, lg);
    // for dependent edges, new faces doesn't affect Mark. -> stop
    if (vertex_type (ks, lg) == dependent) return 0; 
    line_graph_t::ifi_t ifi, if_end;
    for (tie (ifi, if_end)= in_edges (ks, lg); ifi != if_end; ++ifi) {
      int v1, v2;
      edge_vertex_name (source (*ifi, lg), lg, v1, v2);
      // assert (v2 == k);
      throw_debug_exception (v2 != k, consistency_exception, "Adjacency corrupted in line graph"); 
      if (v1 == i) return 0; } // (i,k,s) found
    return 1;
  }
};

struct target_not_dependent_t {
  int operator() (line_graph_t::face_t f, const line_graph_t& lg) const {
    return (vertex_type (target (f, lg), lg) != dependent); }
};

// operator for MOMR on faces
struct momrf_op_t {
  int operator() (line_graph_t::face_t f, const line_graph_t& lg) {
    int momr= 1; // the face itself
    int i, j, k; // f's vertices w.r.t. c-graph
    face_vertex_name (f, lg, i, j, k);
    line_graph_t::edge_t ij= source (f, lg), jk= target (f, lg);

    new_pik_t new_pik (i, k);
    momr-= sum_over_all_in_edges (ij, lg, new_pik);
    if (out_degree (ij, lg) == 1) 
      momr+= sum_over_all_in_edges (ij, lg, source_not_independent_t());

    new_iks_t new_iks (i, k);
    momr-= sum_over_all_out_edges (jk, lg, new_iks);
    if (in_degree (jk, lg) == 1) 
      momr+= sum_over_all_out_edges (jk, lg, target_not_dependent_t());
#ifndef NDEBUG
    line_graph_t         gtmp (lg);

    // eliminating f in gtmp does not work -> edge_descriptor from gtmp needed
    line_graph_t::face_t   ftmp;
    ftmp= *same_edge (f, lg, gtmp);
    face_elimination (ftmp, gtmp);

    int old_overall_markowitz= overall_markowitz_degree (lg);
    int new_overall_markowitz= overall_markowitz_degree (gtmp);
    if (old_overall_markowitz - new_overall_markowitz != momr) {
      write_graph ("AD edge before elimination", lg);
      line_graph_t::const_evn_t                 evn= get(vertex_name, lg);
      write_vertex_property (cout, "vertices of this edge graph", evn, lg);
      cout << "overall_markowitz_degree is " << old_overall_markowitz << "\n"; 
      cout << "elimination of face: ";
      write_face_op_t wf (gtmp); wf (cout, ftmp); 
      cout << endl;
      write_graph ("AD edge after elimination", gtmp);
      line_graph_t::evn_t                 evntmp= get(vertex_name, gtmp);
      write_vertex_property (cout, "vertices of this edge graph", evntmp, lg);
      cout << "overall_markowitz_degree is " << new_overall_markowitz 
	   << " momr is " << momr << "\n"; 
      line_graph_t         gtmp2 (lg);
      ftmp= *same_edge (f, lg, gtmp2);
      face_elimination (ftmp, gtmp2);
    }
    // assert (overall_markowitz_degree (lg) - overall_markowitz_degree (gtmp) == momr);
    throw_debug_exception (overall_markowitz_degree (lg) - overall_markowitz_degree (gtmp) != momr, 
			   consistency_exception, "momr not correct"); 
#endif
    return momr; }
};

int momr_face_t::operator() (const vector<line_graph_t::face_t>& fv1,
			     const line_graph_t& lg,
			     vector<line_graph_t::face_t>& fv2) {
  momrf_op_t   momrf_op;
  return standard_heuristic_op (fv1, lg, fv2, momrf_op, *this);
}

momr_face_t momr_face;

// -------------------------------------------------------------------------
// Minimal distance 
// -------------------------------------------------------------------------

// operator for minimal distances on faces
struct distf_op_t {
  int operator() (line_graph_t::face_t f, const line_graph_t& lg) {
    int i, j, k; face_vertex_name (f, lg, i, j, k);
    return k - i; }
};

int minimal_distance_face_t::operator() (const vector<line_graph_t::face_t>& fv1,
					 const line_graph_t& lg, vector<line_graph_t::face_t>& fv2) {
  return standard_heuristic_op (fv1, lg, fv2, distf_op_t(), *this);
}

// -------------------------------------------------------------------------
// Scarcity preserving edge eliminations
// -------------------------------------------------------------------------
int scarce_pres_edge_eliminations (vector<edge_bool_t>& bev1,
                                   const c_graph_t& cg,
                                   vector<edge_bool_t>& bev2) {
  bev2.resize (0);
  if (bev1.size() == 0) return 0;

  for (size_t c = 1; c < bev1.size(); c++) {
    c_graph_t::edge_t e = bev1[c].first;
    bool isFront = bev1[c].second;
    vector<c_graph_t::vertex_t> v_v;

    // select edge elimination objects that would isolate the target vertex
    // (for forward eliminations) or source vertex (for back eliminations)
    if (isFront) {
      predecessor_set (target (e, cg), cg, v_v);
      if (v_v.size() == 1) bev2.push_back (bev1[c]);
      break;
    }
    else {
      successor_set (source (e, cg), cg, v_v);
      if (v_v.size() == 1) bev2.push_back (bev1[c]);
      break;
    }

    // select eliminations that create a one or fewer fill-ins
    int fill = isFront ? new_out_edges (e,cg)
                       : new_in_edges (e,cg);
    if (fill < 2) bev2.push_back (bev1[c]);
  }
  return bev2.size();
}

} // namespace angel

// to do: some names are confusing, e.g. ev for a face vector
