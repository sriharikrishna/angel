#ifdef USEXAIFBOOSTER

#ifndef 	_reroutings_include_
#define 	_reroutings_include_

#include "angel_types.hpp"
#include "eliminations.hpp"

using std::list;
using std::vector;
using std::cout;
using boost::tie;
using namespace xaifBoosterCrossCountryInterface;

namespace angel {

/** Populates a list of all viable edge reroutings in \p angelLCG.

    \param angelLCG the c_graph_t (passed by reference) that the operation is performed on.
    \param erv empty list that will hold all pre-routings and post-routings in \p angelLCG.
    \return List of edge reroutings \p erv (by reference).
 */
void reroutable_edges (c_graph_t& angelLCG,
		       vector<edge_reroute_t>& erv);

/** Calculates the change in nontrivial edge count from \p er
    without actually performing it.  In addition,
    incrementIsTrivial is returned by reference
 */
int reroute_effect (const edge_reroute_t er,
		    const c_graph_t& angelLCG,
		    const Elimination::AwarenessLevel_E ourAwarenessLevel,
		    bool& incrementIsTrivial);

/** Filters edge reroutings from \p erv1.  Those reroutings that reduce the
    nonunit edge count in \p angelLCG when followed by an edge elimination
    are placed into \p erv2.

    \param erv1 vector of edge reroutings in \p angelLCG
    \param angelLCG the c_graph_t (passed by reference) that the operation is
	   performed on.
    \param erv2 empty list that will hold all nonunit edge count reducing pre-
	   or post-routings followed by edge eliminations in \p angelLCG.
    \return List of edge reroutings \p erv2 (by reference).
 */
bool edge_reducing_rerouteElims_types12 (const vector<edge_reroute_t>& erv1,
					 const c_graph_t& angelLCG,
					 const Elimination::AwarenessLevel_E ourAwarenessLevel,
					 bool allowMaintainingFlag,
					 vector<edge_reroute_t>& erv2);

/** Filters edge reroutings paired with eliminations from \p erv1.
    Those reroutings of type 3 (pre-routing (j,i) about (k,i),
    followed by the back-elimination of some (i,l)) that preserve
    scarcity or propagation are placed into \p erv2.

    \param erv1 vector of edge reroutings in \p angelLCG
    \param angelLCG the graph (of type c_graph_t) passed by reference
    \param erv2 vector by which results of the filter are returned
    \return List of edge reroutings \p erv2 (by reference).
 */
bool edge_reducing_rerouteElims_type3 (const vector<edge_reroute_t>& erv1,
				       const c_graph_t& angelLCG,
				       const Elimination::AwarenessLevel_E ourAwarenessLevel,
				       bool allowMaintainingFlag,
				       vector<edge_reroute_t>& erv2);

// Decrement edge from the source of prerouted_e to tgt (set as -= (src of pivot_e, tgt) * prerouted_e/pivot_e
unsigned int perform_quotient_decrement_directly (c_graph_t::edge_t prerouted_e,
						  c_graph_t::edge_t pivot_e,
						  c_graph_t::vertex_t tgt,
						  c_graph_t& angelLCG,
						  const Elimination::AwarenessLevel_E ourAwarenessLevel,
						  list<EdgeRef_t>& edge_ref_list,
						  JacobianAccumulationExpressionList& jae_list);

unsigned int preroute_edge_directly (edge_reroute_t er,
				     c_graph_t& angelLCG,
				     const Elimination::AwarenessLevel_E ourAwarenessLevel,
				     list<EdgeRef_t>& edge_ref_list,
				     JacobianAccumulationExpressionList& jae_list);

unsigned int postroute_edge_directly (edge_reroute_t er,
				      c_graph_t& angelLCG,
				      const Elimination::AwarenessLevel_E ourAwarenessLevel,
				      list<EdgeRef_t>& edge_ref_list,
				      JacobianAccumulationExpressionList& jae_list);

unsigned int prerouteEdge_noJAE (edge_reroute_t er,
				 c_graph_t& angelLCG,
				 const Elimination::AwarenessLevel_E ourAwarenessLevel);

unsigned int postrouteEdge_noJAE (edge_reroute_t er,
				  c_graph_t& angelLCG,
				  const Elimination::AwarenessLevel_E ourAwarenessLevel);

} // namespace angel

#endif // _reroutings_include_

#endif  // USEXAIFBOOSTER

