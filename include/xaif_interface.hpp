// $Id: xaif_interface.hpp,v 1.4 2003/11/10 16:55:27 uwe_naumann Exp $

#ifndef 	_xaif_interface_include_
#define 	_xaif_interface_include_

#ifdef USE_XAIF

#include "angel_types.hpp"

#include "xaifBooster/algorithms/CrossCountryInterface/inc/LinearizedComputationalGraph.hpp"
#include "xaifBooster/algorithms/CrossCountryInterface/inc/JacobianAccumulationExpressionList.hpp"

namespace angel {

void compute_elimination_sequence (const xaifBoosterCrossCountryInterface::LinearizedComputationalGraph& xgraph,
				   int tasks, 
				   xaifBoosterCrossCountryInterface::JacobianAccumulationExpressionList& expression_list);

/* internal function
void read_graph_xaif_booster (const xaifBooster::LinearizedComputationalGraph& xg, c_graph_t& cg,
			      vector<xaifBooster::LinearizedComputationalGraphVertex*>& av);
*/

} // namespace angel

#endif // USE_XAIF

#endif  // _xaif_interface_include_
