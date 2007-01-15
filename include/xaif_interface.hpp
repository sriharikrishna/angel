// $Id: xaif_interface.hpp,v 1.7 2004/10/16 04:18:17 jean_utke Exp $

#ifndef 	_xaif_interface_include_
#define 	_xaif_interface_include_

#ifdef USE_XAIF

#include "angel_types.hpp"

#include "xaifBooster/algorithms/CrossCountryInterface/inc/GraphCorrelations.hpp"
#include "xaifBooster/algorithms/CrossCountryInterface/inc/LinearizedComputationalGraph.hpp"
#include "xaifBooster/algorithms/CrossCountryInterface/inc/JacobianAccumulationExpressionList.hpp"

namespace angel {

void compute_partial_elimination_sequence (const xaifBoosterCrossCountryInterface::LinearizedComputationalGraph& xgraph,
				           int tasks, 
				           double, // for interface unification
				           xaifBoosterCrossCountryInterface::JacobianAccumulationExpressionList& jae_list,
					   xaifBoosterCrossCountryInterface::LinearizedComputationalGraph& rg,
					   xaifBoosterCrossCountryInterface::VertexCorrelationList& v_cor_list,
					   xaifBoosterCrossCountryInterface::EdgeCorrelationList& e_cor_list);

void compute_elimination_sequence (const xaifBoosterCrossCountryInterface::LinearizedComputationalGraph& xgraph,
				   int tasks, 
				   double, // for interface unification
				   xaifBoosterCrossCountryInterface::JacobianAccumulationExpressionList& expression_list);

void compute_elimination_sequence_lsa_vertex (const xaifBoosterCrossCountryInterface::LinearizedComputationalGraph& xgraph,
					      int iterations, 
					      double gamma,
					      xaifBoosterCrossCountryInterface::JacobianAccumulationExpressionList& expression_list);

void compute_elimination_sequence_lsa_face (const xaifBoosterCrossCountryInterface::LinearizedComputationalGraph& xgraph,
					    int iterations, 
					    double gamma,
					    xaifBoosterCrossCountryInterface::JacobianAccumulationExpressionList& expression_list);

} // namespace angel

#endif // USE_XAIF

#endif  // _xaif_interface_include_
