// $Id: xaif_interface.hpp,v 1.7 2004/10/16 04:18:17 jean_utke Exp $

#ifndef         _xaif_interface_include_
#define         _xaif_interface_include_

#ifdef USEXAIFBOOSTER

#include "angel_types.hpp"

#include "xaifBooster/algorithms/CrossCountryInterface/inc/GraphCorrelations.hpp"
#include "xaifBooster/algorithms/CrossCountryInterface/inc/LinearizedComputationalGraph.hpp"
#include "xaifBooster/algorithms/CrossCountryInterface/inc/JacobianAccumulationExpressionList.hpp"

namespace angel {

/** \brief Executes a scarcity-preserving partial elimination sequence
 *  \param xgraph The original (input) linearized computational graph
 *  \param tasks
 *  \param jae_list
 *  \param rg
 *  \param v_cor_list
 *  \param e_cor_list
 *  	Performs a partial elimination sequence on a copy of the original graph
 *  and returns by reference a jacobian accumulation expression list, a
 *  remainder graph, and vertex/edge correlation lists \p v_cor_list and
 *  \p e_cor_list that map vertices in \p rg to vertices in \p xgraph.
 */
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

#endif // USEXAIFBOOSTER

#endif  // _xaif_interface_include_
