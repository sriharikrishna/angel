// $Id: xaif_interface.hpp,v 1.7 2004/10/16 04:18:17 jean_utke Exp $

#ifndef 	_xaif_interface_include_
#define 	_xaif_interface_include_

#ifdef USE_XAIF

#include "angel_types.hpp"

#include "xaifBooster/algorithms/CrossCountryInterface/inc/LinearizedComputationalGraph.hpp"
#include "xaifBooster/algorithms/CrossCountryInterface/inc/JacobianAccumulationExpressionList.hpp"

namespace angel {

struct vertex_correlation_entry {
  xaifBoosterCrossCountryInterface::LinearizedComputationalGraphVertex* lcgVert;
  xaifBoosterCrossCountryInterface::LinearizedComputationalGraphVertex* rv;
};

enum RemainderEdgeType {LCG_EDGE, JAE_VERT};

union edge_correlation_entry {
  xaifBoosterCrossCountryInterface::LinearizedComputationalGraphEdge* lcgEdge;
  xaifBoosterCrossCountryInterface::JacobianAccumulationExpressionVertex* jaeVert;
  RemainderEdgeType type;
  xaifBoosterCrossCountryInterface::LinearizedComputationalGraphEdge* re;
};

typedef std::list<vertex_correlation_entry> vertexCorrelationList;
typedef std::list<edge_correlation_entry> edgeCorrelationList;

void compute_partial_elimination_sequence (const xaifBoosterCrossCountryInterface::LinearizedComputationalGraph& xgraph,
				           int tasks, 
				           double, // for interface unification
				           xaifBoosterCrossCountryInterface::JacobianAccumulationExpressionList& expression_list,
					   xaifBoosterCrossCountryInterface::LinearizedComputationalGraph& rgraph,
					   vertexCorrelationList& v_cor_list,
					   edgeCorrelationList& e_cor_list);

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
