// $Id: angel_comm.hpp,v 1.8 2003/06/11 16:28:52 gottschling Exp $

#ifndef 	_angel_comm_include_
#define 	_angel_comm_include_

// File will be completly ignored without MPI
#ifdef USE_MPI

#include "angel_types.hpp"
#include "gmpi.hpp"
#include "eliminations.hpp"

namespace angel {
  /// Buffer type for all communications
  typedef GMPI::buffer_t<int>     comm_buffer_t;

  /// Graph ID, e.g. to identify received int arrays
  enum graph_id_t {c_graph_id, line_graph_id, accu_graph_id}; 
}

// additional operators for GMPI
namespace GMPI {

  using namespace std;
  using namespace angel;

  // =============== reading from and writing into buffers ===========
  
  /// Read a vertex from buffer
  inline const comm_buffer_t& operator>> (const comm_buffer_t& buffer, 
					  c_graph_t::vertex_t& input) {
    input= buffer.read (); return buffer; }

  /// Write a vertex into buffer
  inline comm_buffer_t& operator<< (comm_buffer_t& buffer, 
					  const c_graph_t::vertex_t& output) {
    buffer.write (output); return buffer; }
  
  /// Read a edge elimination from buffer
  inline const comm_buffer_t& operator>> (const comm_buffer_t& buffer, 
					  edge_ij_elim_t& input) {
    int tmp; buffer >> input.i >> input.j >> tmp; 
    input.front= (bool) tmp; return buffer; }

  /// Write a edge elimination into buffer
  inline comm_buffer_t& operator<< (comm_buffer_t& buffer, 
				    const edge_ij_elim_t& output) {
    buffer << output.i << output.j << (int) output.front; return buffer; }

  /// Read a face elimination from buffer
  inline const comm_buffer_t& operator>> (const comm_buffer_t& buffer, 
					  triplet_t& input) {
    buffer >> input.i >> input.j >> input.k; return buffer; }

  /// Write a face elimination into buffer
  inline comm_buffer_t& operator<< (comm_buffer_t& buffer, 
				    const triplet_t& output) {
    buffer << output.i << output.j << output.k; return buffer; }

  /// Read a c graph from buffer
  const comm_buffer_t& operator>> (const comm_buffer_t& buffer, c_graph_t& cg);
  
  /// Write a c graph into buffer
  comm_buffer_t& operator<< (comm_buffer_t& buffer, const c_graph_t& cg);

  /// Read a line graph from buffer
  const comm_buffer_t& operator>> (const comm_buffer_t& buffer, line_graph_t& input);
  
  /// Write a line graph into buffer
  comm_buffer_t& operator<< (comm_buffer_t& buffer, const line_graph_t& output);  

  /// Read elimination history, og is not communicated
  template <typename Ad_graph_t, typename El_spec_t>
  const comm_buffer_t& operator>> (const comm_buffer_t& buffer, 
				   elimination_history_t<Ad_graph_t,El_spec_t>& input) {
    // Clear graph and sequence
    Ad_graph_t empty; input.cg= empty; input.seq.resize (0);
    buffer >> input.ccosts >> input.cg >> input.seq;
    return buffer;
  }

  /// Write elimination history, og is not communicated
  template <typename Ad_graph_t, typename El_spec_t>
  comm_buffer_t& operator<< (comm_buffer_t& buffer, 
			     const elimination_history_t<Ad_graph_t,El_spec_t>& input) {
    buffer << input.ccosts << input.cg << input.seq;
    return buffer; }

} // namespace GMPI

namespace angel {
  using namespace GMPI;

  typedef comm_ref_t<int, c_graph_t>      c_graph_comm_ref_t;

  typedef comm_ref_t<int, line_graph_t>   line_graph_comm_ref_t;

  // Tags used in angel
  const int completion_tag= 3377;

  /* C version
  inline void mark_completion (const MPI_Comm& comm) {
    int me, size;
    MPI_Comm_rank (comm, &me); MPI_Comm_size (comm, &size); 
    for (int c= 0; c < size; c++)
      if (c != me) MPI_BSend (&me, 1, MPI_INT, c, completion_tag, comm);
  }

  inline bool test_completion (const MPI_Comm& comm) {
    int        flag;
    MPI_Status status;
    MPI_Iprobe (MPI_ANY_SOURCE, completion_tag, comm, &flag, &status);
    return flag;
  }

  inline void clean_completion_messages (const MPI_Comm& comm) {
    do {
      int        flag, dummy;
      MPI_Status status;
      MPI_Iprobe (MPI_ANY_SOURCE, completion_tag, comm, &flag, &status);
      if (flag) MPI_Recv (&dummy, 1, MPI_INT, MPI_ANY_SOURCE, completion_tag, comm, &status);
    } while (flag);
  } */

  inline void mark_completion (const MPI::Comm& comm) {
    int              me= comm.Get_rank(), size= comm.Get_size();
    for (int c= 0; c < size; c++)
      if (c != me) comm.Send (&me, 1, MPI::INT, c, completion_tag);
  }

  inline bool test_completion (const MPI::Comm& comm) {
    return comm.Iprobe (MPI::ANY_SOURCE, completion_tag); }

  inline void clean_completion_messages (const MPI::Comm& comm) {
    while (comm.Iprobe (MPI::ANY_SOURCE, completion_tag)) {
      int     dummy;
      comm.Recv (&dummy, 1, MPI_INT, MPI_ANY_SOURCE, completion_tag);}
  }

} // namespace angel

#include "angel_comm_impl.hpp"  // contains lengthy template functions

#endif // USE_MPI

#endif // 	_angel_comm_include_
