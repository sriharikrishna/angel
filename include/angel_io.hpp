// $Id: angel_io.hpp,v 1.8 2003/06/11 16:28:53 gottschling Exp $

#ifndef 	_angel_io_include_
#define 	_angel_io_include_


//
//
//

#include "boost/graph/graphviz.hpp"

#include <vector>
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <ctime>

#include "angel_types.hpp"
#include "angel_tools.hpp"

namespace angel {

  using namespace std;

  /** \brief Read graph in EliAD graph format from file
      
      In case file not found a new name is asked for (on cin) 
      if retry == true or ommited. If no name is entered then an
      exception containing the last tried filename is thrown. 
      Otherwise it is retried with the new name which is returned
      in the parameter list.
  */
int read_graph_eliad (string& file_name, c_graph_t& cg, bool retry= true);

// =====================================================
// output
// =====================================================

/// Write a face \p face of \p lg to \p stream
void write_face (ostream& stream, 
		 line_graph_t::face_t face,
		 const line_graph_t& lg);

/// Write a face \p face of \p lg to standard output
inline void write_face (line_graph_t::face_t face,
			const line_graph_t& lg) {
  write_face (cout, face, lg);
}

/// Write a vector \p v of faces from \p lg to \p stream with comment \p s
void write_face_vector (ostream& stream, const string& s, 
			const vector<line_graph_t::face_t>& v,
			const line_graph_t& lg);

/// Write a vector \p v of faces from \p lg to standard output with comment \p s
inline void write_face_vector (const string& s, 
			       const vector<line_graph_t::face_t>& v,
			       const line_graph_t& lg) {
  write_face_vector (cout, s, v, lg);
}

// -----------------------------------------------------
// general templates
// -----------------------------------------------------

/// Write pair of arbitrary types to \p stream if their output operator is defined
template <typename T1, typename T2>
ostream& operator<< (ostream& stream, const pair<T1,T2>& p) {
  return stream << "(" << p.first << ", " << p.second << ")"; }

/// Write STL vector \p v to \p stream with comment \p s if their output operator is defined
template <typename Scalar_t>
inline void write_vector (ostream& stream, const string& s, 
			  const vector<Scalar_t>& v);

/// Write STL vector \p v to standard output with comment \p s if their output operator is defined
template <typename Scalar_t>
inline void write_vector (const string& s, const vector<Scalar_t>& v) {
  write_vector (cout, s, v);
}

/** \brief Write STL vector to stream
    \param stream
    \param s Commenting string
    \param v Vector
    \param op Output operator, op (s, v[i]) must write element v[i] to \p s
*/
template <typename Scalar_t, typename Op_t>
inline void write_vector (ostream& stream, const string& s, 
			  const vector<Scalar_t>& v, Op_t op);

/** \brief Write STL vector to standard output
    \param stream
    \param v Vector
    \param op Output operator, op (s, v[i]) must write element v[i] to \p s
*/
template <typename Scalar_t, typename Op_t>
inline void write_vector (const string& s, const vector<Scalar_t>& v, 
			  Op_t op) {
  write_vector (cout, s, v, op);
}

// -----------------------------------------------------
// general graph output
// -----------------------------------------------------

/** \brief Write c-graph or line graph to stream
    \param stream
    \param s Commenting string
    \param adg C-graph or line graph
    \param write_edge_weight Write edge labels, only defined for c-graph
*/
template <typename Ad_graph_t> 
void write_graph (ostream& stream, const string& s, const Ad_graph_t& adg,
		  bool write_edge_weight);

/** \brief Write c-graph or line graph to standard output
    \param s Commenting string
    \param adg C-graph or line graph
    \param write_edge_weight Write edge labels, only defined for c-graph
*/
template <typename Ad_graph_t> 
inline void write_graph (const string& s, const Ad_graph_t& adg,
			 bool write_edge_weight) {	
  write_graph (cout, s, adg, write_edge_weight);
}

/** \brief Write c-graph or line graph to file
    \param file_name File will be overwritten
    \param s Commenting string
    \param adg C-graph or line graph
    \param write_edge_weight Write edge labels, only defined for c-graph
*/
template <typename Ad_graph_t> 
inline void write_graph (const string& file_name, 
			 const string& s, const Ad_graph_t& adg,
			 bool write_edge_weight) {       
  ofstream fout (file_name.c_str());
  write_graph (fout, s, adg, write_edge_weight);
}


/** \brief Write c-graph or line graph to stream
    \param stream
    \param s Commenting string
    \param adg C-graph or line graph
*/
template <typename Ad_graph_t> 
void write_graph (ostream& stream, const string& s, const Ad_graph_t& adg);

/** \brief Write c-graph or line graph to standard output
    \param s Commenting string
    \param adg C-graph or line graph
*/
template <typename Ad_graph_t> 
inline void write_graph (const string& s, const Ad_graph_t& adg) {	
  write_graph (cout, s, adg);
}

/** \brief Write c-graph or line graph to file
    \param file_name File will be overwritten
    \param s Commenting string
    \param adg C-graph or line graph
*/
template <typename Ad_graph_t> 
inline void write_graph (const string& file_name, 
			 const string& s, const Ad_graph_t& adg) {       
  ofstream fout (file_name.c_str());
  write_graph (fout, s, adg);
}

// -----------------------------------------------------
// general graph output as Boolian adjajency matrix
// -----------------------------------------------------

/** \brief Write c-graph or line graph to file as Boolean matrix
    \param file_name File will be overwritten
    \param adg C-graph or line graph
    \param write_transposed Write transposed matrix, if ommited false assumed
    \note Transposed form is quite memory expensive
*/
template <typename Ad_graph_t> 
void write_graph_as_bool_matrix (const string& file_name, const Ad_graph_t& adg,
				 bool write_transposed= false);

// -----------------------------------------------------
// write graph like EliAD tools does
// -----------------------------------------------------

/** \brief Write c-graph or line graph in EliAD format to stream
    \param stream
    \param adg C-graph or line graph
    \note Can be read by read_graph_eliad (const char* file_name, c_graph_t& cg)
*/
template <typename Ad_graph_t> 
inline void write_graph_eliad (ostream& stream, const Ad_graph_t& adg);

/** \brief Write c-graph or line graph in EliAD format to standard output
    \param adg C-graph or line graph
    \note Can be read by read_graph_eliad (const char* file_name, c_graph_t& cg)
*/
template <typename Ad_graph_t> 
inline void write_graph_eliad (const Ad_graph_t& adg) {
  write_graph_eliad (cout, adg);
}

/** \brief Write c-graph or line graph in EliAD format to file
    \param file_name File will be overwritten
    \param adg C-graph or line graph
    \note Can be read by read_graph_eliad (const char* file_name, c_graph_t& cg)
*/
template <typename Ad_graph_t> 
inline void write_graph_eliad (const string& file_name, const Ad_graph_t& adg) {
  ofstream fout (file_name.c_str());
  write_graph_eliad (fout, adg);
}

/// Operator used in write_graph_eliad
class write_edge_eliad_op_t {
  ostream& stream;
public:
  write_edge_eliad_op_t (ostream& s) : stream (s) {}
  template <typename Ad_graph_t> 
  void operator() (typename Ad_graph_t::edge_descriptor e, const Ad_graph_t& adg) {
    stream << "   " << target (e, adg) + 1 << "   " << source (e, adg) + 1 << "   2\n";
  }
};

template <typename Ad_graph_t> 
inline void write_graph_eliad (ostream& stream, const Ad_graph_t& adg) {

  stream << "n = " << adg.v() << "\n" << "CG = [\n";
  write_edge_eliad_op_t write_edge (stream);
  for_all_edges (adg, write_edge);
  stream << "]\n";
}

// -----------------------------------------------------
// write internal graph properties
// -----------------------------------------------------


/** \brief Write internal vertex property  to stream
    \param stream
    \param s Commenting string
    \param prop Vertex property
    \param adg C-graph or line graph
*/
template <typename Prop_t, typename Ad_graph_t> 
void write_vertex_property (ostream& stream, const string& s, 
			    const Prop_t& prop, const Ad_graph_t& adg) {
  stream << s << " are {";

  typename Ad_graph_t::vertex_iterator vi, vend;
  boost::tie (vi, vend) = vertices (adg);
  // write first if exist
  if (vi != vend) stream << prop[*vi++];

  for (; vi != vend; ++vi) 
    stream << ", " << prop[*vi];
  stream << '}' << endl;
}

/** \brief Write internal edge property  to stream
    \param stream
    \param s Commenting string
    \param prop Edge property
    \param adg C-graph or line graph
*/
template <typename Prop_t, typename Ad_graph_t> 
void write_edge_property (ostream& stream, const string& s, 
			  const Prop_t& prop, const Ad_graph_t& adg);



// =====================================================
// lengthy implementations 
// =====================================================


template <typename Scalar_t>
inline void write_vector (ostream& stream, const string& s, 
			  const vector<Scalar_t>& v) {

  stream << s << " (size = " << v.size() << ") is {";

  typename vector<Scalar_t>::const_iterator i= v.begin();
  // write first if exist
  if (i != v.end()) stream << *i++; 

  // from second to last (if exist)
  for (; i != v.end(); ++i)
    stream << ", " << *i;
  stream << '}' << endl;
}

template <typename Scalar_t, typename Op_t>
inline void write_vector (ostream& stream, const string& s, 
			  const vector<Scalar_t>& v, Op_t op) {

  stream << s << " (size = " << v.size() << ") is {";

  typename vector<Scalar_t>::const_iterator i= v.begin();
  // write first if exist
  if (i != v.end()) op (stream, *i++); 

  // from second to last (if exist)
  for (; i != v.end(); ++i)
    stream << ", ", op (stream, *i);
  stream << '}' << endl;
}

template <typename Ad_graph_t> 
void write_graph_as_bool_matrix (const string& file_name, const Ad_graph_t& adg,
				 bool write_transposed) {
  using namespace boost;
  using boost::tie;

  // typedef typename Ad_graph_t::pure_graph_t                         pure_graph_t;
  typedef typename graph_traits<Ad_graph_t>::vertex_iterator      vi_t;
  typedef typename graph_traits<Ad_graph_t>::edge_iterator        ei_t;
  typedef typename graph_traits<Ad_graph_t>::adjacency_iterator   ai_t;
  typedef typename property_map<Ad_graph_t, vertex_index_t>::type id_t;
  // typedef typename pure_graph_t::edge_type                          ed_t;

  // const pure_graph_t& g (adg.pure_graph);
  vi_t i, end;
  id_t id = get(vertex_index, adg);

  // tie(i, end) = vertices(g);
  int gsize= num_vertices (adg);

  ofstream fout (file_name.c_str());
  fout << adg.x() << endl << adg.z() << endl << adg.y() << endl;

  if (write_transposed) {
    vector<bool> bool_line (gsize, false);
    vector<vector<bool> > bool_matrix (gsize, bool_line);
    for (tie(i, end) = vertices(adg); i != end; ++i) {
      ai_t ai, a_end;
      for (tie(ai, a_end) = adjacent_vertices(*i, adg); ai != a_end; ++ai)
	bool_matrix[get(id, *ai)][get(id, *i)]= true;
    }
    for (tie(i, end) = vertices(adg); i != end; ++i) {
      const vector<bool>& line_ref (bool_matrix[get(id, *i)]);
      for (int j= 0; j < gsize; j++)
	fout << (line_ref[j] ? 1 : 0);
      fout << endl;
    }
  } else 
    for (tie(i, end) = vertices(adg); i != end; ++i) {
      vector<int> bool_line (gsize, 0);
      ai_t ai, a_end;
      for (tie(ai, a_end) = adjacent_vertices(*i, adg); ai != a_end; ++ai)
	  bool_line[get(id, *ai)]= 1;
      for (int j= 0; j < gsize; j++)
	fout << bool_line[j];
      fout << endl;
    }
}

template <typename Ad_graph_t> 
void write_graph (ostream& stream, const string& s, const Ad_graph_t& adg,
		  bool write_edge_weight) {	
  using namespace boost;
  stream << s << " has " << num_vertices (adg) << " vertices: "
	 << adg.x() << " independent, " << adg.z() << " intermediate and "
	 << adg.y() << " dependent\n";
  write_vector (stream, "the dependent vertices are", adg.dependents);
  stream << "the adjacencies are:\n";


  if (write_edge_weight) {
    typename property_map<Ad_graph_t, edge_weight_t>::const_type 
             ew= get(edge_weight, adg);
    typename graph_traits<Ad_graph_t>::vertex_iterator  i, end;
    for (tie (i, end)= vertices (adg); i != end; ++i) {
      typename graph_traits<Ad_graph_t>::out_edge_iterator  ei, e_end;
      tie(ei, e_end) = out_edges(*i, adg);
      stream << "vertex " << *i << " has ";
      if (ei == e_end) stream << "no successor";
      else stream << "successors ";
      for (; ei != e_end; ++ei)
	stream << target (*ei, adg) << '[' << ew[*ei] << "]  ";
      stream << endl;
    }
    stream << endl;
  } else {
    typename graph_traits<Ad_graph_t>::vertex_iterator  i, end;
    for (tie (i, end)= vertices (adg); i != end; ++i) {
      typename graph_traits<Ad_graph_t>::adjacency_iterator  ai, a_end;
      tie(ai, a_end) = adjacent_vertices(*i, adg);
      stream << "vertex " << *i << " has ";
      if (ai == a_end) stream << "no successor";
      else stream << "successors ";
      for (; ai != a_end; ++ai)
	stream << *ai << "  ";
      stream << endl;
    }
    stream << endl;
  }
}

template <typename Ad_graph_t> 
void write_graph (ostream& stream, const string& s, const Ad_graph_t& adg) {	
  using namespace boost;
  stream << s << " has " << num_vertices (adg) << " vertices: "
	 << adg.x() << " independent, " << adg.z() << " intermediate and "
	 << adg.y() << " dependent\n";
  write_vector (stream, "the dependent vertices are", adg.dependents);
  stream << "the adjacencies are:\n";

    typename graph_traits<Ad_graph_t>::vertex_iterator  i, end;
    for (tie (i, end)= vertices (adg); i != end; ++i) {
      typename graph_traits<Ad_graph_t>::adjacency_iterator  ai, a_end;
      tie(ai, a_end) = adjacent_vertices(*i, adg);
      stream << "vertex " << *i << " has ";
      if (ai == a_end) stream << "no successor";
      else stream << "successors ";
      for (; ai != a_end; ++ai)
	stream << *ai << "  ";
      stream << endl;
    }
    stream << endl;
}




template <typename Prop_t, typename Ad_graph_t> 
void write_edge_property (ostream& stream, const string& s, 
			  const Prop_t& prop, const Ad_graph_t& adg) {
  stream << s << " is {";

  typename Ad_graph_t::edge_iterator ei, eend;
  boost::tie (ei, eend) = edges (adg);
  // write first if exist
  if (ei != eend) {
    stream << '(' << source (*ei, adg) << ", " << target (*ei, adg) 
	   << ")=" << prop[*ei];
    ++ei;}

  for (; ei != eend; ++ei) 
    stream << ", (" << source (*ei, adg) << ", " << target (*ei, adg) 
	   << ")=" << prop[*ei];
  stream << '}' << endl;
}

template <typename Ad_graph_t> 
void graphviz_display (const Ad_graph_t& adg) {
  string aFilename("/tmp/GraphVizDisplay.dot");
  ofstream anOutFileStream;
  anOutFileStream.open(aFilename.c_str(),ios::out);
  boost::write_graphviz(anOutFileStream, adg); 
  anOutFileStream.close(); 
  string commandString("dot -Tgif " + aFilename + " > " + aFilename + ".gif ; xv " + aFilename + ".gif" ); 
  system(commandString.c_str()); 
}

extern ofstream log_file;

#ifndef USE_MPI
inline void open_log_file (int& argc, char**& argv) {
  ostringstream log_file_name;
  log_file_name << "log_file_" << time (0);
  log_file.open (log_file_name.str().c_str());
  log_file << "argv" << endl;
  for (int i= 0; i < argc; i++)
    log_file << argv[i] << endl;
  log_file << "----- end of argv -----" << endl;
}
#endif

#ifdef USE_MPI
inline void open_log_file (int& argc, char**& argv, int proc) {
  ostringstream log_file_name;
  log_file_name << "log_file_proc_" << proc << "_" << time (0);
  log_file.open (log_file_name.str().c_str());
  log_file << "argv" << endl;
  for (int i= 0; i < argc; i++)
    log_file << argv[i] << endl;
  log_file << "----- end of argv -----" << endl;
}
#endif

inline void close_log_file () {
  log_file.close();
}   
      
} // namespace angel

#endif // 	_angel_io_include_























































