// $Id: angel_io.cpp,v 1.4 2004/02/22 18:44:46 gottschling Exp $

#include "angel_io.hpp"

#include <fstream>
#include <string.h>
#include <cstdio>
#include <vector>

#include "angel_tools.hpp"
#include "angel_exceptions.hpp"

namespace angel {

  using namespace std;
  using namespace boost;

int read_graph_eliad (string& file_name, c_graph_t& cg, bool retry) {

  typedef c_graph_t::vertex_t vertex_t;

  FILE* fin= fopen (file_name.c_str(), "r");
  while (fin == NULL) {
    string error_message= "File " + file_name + " with c-graph not found"; 
    if (retry) {
      cout << "File " << file_name << " of c-graph does not exist. \n"
	   << "Please enter other filename (or \"abort\" to abort). \n";
      cin >> file_name; }
    if (!retry || file_name == "abort") 
      throw_exception (true, io_exception, error_message);
    fin= fopen (file_name.c_str(), "r"); }

  char line [80]; 
  c_graph_t::ew_t ew= get(edge_weight, cg); 

  fgets (line, 80, fin);
  while (!feof (fin) && !strpbrk (line, "0123456789")) fgets (line, 80, fin); // 1st line with numbers 
  char* cp= strpbrk (line, "0123456789"); 
  int nv, read_values= sscanf (cp, "%i", &nv); // number of vertices
  throw_exception (read_values != 1, io_exception, "Number of vertices expected");
  c_graph_t gtmp (0, nv, 0); // all vertices as intermediate for now

  fgets (line, 80, fin); // read 'CG = ['

  int edge_number= 0; // to give numbers to the edges
  while (!feof (fin)) {
    fgets (line, 80, fin);
    if (strchr (line, ']')) break; // end found
    int target, source, triviality; 
    read_values= sscanf (line, "%i %i %i", &target, &source, &triviality);
    throw_exception (read_values != 3, io_exception, "Three values per line expected");
    c_graph_t::edge_t edge; bool added; 
    tie (edge, added)= add_edge (source-1, target-1, edge_number++, gtmp); // fortran to c re-numbering
    ew [edge]= triviality;
  }

  // vertices with in-degree 0 are independent and with out-degree 0 dependent
  c_graph_t::vi_t vi, v_end;
  vector<vertex_t> indeps;
  for (boost::tie (vi, v_end)= vertices (gtmp); vi != v_end; ++vi) {
    int ind= in_degree (*vi, gtmp), outd= out_degree (*vi, gtmp);
    throw_exception (ind == 0 && outd == 0, io_exception, 
		     "Unconnected vertex in input graph");
    if (ind == 0) indeps.push_back (*vi);
    if (outd == 0) gtmp.dependents.push_back (*vi); }

  gtmp.X= indeps.size(); 

  c_graph_t gtmp2;
  independent_vertices_to_front (gtmp, indeps, gtmp2);

  gtmp2.check_initial ();
  cg.swap (gtmp2);
  return 0;
}

void write_face (std::ostream& stream, 
		 line_graph_t::face_t face,
		 const line_graph_t& lg) {

  line_graph_t::edge_t vij= source (face, lg), vjk= target (face, lg);

  line_graph_t::const_evn_t evn= get(vertex_name, lg);
  int i= evn[vij].first, j= evn[vij].second, k= evn[vjk].second;
  throw_debug_exception (j != evn[vjk].first, consistency_exception,
			 "Adjacency corrupted in line graph"); 

  stream << '(' << vij << ", " << vjk
	 << ")=(" << i << ", " << j << ", " << k << ')';
}

void write_face_vector (std::ostream& stream, const std::string& s, 
			const std::vector<line_graph_t::face_t>& v,
			const line_graph_t& lg) {
  stream << s << " (size = " << v.size() << ") is {";

  std::vector<line_graph_t::face_t>::const_iterator i= v.begin();
  // write first if exist
  if (i != v.end()) write_face (stream, *i++, lg); 

  // from second to last (if exist)
  for (; i != v.end(); ++i) {
    stream << ", ";
    write_face (stream, *i, lg); }
  stream << '}' << std::endl;
}

ofstream log_file;

string numbered_filename (const string& basename, const string& suffix, 
			int number, int width) {
  ostringstream ost;
  ost << basename; 
  ost.width(width); ost.fill('0'); ost << number;
  ost << '.' << suffix;
  return ost.str();
}

no_output_t no_output;

string_stream_output_t cout_string_output (std::cout);

vis_display_output_t cout_vis_display_output (std::cout);

} // namespace angel



