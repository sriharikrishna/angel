// $Id: angel_tools_impl.hpp,v 1.4 2003/06/11 16:28:53 gottschling Exp $
// long template definitions from angel_tools.hpp


template <typename Neighbor_t>
bool search_path (const std::vector<c_graph_t::vertex_t>& from, 
		  const std::vector<c_graph_t::vertex_t>& to, const Neighbor_t& n,
		  std::vector<c_graph_t::vertex_t>& path,
		  bool breadth_first) {
  using namespace std;
  typedef c_graph_t::vertex_t             vertex_t;
  typedef vector<vertex_t>                vv_t;

  bool                path_found= false;
  deque<vertex_t>     trials; 
  vector<int>         dists (n.adg.v());  // distances: 0 means infinity, 1 means start

  for (size_t c= 0; c < from.size(); c++) {
    trials.push_back (from[c]); dists[from[c]]= 1; }
  
  while (!path_found && !trials.empty()) {
    vertex_t       current_vertex= trials.front();
    trials.pop_front (); 
    int            current_dist= dists[current_vertex]; 
    typename Neighbor_t::ei_t   ei, e_end;
    for (tie (ei, e_end)= n.edges (current_vertex); ei != e_end; ++ei) {
      vertex_t next_vertex= n.neighbor (ei);
      if (dists[next_vertex] == 0) {
	dists[next_vertex]= current_dist + 1; 
	if (breadth_first) trials.push_back (next_vertex); 
	else trials.push_front (next_vertex); 
	vv_t::const_iterator ito= find (to.begin(), to.end(), next_vertex);
	if (ito != to.end()) { // if arrived build path
	  int      path_dist= current_dist + 1;
	  path.resize (path_dist); // increase vector because we fill it backwards
	  vv_t::const_iterator ifrom= find (from.begin(), from.end(), next_vertex);
	  while (ifrom == from.end()) { // searching the path backward
	    path[path_dist-1]= next_vertex; 
	    typename Neighbor_t::rei_t   rei, re_end;
	    for (tie (rei, re_end)= n.redges (next_vertex); rei != re_end; ++rei)
	      if (dists[n.rneighbor (rei)] == path_dist - 1) {
		next_vertex= n.rneighbor (rei); path_dist--; break; }
	    ifrom= find (from.begin(), from.end(), next_vertex);
	    throw_debug_exception (rei == re_end, consistency_exception, "Path interrupted"); }
	  path[0]= next_vertex;
	  throw_debug_exception (path_dist != 1, consistency_exception, "Path not finished properly");
	  path_found= true; break; } } } }
  return path_found;
}

template <typename Neighbor_t>
int maximal_paths (c_graph_t::vertex_t v, const Neighbor_t& nin, 
		   std::vector<typename std::vector<c_graph_t::vertex_t> >& paths) {
  using namespace std;
  c_graph_t                      cgc (nin.adg); // graph must be copied
  Neighbor_t                     n (cgc);
  vector<c_graph_t::vertex_t>    from (1, v), to (n.last()), current_path;

  paths.resize (0);
  while (search_path (from, to, n, current_path)) {
    paths.push_back (current_path);
    // remove vertices on path except v
    current_path.erase (current_path.begin()); n.clear_vertices (current_path); } 
  throw_debug_exception (paths.size() > to.size() || paths.size() > nin.degree (v),
			 consistency_exception, "Too many paths (wrong computation)"); 
  return paths.size();
}

template <typename Neighbor_t>
int smallest_separator_set (c_graph_t::vertex_t v, const Neighbor_t& nin, 
			    std::vector<c_graph_t::vertex_t>& sep_set) {
  using namespace std;
  typedef c_graph_t::vertex_t             vertex_t;
  typedef vector<vertex_t>                vv_t;
  
  sep_set.resize (0);
  vv_t                 from (1, v), to (nin.last());
  vector<vv_t>         all_paths;
  int                  num_paths= maximal_paths (v, nin, all_paths);
  for (int c= 0; c < num_paths; c++) all_paths[c].erase (all_paths[c].begin()); // remove v from paths

  for (int c1= 0; c1 < num_paths; c1++) {
    Neighbor_t n1 (nin);
    // remove vertices from sep set and following paths
    n1.clear_vertices (sep_set);
    for (int c2= c1 + 1; c2 < num_paths; c2++) 
      n1.clear_vertices (all_paths[c2]);

    // now search in the current path for a separating vertex
    const Neighbor_t& current_path= all_paths[c1];
    for (size_t c2= 0; c2 < current_path.size(); c2++) {
      vertex_t current_vertex= current_path[c2];
      Neighbor_t n2 (n1);
      vv_t vec (1, current_vertex), new_path;
      n2.clear_vertices (vec);
      if (!search_path (from, to, n2, new_path)) {
	sep_set.push_back (current_vertex); break; } } }

#ifndef NDEBUG
  Neighbor_t ntest (nin);
  ntest.clear_vertices (sep_set);
  vv_t test_path;
  throw_exception (search_path (from, to, ntest, test_path), consistency_exception, "Separator set wrong");
#endif

  return sep_set.size();
}


