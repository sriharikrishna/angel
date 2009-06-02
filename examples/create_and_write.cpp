// $Id: create_and_write.cpp,v 1.1 2008/02/28 14:57:32 gottschling Exp $
// Author: Peter Gottschling

#include <angel/angel.hpp>


using namespace angel;


int main()
{
    // Create a graph with 3 independent, 4 intermediate, and 2 dependent vertices
    c_graph_t    g(3, 4, 2);


    // Print the graph
    write_graph_eliad(g);


    return 0;
}
