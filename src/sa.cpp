// $Id: sa.cpp,v 1.7 2008/02/28 14:57:33 gottschling Exp $

#include "angel/include/sa.hpp"

#include <cmath>

namespace angel {

  using namespace std;
  using namespace boost;

// =====================================================
// neighbourhoods
// =====================================================

void neighbor_swap (const std::vector<int>& old_seq, std::vector<int>& seq) {
  seq= old_seq;
  int size= old_seq.size();
  // assert (size > 1); // otherwise endless loop
  throw_debug_exception (size <= 1, consistency_exception, "Nothing to swap -> endless loop"); 

  size_t r1= angel::random (size);
  size_t r2= angel::random (size);
  while (r2 == r1) r2= angel::random (size); // should be different
  std::swap (seq[r1], seq[r2]); 
}

} // namespace angel



