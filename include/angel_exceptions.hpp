// $Id: angel_exceptions.hpp,v 1.1 2003/06/11 16:30:05 gottschling Exp $

#ifndef 	_angel_exceptions_include_
#define 	_angel_exceptions_include_

#include <string>
#include <iostream>
#include <sstream>

namespace angel {

  class base_exception {
  protected:
    std::string reason;
  public:
    /// Save file name, line number and reason of exception 
    base_exception (std::string filename, int linenumber, std::string what) {
      std::ostringstream stream;
      stream << "In file " << filename << " at line " << linenumber << ": " << what; 
      reason= stream.str(); }
    /// Write file name, line number and reason to cerr
    void say_reason () {
      std::cerr << reason << std::endl;}
    /// return file name, line number and reason as string
    const std::string& what_reason () const {return reason;}
  };

  class io_exception : public base_exception {
  public:
    io_exception (std::string filename, int linenumber, std::string what) 
      : base_exception (filename, linenumber, what) {}
  };

  class consistency_exception : public base_exception {
  public:
    consistency_exception (std::string filename, int linenumber, std::string what) 
      : base_exception (filename, linenumber, what) {}
  };
  

#ifndef NDEBUG
#define throw_debug_exception(Test,Exception,Message) \
{ \
if (Test) { \
  throw Exception(__FILE__, __LINE__, Message); }\
}
#else
#define throw_debug_exception(Test,Exception,Message)
#endif

#define throw_exception(Test,Exception,Message) \
{ \
if (Test) { \
  throw Exception(__FILE__, __LINE__, Message); }\
}


} // namespace angel


#endif  // _angel_exceptions_include_

