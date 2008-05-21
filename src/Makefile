# $Id: Makefile,v 1.22 2008/02/28 14:57:32 gottschling Exp $

# BOOST_DIR must be defined in the environment !

# CXXFLAGS may be changed appropriately
#CXXFLAGS+= -O3 
CXXFLAGS+= -DNDEBUG
#CXXFLAGS+= -g

#CPPFLAGS+= -DIGNORE_TRIVIAL_ELIMINATIONS
#CPPFLAGS+= -DGNUPLOT # generate output for gnuplot (maybe part of output must be set as comment)
#CPPFLAGS+= -DWRITE_COSTS # write costs for instance in LSA.hpp
#CPPFLAGS+= -DSAME_RANDOM_VALUES # pseudo random values identical in each run, for debugging

OBJECTS	= heuristics.o sa.o angel_comm.o angel_types.o angel_tools.o angel_io.o eliminations.o \
			graph_generator.o xaif_interface.o 
IDIR	= ../include
CXXFLAGS+= -c

ANGEL_ROOT = ../..
CXXFLAGS+= -I$(ANGEL_ROOT) 

it:	all

all:	$(OBJECTS)

clean: 
	$(RM) $(RMFLAGS) *.o *~ 

echo:
	echo "$(CPPFLAGS) : $(angel_config)"

.PHONY: it all clean echo

angel_types.o: angel_types.cpp $(IDIR)/angel_types.hpp
	$(CXX) $(CXXFLAGS) $(CPPFLAGS) -o $@ angel_types.cpp

angel_tools.o: angel_tools.cpp $(IDIR)/angel_tools.hpp \
		 $(IDIR)/angel_types.hpp \
		$(IDIR)/angel_io.hpp $(IDIR)/eliminations.hpp
	$(CXX) $(CXXFLAGS) $(CPPFLAGS) -o $@ angel_tools.cpp

angel_io.o: angel_io.cpp $(IDIR)/angel_io.hpp $(IDIR)/angel_types.hpp \
		$(IDIR)/angel_tools.hpp
	$(CXX) $(CXXFLAGS) $(CPPFLAGS) -o $@ angel_io.cpp

eliminations.o: eliminations.cpp $(IDIR)/eliminations.hpp $(IDIR)/angel_types.hpp \
		$(IDIR)/angel_tools.hpp $(IDIR)/angel_io.hpp
	$(CXX) $(CXXFLAGS) $(CPPFLAGS) -o $@ eliminations.cpp

heuristics.o: heuristics.cpp $(IDIR)/heuristics.hpp $(IDIR)/angel_types.hpp \
		$(IDIR)/angel_tools.hpp \
		 $(IDIR)/angel_io.hpp $(IDIR)/eliminations.hpp
	$(CXX) $(CXXFLAGS) $(CPPFLAGS) -o $@ heuristics.cpp

graph_generator.o: graph_generator.cpp $(IDIR)/graph_generator.hpp $(IDIR)/angel_types.hpp \
		 $(IDIR)/angel_tools.hpp
	$(CXX) $(CXXFLAGS) $(CPPFLAGS) -o $@ graph_generator.cpp

sa.o: sa.cpp $(IDIR)/sa.hpp $(IDIR)/sa_impl.hpp $(IDIR)/angel_types.hpp \
		 $(IDIR)/angel_tools.hpp \
		 $(IDIR)/angel_io.hpp \
		 $(IDIR)/eliminations.hpp $(IDIR)/heuristics.hpp
	$(CXX) $(CXXFLAGS) $(CPPFLAGS) -o $@ sa.cpp

angel_comm.o: angel_comm.cpp $(IDIR)/angel_comm.hpp $(IDIR)/angel_comm_impl.hpp \
		$(IDIR)/angel_types.hpp \
		$(IDIR)/gmpi.hpp $(IDIR)/gmpi_impl.hpp 
	$(CXX) $(CXXFLAGS) $(CPPFLAGS) -o $@ angel_comm.cpp

xaif_interface.o: xaif_interface.cpp $(IDIR)/xaif_interface.hpp $(IDIR)/angel_types.hpp \
		 $(IDIR)/eliminations.hpp $(IDIR)/heuristics.hpp
	$(CXX) $(CXXFLAGS) $(CPPFLAGS) -o $@ xaif_interface.cpp











