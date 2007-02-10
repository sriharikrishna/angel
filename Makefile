# $Id: Makefile,v 1.9 2004/10/16 04:18:17 jean_utke Exp $

ifeq "$(strip $(config))" ""
	angel_config:=gnu
else
	angel_config:=$(config)
endif

include specs/$(angel_config).conf

# usage of other libraries (architecture (or compiler version) independent part of def)
include specs/lib_usage.conf

ifeq "$(strip $(usexaif))" "yes"
  CPPFLAGS	+= -DUSE_XAIF
  CPPFLAGS	+= -I$(XAIF_DIR)
endif

.PHONY:	it lib objects doc clean dist echo

it: 	lib 

lib:	lib/libangel.a

lib/libangel.a:	objects
	$(RM) $(RMFLAGS) $@
	$(AR) $(ARFLAGS) $@ src/*.o

objects:
	cd src && $(MAKE) 

doc:
	doxygen Doxyfile
	cd doc/latex && $(MAKE)

clean:
	cd src && $(MAKE) clean 
	$(RM) $(RMFLAGS) lib/libangel.a
	$(RM) $(RMFLAGS) doc/latex doc/html

echo:
	cd src && $(MAKE) echo 

dist:
	cd .. && tar -zcvf angel.tgz --no-recursion angel/Makefile angel/*/Makefile angel/src/*.cpp \
		angel/include/*.hpp angel/lib \
		angel/Doxyfile angel/specs/*.conf 
