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

.PHONY:	it lib objects doc clean distclean dist docdist echo

it: 	lib 

lib:	lib/libangel.a

lib/libangel.a:	objects
	$(RM) $(RMFLAGS) $@
	$(AR) $(ARFLAGS) $@ src/*.o

objects:
	cd src && $(MAKE) && cd ..

doc:
	doxygen Doxyfile
	cd doc && $(MAKE) doc && cd ..

clean:
	cd src && $(MAKE) clean && cd ..
	$(RM) $(RMFLAGS) lib/libangel.a

#removes everything but the sources and CVS files
distclean:	clean
	cd src && $(MAKE) distclean && cd ..
	cd doc && $(MAKE) distclean && cd ..

echo:
	cd src && $(MAKE) echo && cd ..

dist:
	cd .. && tar -cf angel.tar --no-recursion angel/Makefile angel/*/Makefile angel/src/*.cpp \
		angel/include/*.hpp angel/lib angel/doc/html \
		angel/Doxyfile angel/specs/*.conf \
	&& gzip angel.tar && cd angel

docdist:
	cd .. && tar -cf angel_doc.tar --no-recursion  \
		angel/lib angel/doc/html/* angel/doc/latex/refman.pdf \
	&& gzip angel_doc.tar && cd angel












