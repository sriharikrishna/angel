# Makefile in latex is overwritten by doxygen. So, clean and distclean is defined here 

include ../specs/$(angel_config).conf

.PHONY:	doc clean distclean

doc:
	#cd latex && $(MAKE) && cd .. # use Makefile from doxygen

clean:
	cd latex && $(RM) $(RMFLAGS) *~ *.dvi *.aux *.toc *.idx *.ind *.ilg *.log *.out && cd ..

distclean:	clean
	cd latex && $(RM) $(RMFLAGS) *.tex *.ps *.pdf && cd ..
	cd man/man3 && $(RM) $(RMFLAGS) *.3 && cd ../..
	cd html && $(RM) $(RMFLAGS) *.html *.css *.png *.repository && cd ..
