prebuild := depend setup
prebuild_out := _CoqProject Makefile.coq Makefile.coq.conf

.PHONY : all
all :

.PHONY : depend
depend :
	@ opam install --deps-only --verbose .

.PHONY : setup
setup :
	@ ./setup.sh

Makefile.coq : _CoqProject
	@ coq_makefile -f $< -o $@

_CoqProject : | __CoqProject
	@ ./setup.sh

ifeq (,$(filter $(prebuild),$(MAKECMDGOALS)))
-include Makefile.coq
endif

.PHONY : clean
clean ::
	@ rm -f $(prebuild_out)
