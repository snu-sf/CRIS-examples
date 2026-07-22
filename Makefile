COQMODULE    := CRISEXAMPLES
CRISMODULE	 := CRIS
ROCQ         ?= rocq
COQTHEORIES  := $(shell find . \( -path "./deprecated" -o -path "./_opam" -o -path "./$(CRISMODULE)" \) -prune -o -type f -not -name '.*.v' -iname '*.v' -print)
COQDIRS      := $(sort $(patsubst ./%,%,$(shell for f in $(COQTHEORIES); do d=$${f%/*}; while [ "$$d" != "." ]; do printf "%s\n" "$$d"; d=$${d%/*}; done; done)))
COQDIR_THEORIES = $(filter ./$@/%.v,$(COQTHEORIES))
COQGOALS     := $(filter %.vo %.vos,$(MAKECMDGOALS))
CRISGOAL     := $(if $(filter %.vo,$(COQGOALS)),cris,$(if $(filter %.vos,$(COQGOALS)),cris-quick))

.PHONY: all all-quick cris cris-quick FORCE $(COQDIRS)

ifneq ($(COQGOALS),)
.PHONY: $(COQGOALS) __coq_goals

$(COQGOALS): __coq_goals ;

__coq_goals: $(CRISGOAL) Makefile.coq
	$(MAKE) -f Makefile.coq $(COQGOALS)
else
%.vo: cris Makefile.coq %.v FORCE
	$(MAKE) -f Makefile.coq $@

%.vos: cris-quick Makefile.coq %.v FORCE
	$(MAKE) -f Makefile.coq $@
endif

all: cris Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQTHEORIES))
all-quick: cris-quick Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(COQTHEORIES))

cris:
	$(MAKE) -C $(CRISMODULE) all

cris-quick:
	$(MAKE) -C $(CRISMODULE) all-quick

$(COQDIRS): cris Makefile.coq
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQDIR_THEORIES))

FORCE:

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-arg -w -arg -deprecated-hint-without-locality"; \
	 echo "-arg -w -arg -deprecated-instance-without-locality"; \
	 echo "-arg -w -arg -notation-incompatible-prefix"; \
	 echo "-arg -w -arg -notation-overriden"; \
	 echo "-arg -w -arg -ambiguous-paths"; \
	 echo "-arg -w -arg -redundant-canonical-projection"; \
	 echo "-arg -w -arg -cannot-define-projection"; \
	 echo "-arg -require-import -arg ExtLib.Structures.Monad"; \
	 echo "-Q $(CRISMODULE)/itreeS ITreeS"; \
	 echo "-Q $(CRISMODULE)/theories $(CRISMODULE)"; \
	 echo "-Q $(CRISMODULE)/library $(CRISMODULE)"; \
	 echo "-Q $(CRISMODULE)/extract $(CRISMODULE)"; \
	 echo "-Q sequential/imp_system $(CRISMODULE).imp_system"; \
	 echo "-Q sequential/cannon $(CRISMODULE).cannon"; \
	 echo "-Q sequential/cellio $(CRISMODULE).cellio"; \
	 echo "-Q sequential/celliocb $(CRISMODULE).celliocb"; \
	 echo "-Q sequential/celliostk $(CRISMODULE).celliostk"; \
	 echo "-Q sequential/hybrid_mem $(CRISMODULE).hybrid_mem"; \
	 echo "-Q sequential/knot $(CRISMODULE).knot"; \
	 echo "-Q sequential/map $(CRISMODULE).map"; \
	 echo "-Q sequential/mutsum $(CRISMODULE).mutsum"; \
	 echo "-Q sequential/repeat $(CRISMODULE).repeat"; \
	 echo "-Q sequential/ring $(CRISMODULE).ring"; \
	 echo "-Q sequential/single_coin $(CRISMODULE).single_coin"; \
	 echo "-Q concurrent/promise_free $(CRISMODULE).promise_free"; \
	 echo "-Q concurrent/scheduler $(CRISMODULE).scheduler"; \
	 echo "-Q concurrent/incr $(CRISMODULE).incr"; \
	 echo "-Q concurrent/spinlock $(CRISMODULE).spinlock"; \
	 echo "-Q concurrent/IO_proxy $(CRISMODULE).IO_proxy"; \
	 echo "-Q concurrent/priority_queue $(CRISMODULE).priority_queue"; \
	 echo "-Q concurrent/elimination_stack $(CRISMODULE).elimination_stack"; \
	 echo "-Q concurrent/hwqueue $(CRISMODULE).hwqueue"; \
	 echo $(COQTHEORIES)) > _CoqProject
	$(ROCQ) makefile -f _CoqProject -o Makefile.coq

clean:
	@# Do not delegate to Makefile.coq here: its generated clean target
	@# follows _CoqProject paths, including the CRIS checkout.
	@# Make sure not to enter the CRIS submodule, `_opam`, or hidden folders.
	find . -mindepth 1 \( -path "./$(CRISMODULE)" -o -path "./_opam" -o -name ".*" \) -prune -o -type f \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vos" \) -print -exec rm -f {} + || true
	rm -f _CoqProject Makefile.coq Makefile.coq.conf #Makefile.coq-rsync Makefile.coq-rsync.conf

clean-all: clean
	$(MAKE) -C $(CRISMODULE) clean
.PHONY: clean clean-all

# Install build-dependencies
OPAMFILES=$(wildcard *.opam)
BUILDDEPFILES=$(addsuffix -builddep.opam, $(addprefix builddep/,$(basename $(OPAMFILES))))

builddep/%-builddep.opam: %.opam Makefile
	@echo "# Creating builddep package for $<."
	@mkdir -p builddep
	@sed <$< -E 's/^(build|install|remove):.*/\1: []/; s/"(.*)"(.*= *version.*)$$/"\1-builddep"\2/;' >$@

builddep-opamfiles: $(BUILDDEPFILES)
.PHONY: builddep-opamfiles

builddep: builddep-opamfiles
	@# We want opam to not just install the build-deps now, but to also keep satisfying these
	@# constraints.  Otherwise, `opam upgrade` may well update some packages to versions
	@# that are incompatible with our build requirements.
	@# To achieve this, we create a fake opam package that has our build-dependencies as
	@# dependencies, but does not actually install anything itself.
	@echo "# Installing builddep packages."
	@opam install $(OPAMFLAGS) $(BUILDDEPFILES)
.PHONY: builddep
