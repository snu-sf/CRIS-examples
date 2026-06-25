COQMODULE    := CRISEXAMPLES
CRISMODULE	 := CRIS
COQTHEORIES  := $(shell find . \( -path "./deprecated" -o -path "./_opam" -o -path "./$(CRISMODULE)" \) -prune -o -type f -not -name '.*.v' -iname '*.v' -print)
COQDIRS      := $(sort $(patsubst ./%,%,$(shell for f in $(COQTHEORIES); do d=$${f%/*}; while [ "$$d" != "." ]; do printf "%s\n" "$$d"; d=$${d%/*}; done; done)))
COQDIR_THEORIES = $(filter ./$@/%.v,$(COQTHEORIES))
COQGOALS     := $(filter %.vo %.vos,$(MAKECMDGOALS))

.PHONY: all all-quick FORCE $(COQDIRS)

ifneq ($(COQGOALS),)
.PHONY: $(COQGOALS) __coq_goals

$(COQGOALS): __coq_goals ;

__coq_goals: Makefile.coq
	$(MAKE) -f Makefile.coq $(COQGOALS)
else
%.vo: Makefile.coq %.v FORCE
	$(MAKE) -f Makefile.coq $@

%.vos: Makefile.coq %.v FORCE
	$(MAKE) -f Makefile.coq $@
endif

all: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQTHEORIES))
all-quick: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(COQTHEORIES))

$(COQDIRS): Makefile.coq
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
	 echo "-R $(CRISMODULE)/itreeS ITreeS"; \
	 echo "-R $(CRISMODULE)/theories $(CRISMODULE)"; \
	 echo "-R $(CRISMODULE)/library $(CRISMODULE)"; \
	 echo "-R $(CRISMODULE)/extract $(CRISMODULE)"; \
	 echo "-R sequential/imp_system $(CRISMODULE).imp_system"; \
	 echo "-R sequential/cannon $(CRISMODULE).cannon"; \
	 echo "-R sequential/cellio $(CRISMODULE).cellio"; \
	 echo "-R sequential/celliocb $(CRISMODULE).celliocb"; \
	 echo "-R sequential/celliostk $(CRISMODULE).celliostk"; \
	 echo "-R sequential/hybrid_mem $(CRISMODULE).hybrid_mem"; \
	 echo "-R sequential/knot $(CRISMODULE).knot"; \
	 echo "-R sequential/map $(CRISMODULE).map"; \
	 echo "-R sequential/mutsum $(CRISMODULE).mutsum"; \
	 echo "-R sequential/repeat $(CRISMODULE).repeat"; \
	 echo "-R sequential/ring $(CRISMODULE).ring"; \
	 echo "-R sequential/single_coin $(CRISMODULE).single_coin"; \
	 echo "-R concurrent/promise_free $(CRISMODULE).promise_free"; \
	 echo "-R concurrent/scheduler $(CRISMODULE).scheduler"; \
	 echo "-R concurrent/incr $(CRISMODULE).incr"; \
	 echo "-R concurrent/spinlock $(CRISMODULE).spinlock"; \
	 echo "-R concurrent/IO_proxy $(CRISMODULE).IO_proxy"; \
	 echo "-R concurrent/priority_queue $(CRISMODULE).priority_queue"; \
	 echo "-R concurrent/elimination_stack $(CRISMODULE).elimination_stack"; \
	 echo "-R concurrent/hwqueue $(CRISMODULE).hwqueue"; \
	 echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	@# Do not delegate to Makefile.coq here: its generated clean target
	@# follows _CoqProject paths, including the CRIS checkout.
	@# Make sure not to enter the CRIS submodule, `_opam`, or hidden folders.
	find . -mindepth 1 \( -path "./$(CRISMODULE)" -o -path "./_opam" -o -name ".*" \) -prune -o -type f \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vos" \) -print -exec rm -f {} + || true
	rm -f _CoqProject Makefile.coq Makefile.coq.conf #Makefile.coq-rsync Makefile.coq-rsync.conf
.PHONY: clean

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
