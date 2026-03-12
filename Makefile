COQMODULE    := CRISEXAMPLES
CRISMODULE	 := CRIS
COQTHEORIES  := $(shell find . -not -path "./deprecated/*" -not -path "./_opam/*" -iname '*.v')

.PHONY: all all-quick

%.vo: %.v
	$(MAKE) -f Makefile.coq $@

%.vos: %.v
	$(MAKE) -f Makefile.coq $@

all: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQTHEORIES))
all-quick: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(COQTHEORIES))

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-arg -w -arg -deprecated-hint-without-locality"; \
	 echo "-arg -w -arg -deprecated-instance-without-locality"; \
	 echo "-arg -w -arg -notation-incompatible-prefix"; \
	 echo "-arg -w -arg -notation-overriden"; \
	 echo "-arg -w -arg -ambiguous-paths"; \
	 echo "-arg -w -arg -redundant-canonical-projection"; \
	 echo "-arg -w -arg -cannot-define-projection"; \
	 echo "-R $(CRISMODULE)/theories $(CRISMODULE)"; \
	 echo "-R $(CRISMODULE)/scheduler $(CRISMODULE)"; \
	 echo "-R $(CRISMODULE)/apc $(CRISMODULE)"; \
	 echo "-R $(CRISMODULE)/prophecy $(CRISMODULE)"; \
	 echo "-R $(CRISMODULE)/imp_system $(CRISMODULE)"; \
	 echo "-R $(CRISMODULE)/extract $(CRISMODULE)"; \
	 echo "-R $(CRISMODULE)/helping $(CRISMODULE)"; \
	 echo "-R cannon $(CRISMODULE).cannon"; \
	 echo "-R cellio $(CRISMODULE).cellio"; \
	 echo "-R celliocb $(CRISMODULE).celliocb"; \
	 echo "-R elimination_stack $(CRISMODULE).elimination_stack"; \
	 echo "-R hybrid_mem $(CRISMODULE).hybrid_mem"; \
	 echo "-R incr $(CRISMODULE).incr"; \
	 echo "-R knot $(CRISMODULE).knot"; \
	 echo "-R map $(CRISMODULE).map"; \
	 echo "-R mutsum $(CRISMODULE).mutsum"; \
	 echo "-R priority_queue $(CRISMODULE).priority_queue"; \
	 echo "-R promise_free $(CRISMODULE).promise_free"; \
	 echo "-R repeat $(CRISMODULE).repeat"; \
	 echo "-R ring $(CRISMODULE).ring"; \
	 echo "-R scheduler $(CRISMODULE).scheduler"; \
	 echo "-R single_coin $(CRISMODULE).single_coin"; \
	 echo "-R spinlock $(CRISMODULE).spinlock"; \
	 echo "-R hwqueue $(CRISMODULE).hwqueue"; \
	 echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean || true
	@# Make sure not to enter the `_opam` folder.
	find [a-z]*/ \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vos" \) -print -delete || true
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
