.PHONY: help check dev spec proofs sorry sorries nodecide orphans build cache extract submodules

# `native_decide` is never acceptable: it moves a claim off the kernel and onto the compiler,
# which no amount of later work discharges. Every target refuses it.
NEVER_RE := (^|[^`[:alnum:]_])native_decide([^`[:alnum:]_]|$$)

# `sorry` and `admit` are placeholders for a proof not yet written. `make dev` allows them and
# counts them; `make check` refuses them. Mentions inside backticks are exempt, which is why
# each pattern requires the token not to be preceded by one.
WIP_RE := (^|[^`[:alnum:]_])(sorry|admit)([^`[:alnum:]_]|$$)

# Excludes deps/, another project's sources and not ours to police, and scratch/, where
# gitignored probes may live.
SCAN := --include=*.lean lean --exclude-dir=.lake --exclude-dir=scratch

# The proofs compile with up to 3.5 GB of memory per module; these caps keep a full build of
# the five libraries at about two compiles at a time.
CAPPED := LEAN_NUM_THREADS=2 nice -n 10

help:
	@echo 'make check      - strict target: native_decide and sorry/admit checks, then build the'
	@echo '                  spec and its sts node (the default targets). Nothing may be outstanding.'
	@echo 'make dev        - the same, but counts the outstanding sorry/admit instead of failing.'
	@echo 'make spec       - build the Spec library alone.'
	@echo 'make proofs     - build all five libraries (Spec, Sts, Model, Proofs, EndResults), capped:'
	@echo '                  about 40 minutes, up to 3.5 GB per compile.'
	@echo
	@echo 'make cache      - fetch prebuilt Mathlib artefacts (do this before a first build)'
	@echo 'make sorries    - list every outstanding sorry/admit, without failing'
	@echo 'make orphans    - find .lean files under lean/ that no lean_lib glob claims'
	@echo 'make build      - build the default targets (Spec, Sts)'
	@echo 'make extract    - render the spec into a paper-shaped PDF (extract/out/dc.pdf)'
	@echo 'make submodules - report the pinned revision of each submodule'

# The strict target: no sorry, no admit, no native_decide, build is green.
check: nodecide orphans sorry build

# The working target: everything `check` does except the sorry-free requirement, with the
# outstanding count reported instead.
dev: nodecide orphans sorries build

# The spec alone. A `sorry` under lean/Spec/ fails it: the spec never carries one.
spec: nodecide orphans
	@if grep -rnE '$(WIP_RE)' --include=*.lean lean/Spec; then \
		echo 'FAIL: sorry/admit under lean/Spec'; exit 1; \
	else \
		echo 'no sorry/admit under lean/Spec'; \
	fi
	lake build Spec

# Every library, with the caps above.
proofs: nodecide orphans sorry
	$(CAPPED) lake build Spec Sts Model Proofs EndResults

# A .lean file under lean/ that no lean_lib glob claims is always a mistake: Lake never reads
# it, so it can be stale or broken while every other target stays green.
orphans:
	@bad=`find lean -name '*.lean' \
	    ! -path 'lean/Spec.lean' ! -path 'lean/Spec/*' ! -path 'lean/Sts.lean' \
	    ! -path 'lean/Model.lean' ! -path 'lean/Model/*' \
	    ! -path 'lean/Proofs.lean' ! -path 'lean/Proofs/*' ! -path 'lean/EndResults.lean' \
	    ! -path 'lean/EndResults/*'`; \
	if [ -n "$$bad" ]; then \
		echo "$$bad"; \
		echo 'FAIL: .lean under lean/ claimed by no lean_lib glob in lakefile.toml'; \
		exit 1; \
	else \
		echo 'no orphaned .lean files'; \
	fi

nodecide:
	@if grep -rnE '$(NEVER_RE)' $(SCAN); then \
		echo 'FAIL: native_decide found'; exit 1; \
	else \
		echo 'native_decide check passed'; \
	fi

sorry:
	@if grep -rnE '$(WIP_RE)' $(SCAN); then \
		echo 'FAIL: sorry/admit found. `make dev` allows these; `make check` does not'; \
		exit 1; \
	else \
		echo 'sorry/admit check passed'; \
	fi

# Reports rather than fails: the count is the work left to do.
sorries:
	@n=$$(grep -rnE '$(WIP_RE)' $(SCAN) | wc -l); \
	if [ "$$n" -eq 0 ]; then \
		echo 'no sorry/admit outstanding'; \
	else \
		echo "$$n sorry/admit outstanding:"; \
		grep -rnE '$(WIP_RE)' $(SCAN); \
	fi

build:
	lake build

cache:
	lake exe cache get

extract:
	python3 extract/extract.py

submodules:
	@git submodule status
