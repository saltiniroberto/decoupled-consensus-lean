.PHONY: help check dev sorry sorries nodecide orphans build cache extract submodules

# `native_decide` is never acceptable: it moves a claim off the kernel and onto the compiler,
# which no amount of later work discharges. Every target refuses it.
NEVER_RE := (^|[^`[:alnum:]_])native_decide([^`[:alnum:]_]|$$)

# `sorry` and `admit` are placeholders for a proof not yet written. `make dev` allows them and
# counts them; `make check` refuses them. Mentions inside backticks are exempt, which is why
# each pattern requires the token not to be preceded by one.
WIP_RE := (^|[^`[:alnum:]_])(sorry|admit)([^`[:alnum:]_]|$$)

# Excludes deps/, another project's sources and not ours to police, and latex-specs/, a
# local-only checkout of the old papers.
SCAN := --include=*.lean . --exclude-dir=deps --exclude-dir=.lake --exclude-dir=latex-specs

help:
	@echo 'The two targets that matter:'
	@echo
	@echo 'make dev        - working target: native_decide check, count the outstanding'
	@echo '                  sorry/admit, then build. Allows sorry.'
	@echo 'make check      - strict target: the same, except that any sorry/admit fails it.'
	@echo '                  Nothing may be outstanding. Use before committing a proof.'
	@echo
	@echo 'make cache      - fetch prebuilt Mathlib artefacts (do this before a first build)'
	@echo 'make sorries    - list every outstanding sorry/admit, without failing'
	@echo 'make orphans    - find .lean files under lean/ that no lean_lib glob claims'
	@echo 'make build      - build this project'
	@echo 'make extract    - render the spec into a paper-shaped PDF (extract/out/dc.pdf)'
	@echo 'make submodules - report the pinned revision of each submodule'

# The strict target: no sorry, no admit, no native_decide, build is green.
check: nodecide orphans sorry build

# The working target: everything `check` does except the sorry-free requirement, with the
# outstanding count reported instead.
dev: nodecide orphans sorries build

# A .lean file under lean/ that no lean_lib glob claims is always a mistake: Lake never reads
# it, so it can be stale or outright broken while every other target stays green. That has
# happened -- an editor tab left open on a path two layout moves out of date was saved and
# recreated a whole stale directory, invisible to the build.
orphans:
	@bad=`find lean -name '*.lean' \
	    ! -path 'lean/Spec.lean' ! -path 'lean/Spec/*' \
	    ! -path 'lean/SpecM.lean' ! -path 'lean/SpecM/*' \
	    ! -path 'lean/Analysis.lean' ! -path 'lean/Analysis/*'`; \
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
