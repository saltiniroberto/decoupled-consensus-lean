.PHONY: help check dev sorry sorries nodecide orphans build cache cites mapping index paper submodules

# `native_decide` is never acceptable: it moves a claim off the kernel and onto the compiler,
# which no amount of later work discharges. Every target refuses it.
NEVER_RE := (^|[^`[:alnum:]_])native_decide([^`[:alnum:]_]|$$)

# `sorry` and `admit` are placeholders for a proof not yet written. `make dev` allows them and
# counts them; `make check` refuses them. Mentions inside backticks are exempt, which is why
# each pattern requires the token not to be preceded by one.
WIP_RE := (^|[^`[:alnum:]_])(sorry|admit)([^`[:alnum:]_]|$$)

# Excludes deps/, another project's sources and not ours to police.
SCAN := --include=*.lean . --exclude-dir=deps --exclude-dir=.lake

help:
	@echo 'The two targets that matter:'
	@echo
	@echo 'make dev        - working target: native_decide check, count the outstanding'
	@echo '                  sorry/admit, citation check, then build. Allows sorry.'
	@echo 'make check      - strict target: the same, except that any sorry/admit fails it.'
	@echo '                  Nothing may be outstanding. Use before committing a proof.'
	@echo
	@echo 'make cache      - fetch prebuilt Mathlib artefacts (do this before a first build)'
	@echo 'make sorries    - list every outstanding sorry/admit, without failing'
	@echo 'make orphans    - find .lean files under lean/ that no lean_lib glob claims'
	@echo 'make build      - build this project'
	@echo 'make cites      - check every citation of the paper against its .aux'
	@echo 'make mapping    - regenerate mapping.html from MAPPING.md'
	@echo 'make index      - regenerate INDEX.tsv, one row per declaration'
	@echo 'make paper      - build latex-specs/height_filter_healing.pdf and its .aux'
	@echo 'make submodules - report the pinned revision of each submodule'
	@echo
	@echo 'mapping.html'"'"'s figures column stays empty until there is a FigureDeps.lean to'
	@echo 'run against a built library.'

# The strict target: no sorry, no admit, no native_decide, citations agree, build is green.
check: nodecide orphans sorry cites build

# The working target: everything `check` does except the sorry-free requirement, with the
# outstanding count reported instead.
dev: nodecide orphans sorries cites build

# A .lean file under lean/ that no lean_lib glob claims is always a mistake: Lake never reads
# it, so it can be stale or outright broken while every other target stays green. That has
# happened -- an editor tab left open on a path two layout moves out of date was saved and
# recreated lean/specs/Decoupled/Spec/ as an untracked copy, invisible to the build.
orphans:
	@bad=`find lean -name '*.lean' \
	    ! -path 'lean/Spec.lean' ! -path 'lean/Spec/*' \
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

# Docstrings and MAPPING.md cite the paper by \label, printed number and line span. The label
# is durable; the other two rot silently when the paper is edited, and a Lean build cannot
# notice. Skips with a notice when the paper has not been built, since the .aux it reads is an
# artefact the submodule does not carry -- `make paper` produces it.
cites:
	@python3 tools/check_citations.py

# Neither of these is part of `check` or `dev`: each rewrites a committed file.
mapping:
	@python3 tools/mapping_html.py

# Builds first because the types come from the compiled environment, not the sources.
index: build
	lake env lean tools/decl_index.lean

paper:
	cd latex-specs && latexmk -pdf -interaction=nonstopmode height_filter_healing.tex

submodules:
	@git submodule status
