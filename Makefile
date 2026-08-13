.PHONY: help check sorry build cache cites mapping index paper submodules

# Anything that would let a claim escape the kernel. Mentions inside backticks are exempt,
# which is why the pattern requires the token not to be preceded by one.
BANNED_RE := (^|[^`[:alnum:]_])(sorry|admit|native_decide)([^`[:alnum:]_]|$$)

help:
	@echo 'make cache      - fetch prebuilt Mathlib artefacts (do this before a first build)'
	@echo 'make check      - sorry/admit check, citation check, then build'
	@echo 'make build      - build this project'
	@echo 'make cites      - check every citation of the paper against its .aux'
	@echo 'make mapping    - regenerate mapping.html from MAPPING.md'
	@echo 'make index      - regenerate INDEX.tsv, one row per declaration'
	@echo 'make paper      - build latex-specs/height_filter_healing.pdf and its .aux'
	@echo 'make submodules - report the pinned revision of each submodule'
	@echo
	@echo 'Both index and mapping run now and produce empty output, since nothing is'
	@echo 'formalized yet. mapping.html'"'"'s figures column stays empty until there is a'
	@echo 'FigureDeps.lean to run against a built library.'

check: sorry cites build

# Excludes deps/, another project's sources and not ours to police.
sorry:
	@if grep -rnE '$(BANNED_RE)' --include='*.lean' . \
	    --exclude-dir=deps --exclude-dir=.lake; then \
		echo 'FAIL: sorry/admit/native_decide found'; exit 1; \
	else \
		echo 'sorry/admit check passed'; \
	fi

# Warns "no targets specified and no default targets configured" until this project's
# `lean_lib` is uncommented in lakefile.toml. That is expected, not a fault.
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

# Neither of these is part of `check`: each rewrites a committed file.
mapping:
	@python3 tools/mapping_html.py

# Builds first because the types come from the compiled environment, not the sources.
index: build
	lake env lean tools/decl_index.lean

paper:
	cd latex-specs && latexmk -pdf -interaction=nonstopmode height_filter_healing.tex

submodules:
	@git submodule status
