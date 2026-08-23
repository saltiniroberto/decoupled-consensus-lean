# Paper snapshots

Point-in-time builds of `latex-specs` papers, each named by the full commit hash it was
built from, with the tex that generated it kept beside the PDF. The submodule's own
checkout is never moved for these: the tree is taken with `git archive` and built in a
scratch directory with `make paper`'s recipe (`latexmk -pdf`).

| Files | Paper | Commit |
| --- | --- | --- |
| `d1ebd70ef746ac1da1909d3f3c35286fa4396c64.{pdf,tex}` | `height_filter_healing.tex` | `d1ebd70` — "Simplify fresh quorum syncing to a root pointer" (2026-08-24 snapshot). At this commit the paper is standalone: `recovery_core.tex` does not exist yet, so the one tex file is the whole source apart from the shared setup files (`commands.tex`, `full/`), which are in the submodule's history. |

To reproduce one:

    git -C latex-specs archive <hash> | tar -x -C <scratch>
    cd <scratch> && latexmk -pdf -interaction=nonstopmode height_filter_healing.tex
