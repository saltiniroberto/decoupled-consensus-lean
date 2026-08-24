# Handover — 2026-08-24, mid-sweep, before a compaction

A snapshot, not a record: `CONTEXT.md` is the record. Delete this file once read.

## Where things stand

`main`, tree about to be committed as one WIP commit, `lake build Spec` green (726 jobs).
Today so far: the repository narrowed to the spec + extractor (branch
`pre-consensus1-purge` holds everything removed; local `pre-purge/` is its tree as plain
files); the spec relaid to `lean/Spec/` + `lean/Spec/Defs/`; `Analysis/AccountableSafety.lean`
(statements only, as `Prop`s); `doc/guide.md`; README rewritten twice (now: navigation only,
protocol identity "Ethereum decoupled consensus", no protocol description, no local-file
references); `make extract` → `extract/out/dc.pdf`; a large in-progress sweep removing from
all docstrings (a) references to consensus-1.pdf, its Definition/Section/figure-line
numbers ("assume no knowledge of consensus-1.pdf" — the spec is the source of truth), and
(b) ALL history narration (history belongs in CONTEXT.md only). `FinalityVote.lean` just
moved from `Defs/` to the spec root (Roberto's word), imports fixed.

## Pending, in order

1. **Finish the history/reference sweep** (Roberto, emphatic, twice). Known remaining:
   - `FinalityVote.lean`: delete the whole "## What changed in the crossing" section
     (lines ~32–70; CONTEXT.md already records it); fix the finalityVote docstring's
     "The source's certificate-knowledge condition is not carried over — see the module
     header" → inline: justification is an on-chain fact, the chain is its own evidence.
   - `Fig2GoldfishDuties.lean:23` "as the previous rendering did" → drop.
   - `Fig6StateTransition.lean:43` same phrase → drop; `:36` "The previous draft" → drop.
   - `Model.lean` `Message` docstring second paragraph (first-specification narration) →
     rewrite: attestations travel on the wire so `Store.fgVote` can be a duty; blocks
     carry the ones a proposer includes.
   - `Fig7FGStore.lean:10` "shares a draft name" → "shares a name".
   - `FinsetM.lean:15` the "(Until the 2026-08-24 purge …)" parenthetical → delete.
   - `OldDefs.lean`: entries lose their "From `X.lean` … superseded/dissolved" narration —
     keep only what each is and what revives it; header likewise.
   - Residual `draft` tokens: `Notation.lean:21,102`, `Fig5SGDuty.lean:39` (an
     `## Extract` section — extractor prose, edit the word only), `Store.lean:253`
     ("Not draft content:"), `OldDefs.lean:21–22`.
   - Then `grep -rn "draft\|Definition [0-9]\|Section [0-9]\|rendering" lean/` until only
     legitimate hits remain (file-count phrases like "Figure 6 of seven" are fine; "Figure
     N's `foo`" is fine — it names our own Fig files).
2. **Merge `Defs/Duty.lean` into `Defs/Nondet.lean`** (Roberto: the name makes no sense
   now). Nondet gains `import Spec.Defs.Store` (acyclic — nothing below Store imports
   Nondet); NDREB/broadcast/outcomes move; Duty.lean deleted; importers (Fig2, Fig5,
   FinalityVote, Spec.lean) fixed; doc pages + CONTEXT mentions of `Duty.lean` updated.
3. **`doc/guide.md`**: add a "typing the symbols" section (Roberto: `←` is `\l` or
   `\gets`, `←ᵖ` is `\l\^p`, `∈ᴹ` is `\in\^M`, `⪯` `\preceq`, `⊥` `\bot`, `σ` `\sigma`,
   `Σ` shows as `S` in code, `Δ` `\Delta`, `∪` `\cup`, `∅` `\empty`, `≠` `\ne`, `∃`
   `\exists`, `≥` `\ge`, `⟨⟩` `\<` `\>`, `←ᵖ` etc. — VS Code Lean abbreviations); and
   de-draft the guide (it still says "matches the draft's pseudocode", "if you can read
   the draft" — reword to paper-pseudocode with no external document).
4. **doc/README.md**: move the `FinalityVote.lean` row from the Defs table to the root
   table (it moved); drop `Duty.lean` from the vocabulary row after the merge. README's
   Defs sentence mentions FinalityVote too.
5. **CONTEXT.md entries** for: the identity shift + README front door; `make extract` /
   `dc.pdf`; the no-local-references rule; the de-referencing sweep ("the spec is the
   source of truth"); FinalityVote to the root; the Duty→Nondet merge.
6. Roberto's question, answered in the last message but relevant to next steps: the
   extract order is the hardcoded `FILE_ORDER` list in `extract/extract.py` (~line 65),
   stems in document order, read from `extract/Consensus1-frozen/`. **The frozen copy
   predates `FinalityVote.lean`, `SigningHistory.lean` and `Duty.lean`**, so the extracted
   document has none of them until a frozen refresh (which happens only on his
   instruction) plus a `FILE_ORDER` update.

## Standing constraints (fresh-session traps)

- Docstrings: no history, no consensus-1.pdf/Definition/Section references, no local-file
  references. History → CONTEXT.md; local paths → CONTEXT_LOCAL.md.
- The extractor (`extract/`) is co-edited by a parallel session — don't rewrite its
  conventions, only what Roberto orders (dc.pdf rename done).
- Heredocs containing `/--` are denied by a hook: patch scripts go in `scratch/` via the
  Write tool.
- `make check` must stay green; statements-of-record are `Prop` defs, not `sorry`s.
- Commit at stopping points, split by concern, `Co-Authored-By: Claude Fable 5`.
