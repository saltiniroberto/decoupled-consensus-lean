# `extract/` — the document-extraction workstream

The goal (Roberto, 2026-08-23): a script that extracts, out of the `Spec/Consensus1/`
Lean files, a document similar to the source `consensus-1.pdf`.

## Prose is opt-in: the `## Extract` marker

Roberto, 2026-08-24. A module header or docstring section headed `## Extract` is document
prose; everything unmarked is Lean-side commentary and stays out of the PDF. The default
was chosen deliberately: marked text is written *for* the document, so it can read like
the draft, and new commentary stays out without anyone remembering to fence it.

- In a module header: the section becomes the file's section prose. `## Extract — X`
  gives it subsection title `X`.
- In a figured routine's docstring: the section leads that routine's figure in, the way
  the draft's prose introduces each figure.
- In any other declaration's docstring: the section follows the figure.

Marked prose renders in the draft's typography: backticked spans go through the same
rewriter as the figures, and fall back to mono exactly when they quote Lean.

**The durable home for these sections is the live spec's headers** — a refresh of the
frozen copy wipes anything written only here. Since 2026-08-24 all nine module headers
carry their section, in the live spec and mirrored in the frozen copy, adapted from the
draft's own section prose.

## The conventions the extractor harvests

No rewrite rule names an identifier of the spec. Instead, `extract.py` builds its rename
tables from these conventions, so a spec written with them extracts without touching the
script:

- **A docstring that opens with a backticked paper form names the declaration's symbol
  and access shape.** `` `Σ.gf_votes[k]` `` gives the field name and the bracket read;
  `` `Σ.timestamp(B)` `` a parenthesized read; `` `t_s = 4Δs` `` the subscripted symbol
  `t_s` (the part before `=`, the subscript matched against the parameter name);
  `` `B_gen` `` a plain symbol; `` `Q_target(σ) = {…}` `` a call form. A docstring that
  does not open with a backtick contributes nothing.
- **A figure citation names a routine.** `` `name(args)` (Figure N, lines a–b)`` in the
  docstring's first paragraph gives the paper name, the paper signature, the figure the
  routine's pseudocode belongs to, and its position. Lean parameters absent from the
  cited signature (the validator `i`, the `isProposer` test) stay hidden at call sites,
  exactly as the draft's own calls hide them.
- **A section headed `## Extract — Definition (Title)` is a definition block**, rendered
  as the draft's definition environment: bold "Definition N (Title)." running into the
  section's first paragraph, later paragraphs following as plain prose. **N is assigned
  by the extractor, sequentially in document order** — the Lean is the source of truth
  and the PDF is generated from it, so no number is read from a docstring (Roberto,
  2026-08-24). The docstrings' "(Definition N of the draft)" citations are provenance,
  pointing at the old source; the generated numbers coincide with the draft's today
  because the document order matches, a consequence and not a contract.
- **A structure whose field docstrings open `X.…` is the paper's `X`.** The store's
  fields open `` `Σ.…` ``, so `Store` is `Σ` and every store-typed parameter renders
  `Σ`.
- **"the tuple `(…)`" in a structure's docstring makes its constructor a tuple** — the
  way the draft writes votes, `(v, s, B)`. Other constructors render as
  "a *name* with .f = e, …".
- **A constructor docstring's tuple over its own parameter names is a template.**
  `` `(h, ⊥)` `` on `emptyTarget (h : Nat)` renders `.emptyTarget σ.h` as `(σ.h, ⊥)`.
- **Fallbacks.** A class field with no opening symbol renders namespace-stripped, call
  form with the arity of its type — `Committees.K s` renders `K(s)` until the docstring
  opens with `` `K_s` ``. An uncited `def` renders as a snake-cased small-caps call. All
  names convert camelCase → snake_case; names without an internal case boundary (`B`,
  `T_h`, `S'`) stay.

## The rewrite rules, by what each is keyed on

**Keyed on this style's conventions** — the two flagged rules are the only ones that
would misfire on a spec using the same spellings differently:

- `return { state := σ, send := M }` renders "**broadcast** m; ⟨call⟩" — keyed on the
  literal field names `state`/`send`, the lean-sts step shape (**flagged**);
- inside a send set, a one-argument constructor wrapper `Qualified.ctor x` strips to
  `x` — the `Message` convention (**flagged**);
- `let mut S := S` (the shadow copy of a parameter) is dropped;
- `for _ in [:e]` is the figure's bounded **loop**; `←ᵖ` is kept; `∈ᴹ` renders `∈`;
- `-- line n` / `-- lines a–b` comments give the printed line numbers, their trailing
  text the `▷` margin note, dropped when it merely echoes the rewritten code;
- two peepholes: `X ← call` followed by `return {state := X, send := ∅}` collapses to
  the call, and an unnumbered field assignment joins its numbered predecessor with `;`.

**Keyed on Lean/Mathlib names:** `filterM` fuses into a set-builder, `imageM` renders
`{e : x ∈ s}`, `biUnion` renders `⋃{…}`; `.toNat` strips (`⌊…⌋` over a division),
`.toFinset`, `.run`, `.get h`, `some`, `pure`, `↑` and type ascriptions strip;
`.isSome` renders `≠ ⊥`; `.getD d` drops — **the one lossy rule**, Figure 7's line 15
shows `max{…}` without the empty-set default the Lean carries; `max`/`min`/`abs`/
`Finset.range` render call-style.

**Keyed on Lean surface syntax:** every binder (`let`, `let mut`, `:=`, `x := (← e)`)
renders `←`; let-type annotations and `if _ : c` binders drop; top-level `∧`/`∨` render
**and**/**or**, `∧` inside a set-builder a comma; `{x ∈ s | p}` renders `{x ∈ s : p}`;
`for x in s` renders **for all** `x ∈ s`; `x := fun y => e` renders **define** `x(y)`
**as** `e`; `fun x => f a x` eta-folds to `f(a, ·)`; `X ← X ∪ {e}` renders **add** `e`
**to** `X`; `return ← call` renders the call, `return S` of the mutated store a bare
**return**, a final bare expression **return** `e`; parens drop around atoms,
operator-free groups and call arguments; `n * x` renders as a juxtaposed product, `*`
as `·`, `-` as `−`, `%` as **mod**.

**Typography, figures and prose alike:** keywords bold, cited routine names small caps,
variables italic, field names sans, Greek upright, `x_y` and `t_{s−1}` subscripted. In
`## Extract` prose a backticked span renders through the rewriter unless it quotes Lean
— the mono-fallback triggers are `let`/`fun`/`do`/`mut`/`:=`/`=>`/`←ᵖ`/`∈ᴹ` tokens,
camelCase names, and Type-looking uppercase names, Greek-initial exempt. A
paper-spelled routine name takes small caps, and a single parenthesized comma tuple
after a callable is its argument list, so prose writes calls in paper form.

## `Consensus1-frozen/`

A plain copy of `lean/Spec/Consensus1/` (the `.lean` files, without `doc/`), frozen at
commit `909b4f6` on 2026-08-23. It exists so the extraction script has a stable input
while the live spec keeps changing in parallel.

Rules:

- **The live spec is `lean/Spec/Consensus1/`.** Nothing imports the frozen copy, no build
  target reads it (`lake`'s globs claim only `lean/`, and `make orphans` scans only
  `lean/`), and no spec change is made here.
- The copy is refreshed deliberately, on instruction — re-copy and update the commit hash
  above — never as a side effect of editing the live spec.
