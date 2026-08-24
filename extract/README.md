# `extract/` — the document-extraction workstream

The goal (Roberto, 2026-08-23): a script that extracts, out of the `Spec/`
Lean files, a document similar to the source `consensus-1.pdf`.

## Prose is opt-in: the `## Extract` marker

Roberto, 2026-08-24. A module header or docstring section headed `## Extract` is document
prose; everything unmarked is Lean-side commentary and stays out of the PDF. The default
was chosen deliberately: marked text is written *for* the document, so it can read like
the draft, and new commentary stays out without anyone remembering to fence it.

- In a module header: the section becomes the file's section prose. `## Extract — X`
  gives it subsection title `X`.
- In a `def`'s docstring: **the marker is what makes the def figured** (Roberto,
  2026-08-24) — rendered as pseudocode in the file's figure — and its prose leads the
  figure in, the way the draft's prose introduces each figure. A bare `## Extract`
  with no prose still figures the def.
- In any other declaration's docstring: the section follows the figure.

The marker also drives the document's structure (Roberto, 2026-08-24): **files render
in alphabetical order of their path under `lean/Spec/`**, a file with nothing marked
emitting no section, and **a file's figured routines render in declaration order**.

Marked prose renders in the draft's typography: backticked spans go through the same
rewriter as the figures, and fall back to mono exactly when they quote Lean.

**The `## Extract` sections live in `lean/Spec/`**, the extractor's input.

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
- **A figured routine's paper form derives from its Lean `def`** (Roberto, 2026-08-24):
  the name snake-cased from the Lean name's tail, the signature from the explicit
  parameters in order, a store-typed parameter shown as its structure's symbol —
  `def goldfishScore (votes …) (s …) (B …)` renders `goldfish_score(votes, s, B)`. A
  docstring that opens with a pure backticked call span `` `name(args)` `` overrides
  the derivation; that is how a paper signature hides Lean-side parameters (the
  validator `i`, the `isProposer` test in `` `on_tick(Σ, t)` ``), which then stay
  hidden at call sites exactly as the draft's own calls hide them.
- **A section headed `## Extract — Definition (Title)` is a definition block**, emitted
  as an `amsthm` environment with label `def:<slugified title>`. **Every number in the
  document is LaTeX's own** — definitions, figures, sections, and, since 2026-08-24,
  the figures' line numbers, which `algorithmicx` assigns to the rendered lines. The
  Lean is the source of truth and the PDF is generated from it, so no number is read
  from a docstring or comment (Roberto, 2026-08-24); the generated numbers coincide
  with the draft's where the content matches, a consequence and not a contract.
  A section title's "Figure N — " prefix is
  likewise stripped in the PDF; the figure is captioned and numbered by LaTeX, with
  label `fig:<file stem>`.
- **Prose never writes a generated number.** `## Extract` prose references figures and
  definitions symbolically — `[fig:Fig2GoldfishDuties]`, `[def:store]` — and the
  extractor emits `Figure~\ref{…}` / `Definition~\ref{…}`, hyperlinked. A dangling
  reference is a LaTeX warning.
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
  opens with `` `K_s` ``. An unfigured `def` with no opening symbol renders as a
  snake-cased small-caps call. All
  names convert camelCase → snake_case; names without an internal case boundary (`B`,
  `T_h`, `S'`) stay.

## The rewrite rules, by what each is keyed on

**Keyed on this style's conventions** — the flagged rules are the only ones that
would misfire on a spec using the same spellings differently:

- **the duty monad is harvested from `broadcast` itself**: the def named `broadcast`
  names the monad in its result type (`NDREB`), a routine typed in that monad is a
  duty, a `broadcast m` statement renders as the draft's bold verb, and a duty's tail
  `return` drops — the draft's duties end on the call (**flagged**: keyed on the
  identifier `broadcast`, the draft's own verb);
- a one-argument constructor wrapper `Qualified.ctor x` on a broadcast message strips
  to `x` — the `Message` convention (**flagged**);
- `return { state := σ, send := M }` renders "**broadcast** m; ⟨call⟩" — the lean-sts
  step shape, keyed on the literal field names `state`/`send`; retired in practice by
  the NDREB revision, kept for the boundary shape (**flagged**);
- `let mut S := S` (the shadow copy of a parameter) is dropped;
- `for _ in [:e]` is the figure's bounded **loop**; `←ᵖ` is kept; `∈ᴹ` renders `∈`;
- any `--` comment in a body is the `▷` margin note of the statement it trails or
  precedes (consecutive comment lines join; a note that merely echoes the rewritten
  code drops; a legacy `line n:` prefix is stripped while the sources still carry
  them — nothing numbers the lines);
- one peephole: `X ← call` followed by `return {state := X, send := ∅}` collapses to
  the call.

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

## The input, and the frozen copies

**The extractor's input is the live spec, `lean/Spec/`** (Roberto, 2026-08-24; read
recursively, `Defs/` included). The `## Extract` sections and every extraction-side
edit live there. A `def` renders as pseudocode when its docstring carries the marker,
so the figures fill in as the spec marks its routines.

**The frozen copies live under `archive/`, outside `extract/`** (Roberto, 2026-08-24:
kept as records, and placed where the extractor cannot access them; nothing reads
them, no build target claims them — `lake`'s globs and `make orphans` scan only
`lean/`). `archive/Consensus1-frozen-2/` is the second freeze (`b145f3c`, 2026-08-24,
the NDREB revision, with the extraction-side docstring edits of its day applied on
top); `archive/Consensus1-frozen/` is the first (`909b4f6`, 2026-08-23,
`DutyResult`-returning duties).
