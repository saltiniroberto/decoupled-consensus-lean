# Reading this specification without knowing Lean

This spec is written so that each routine reads like a paper's pseudocode, line for line.
If you can read pseudocode, you can read most of a figure file already. This guide covers
the rest: the notation that is Lean's rather than pseudocode's, and what the types are
telling you. It is a reading guide, not a Lean tutorial — nothing here teaches you to
write proofs.

## The shape of a file

A figure file (`02_GoldfishDuties.lean`, say) contains one routine per pseudocode
routine. Everything between `/--` and `-/` is documentation for the definition below it;
`--` starts a line comment, which the rendered figure shows as a margin note.
The files under `Defs/` hold the data types and the plumbing; the ones whose
header says "this file is not a specification" define notation and can be skipped — they
exist so the figure files can read like pseudocode.

A routine looks like this:

```lean
def Store.processSGVote (S : Store Validator) (vote : SGVote Validator) :
    Store Validator := Id.run do
```

Read: a function named `processSGVote`, taking a store `S` and a `vote`, returning a
`Store`. The `Store.` prefix makes call sites read like pseudocode — `S.processSGVote
vote` is `process_sg_vote(Σ, vote)`, with the store written `S` because `Σ` is reserved
in Lean. `Id.run do` opens an imperative block: statements in order, early `return`
allowed. Inside one, `let x := e` names a value, `let mut S := S` makes a local mutable
copy, and assignments keep the imperative arrow — `S.t ← t`,
`S.gfVotes[k] ← …`. A function without `do` is a single expression.

One convention needs saying once: the protocol builds its layers incrementally, and a
later layer redefines some routines. Lean cannot redefine, so the final reading carries the plain name
(`S.getHead`, `S.processBlock`) and each superseded one is named after its figure
(`Fig1.getHead`, `Fig4.getHead`). If you are looking for "the" fork choice, it is the
one without a figure prefix.

## Reading the types: what a routine can do

The return type is an honest summary of a routine's behaviour. There are five, and they
form a scale:

| Return type | The routine… |
| --- | --- |
| `Store Validator` (plain) | computes a value, nothing else |
| `DRE α` | may **fail** instead of answering |
| `NDR α` | makes an **arbitrary choice**; the result is the set of all possible answers |
| `NDRE α` | both of the above |
| `NDREB Validator α` | both, and it **broadcasts** messages |

Failure first. Some map lookups may find nothing: `S.σ[B]`, the stored state of block
`B`, is undefined if `B` was never processed. Rather than answering with a default, the
read fails, and the failure aborts the whole routine — exactly like an exception, except
that there is deliberately only one, carrying no information. The protocol never fails; a
failure marks a store that correctly-behaving handlers can never build, and "this never
actually happens" is a theorem to be proved, not an assumption made. Inside a `do` block
you see failure-propagation as `←` instead of `:=`: `let σB ← S.σ[B]` means "look up, and
stop here if there is nothing".

Nondeterminism second. Where the protocol says "ties broken arbitrarily" or leaves an
order unspecified, this spec does not secretly pick one. The choice is written with its own
arrow:

```lean
let W ←ᵖ top          -- any maximal-score child; every choice is an outcome
```

and a routine containing such a pick denotes the *set of every result reachable by some
choice*. No run is privileged. This is why there is no function that turns an `NDR` result
back into a single value: extracting one would be making the exact arbitrary decision the
construction exists to avoid. Claims like "the answer does not depend on the tie" become
provable statements — the outcome set has one element.

Broadcasting last. A duty broadcasts and then processes its own message —
`broadcast vote; process_sg_vote(Σ, vote)` — and the Lean says the same:

```lean
broadcast (Message.sgVote vote)
return S.processSGVote vote
```

`broadcast` drops the message into an outbox that accumulates silently across everything
a duty calls; the duty itself just returns the new store. When the tick runs a duty after
another duty, both of their messages are in the outbox — no code collects or merges them.
The outbox becomes visible only at the boundary where a duty's overall effect is stated:
`(S.onTick t p).outcomes` is the set of possible results, each a final store together
with everything broadcast on the way to it.

## Small things you will bump into

**`⊥` and `Option`.** The spec writes `⊥` for an absent block or height. In Lean such a
value has type `Option (Block …)` — either a block or nothing — and `⊥` is the nothing.
Code tests it plainly, `if B.parent ≠ ⊥ then …`, and behind such a test a
read like `let P ← B.parent` extracts the value (and would fail on `⊥`, which the test
has just ruled out).

**Sets.** `Finset α` is a finite set. `{x ∈ s | p x}` filters it, `|s|` is its size,
`∪` and `∈` mean what they say. A condition may quantify — `if ∃ a ∈ votes, a.validator
= v then …` — and this is an executable test, not a proof obligation; Lean checks that
such conditions are decidable and the spec only uses ones that are. One variant to know:
`{x ∈ᴹ s | p}` is a filter whose condition may itself fail (it reads timestamps), so the
whole filter can fail. Blocks carry their votes as a `List` rather than a `Finset`
because a block is transmitted data and lists have an order; the proposer picks that
order nondeterministically, since the protocol doesn't fix one.

**Records.** `Store`, `ChainState` and the messages are records. `S.t` reads a field;
`{ S with t := t }` is a copy of `S` with one field changed — nothing mutates in place,
which is what makes "the store before" and "the store after" both available to theorems.

**Ambient parameters.** Things the protocol treats as globally fixed — the validator set and
weights, `Δ`, the committees — are declared once as *classes* and appear
in signatures as bracketed assumptions: `[Electorate Validator]`, `[Params]`. Read them
as "given the protocol's parameters"; no caller passes them explicitly.

**Preconditions.** A duty scheduled for a specific instant carries that instant as a
hypothesis:

```lean
def Store.sgVote (i : Validator) (S : Store Validator)
    (_ : S.t = SGSchedule.a (round S.s) := by …) : …
```

Read the underscore argument as "requires: the clock is at `a_r`". The `:= by …` part
makes Lean find the justification automatically at each call site — in practice from the
`if` around the call — so the calls stay clean and a call at the wrong instant
simply does not compile.

## Typing the symbols

Reading needs none of this, but the moment you search the files or try an edit you will
want to type the notation. In VS Code with the Lean 4 extension, a backslash abbreviation
turns into the symbol as you type (hovering over any symbol shows its abbreviation):

| Symbol | Type |
| --- | --- |
| `←` | `\l` or `\gets` |
| `⇐` | `\l=` |
| `←ᵖ` | `\l` then `\^p` |
| `∈`, `∈ᴹ` | `\in`, then `\^M` for the monadic one |
| `⪯` | `\preceq` |
| `⊥` | `\bot` |
| `≠` | `\ne` |
| `∃` | `\exists` |
| `≥` | `\ge` |
| `∪` | `\cup` |
| `∅` | `\empty` |
| `σ` | `\sigma` |
| `Δ` | `\Delta` |
| `⟨` `⟩` | `\<` and `\>` |

(`Σ` would be `\Sigma`, but it is reserved in Lean, which is why the code writes the
store as `S`.)

## Where to go deeper

The pages beside this one cover the two designs with real depth:
[nondeterminism.md](nondeterminism.md) for the choice machinery and how results are
consumed, [naming.md](naming.md) for the numbered readings, and
[style.md](style.md) for the full list of conventions. Every definition's own docstring
states what it means without assuming you have read anything else.
