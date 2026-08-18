---
name: paper-statement-audit
description: Read before translating a paper lemma, definition, or antecedent into a Lean statement of record, and whenever any of these appears — the paper's antecedent contains an action verb ("sets", "casts", "records", "processes", "receives", "merges") while the Lean hypothesis is about a block post-state or a store; a docstring is about to call a hypothesis "the event's consequence" or claim "nothing is lost"; a paper clause looks redundant and is about to be dropped; two readings of a sentence are claimed equivalent in prose rather than proved. Catches event-vs-trace mistranslations and silently dropped clauses.
---

# Auditing a Lean statement against the paper's sentence

Both traps below were paid for on Lemma 8 (`lem:chain-target-uniqueness`), 2026-08-15. The
worked example of the fix is that lemma's section in `Analysis/Lemmas.lean`; the full record
is in `CONTEXT.md`'s 2026-08-15 entries.

## Trap 1: an event is not its trace

A paper antecedent that describes an **event** — "a target vote for `T` sets the target bit" —
happens mid-transition. Rendering it as a post-state carrying the event's trace
(`targetParticipation i = true`, `T_h = some T`) is weaker whenever the same transition can
erase the trace before any post-state exists.

The measured instance: the vote that completes the target quorum sets the bit mid-block;
`state_transition` runs `process_height_events` directly after the block's attestations; the
fired branch runs `advance_height`, which clears `T_h` and both participation arrays (and `P`
on justify). No post-state of that branch carries the trace, while the paper's event happened.
A docstring had claimed the post-state hypothesis was "the vote's consequence — nothing is
lost"; the claim was false and nothing in the tree could show it.

The check, whenever the antecedent has an action verb:

1. Name the trace the event leaves in the state.
2. List the same-transition writers that can erase it. In this codebase the eraser is
   `advance_height`: `T_h ← ⊥`, both participation arrays cleared, `P` cleared on justify.
3. If the trace can be erased, choose explicitly, and say which in the docstring:
   - quantify over mid-replay states (heavy, rarely worth it);
   - find an erasure-proof anchor — Lemma 8 used `s_h = T.slot`, which survives because the
     eraser itself rewrites `s_h` deterministically;
   - or state the post-state version with the uncovered reading declared as a deviation.
4. Never bridge the gap with prose. "This hypothesis is the antecedent's consequence" is a
   claim; unproved, it belongs in the docstring as a stated deviation, not as an equivalence.

## Trap 2: the "redundant" clause

"Once nonempty, it is the chain's unique first block at that height" was dismissed as the
first clause seen from the other side. It was the minimality claim — the invariant every other
proof of the lemma needed. A clause may be dropped only with the equivalence proved, or with
the dismissal recorded as a decision, with its reason, where it can be re-examined.

## The convention that makes both traps visible

For statements of record: quote the paper's sentence verbatim in the docstring, map its nouns
one by one to hypotheses, and state each deviation as a deviation. When a hypothesis does no
deductive work but is the paper's antecedent, keep it and say so — dropping it is how the
statement's vocabulary drifts until statement and sentence can no longer be compared.

The code-side twin of this convention is in `CLAUDE.md` ("the paper's bare symbols are
exempt"): symbols may be renamed to words, words the paper defines may not, and a renamed
declaration's docstring opens with the paper's symbol.
