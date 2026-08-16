# Paper ↔ Lean mapping

One row per part of the paper that this project will render, and one row per Lean declaration
that renders it. Keyed on the paper's `\label`, because that is what survives renumbering; the
printed number is given too, because it is what a human reading the PDF sees.

**What is rendered so far: Figures 1 and 2, the numbered definitions those two read, Definitions
11 and 21 except the store-facing `FC`, and Lemmas 1 to 11 with Theorem 5.** Every sentence of
those eleven lemmas and of Theorem 5 is stated, and every statement is proved — Lemma 8's five
and Lemma 9's three included. No row in the results table below is 🟡 or 🔨.
Every other Lean cell is `—`. The row set is the paper's, not a plan: a row appearing here says
the paper has that result, not that this project intends to state it. Fill a row in when its
statement lands.

**Source**: the `latex-specs` submodule, pinned — `height_filter_healing.tex` (Sections 1–5)
and its `\input`, `recovery_core.tex` (Sections 6–13). `git submodule status` is the authority
on which revision this tracks.

**Numbers**: derived from `height_filter_healing.aux`, a LaTeX **build artefact that the
submodule does not carry**. `make cites` checks every number in this file and in every
docstring against it, and skips with a notice when the paper has not been built. To arm it:

```
cd latex-specs && latexmk -pdf height_filter_healing.tex && cd -
```

**What is not carried over from an earlier attempt.** The row set below was derived from that
attempt's own table, which records which results it proved, which it stated partially, and
which it skipped deliberately with a reason. Only the paper-level columns were taken. None of
its judgements is repeated here: an absent row here means "not yet examined", and an earlier
conclusion may in any case be wrong. Its table is not in this repository; `REFERENCES_LOCAL.md`
says where to read it.

## The five algorithm figures

A file rendering one of these is named `Fig<n><Subject>.lean`, `<n>` being the printed number
in this column. A file that renders no figure has no such prefix.

| Paper | № | Lean file | Lean declarations |
| --- | --- | --- | --- |
| `alg:state-replay` | Fig. 1 | `lean/Spec/Fig1SlotReplay.lean` | `processSlot`, `processSlots`, `stateTransition` |
| `alg:attestation-processing` | Fig. 2 | `lean/Spec/Fig2AttestationProcessing.lean` | `processAttestation`, `processAttestations`, `processBlock`, `advanceHeight`, `processHeightEvents` |
| `alg:store` | Fig. 3 | — | — |
| `alg:fork-choice-state` | Fig. 4 | — | — |
| `alg:recovery-action` | Fig. 5 | — | — |

## Definitions

The paper's numbered definitions and assumptions, grouped as the paper groups them. The Lean
column names the declarations that render each one.

### Model and state

| Paper | № | Lean |
| --- | --- | --- |
| `def:validator-weights` | Def. 3 | `Electorate`, `weight`, `W`, `q`, `m`, `Quorum`, `StrictMajority` |
| `def:height` | Def. 4 | `Params` |
| `def:block-chain` | Def. 5 | `Blk`, `Blk.parent`, `Blk.slot`, `Blk.proposer`, `Blk.attestations`, `Blk.claimedRoot`, `ancestors`, `Preceq`, `Prec`, `Compatible`, `Conflicts` |
| `def:fg-message` | Def. 8 | `Attestation`, `HeightPair`, `FinalityPair`, `Attestation.height`, `Attestation.target`, `Attestation.finalizeHeight`, `Attestation.finalizeTarget` |
| `def:valid-attestation-inclusion` | Def. 9 | `ValidInclusion` — membership in `V` only; signatures are the `validator` field |
| `def:chain-state` | Def. 13 | `ChainState`, `ChainState.gen` |
| `def:nonjustifiable` | Def. 14 | `nonjustifiable` |
| `def:participation-state` | Def. 15 | `ChainState.Qtarget`, `ChainState.Qprog` |
| `def:total-raw-replay` (slot eligibility half) | Def. 24 | — |
| `def:valid-block` (assigned proposer half) | Def. 19 | — |

### Transition

| Paper | № | Lean |
| --- | --- | --- |
| `def:vote-contribution` | Def. 10 | `processAttestation` — the two height tests, no separate declaration |
| `def:block-attestation-processing` | Def. 16 | `processAttestation`, `processAttestations` |
| `def:height-outcome` | Def. 18 | `processHeightEvents`, `advanceHeight` |
| `def:finality-action-state` | Def. 20 | `actionState` — over a block post-state rather than `σ[X]` |

### Store and fork choice

| Paper | № | Lean |
| --- | --- | --- |
| `def:certificates` | Def. 21 | `JustificationCertificate`, `ProgressCertificate`, `IncludedOn` — `BlockPostState` in place of `σ[·]`, so a certificate is weaker than the paper's; `FC` was rendered at `f284635` and removed when the finalization hypotheses became recorded pairs |
| `def:stored-data` | Def. 22 | — |
| `def:store-join` | Def. 23 | — |
| `def:state-height` | Def. 6 | — |
| `def:fork-state` | Def. 25 | — |
| `def:finality-root` | Def. 26 | — |

### Recovery

| Paper | № | Lean |
| --- | --- | --- |
| `def:signing-history` | Def. 12 | — |
| `def:recovery-timing` | Def. 28 | — |
| `ass:recovery-goldfish` | Ass. 12 | — |
| `ass:goldfish-committees` | Ass. 3 | — |
| `def:recovery-proposal` | Def. 43 | — |
| `def:rederivation` | Def. 29 | — |
| `def:activation-filter` | Def. 30 | — |
| `def:recovery-context` | Def. 31 | — |
| `def:walk-standing` | Def. 32 | — |
| `def:counting-rule` | Def. 33 | — |
| `def:sg-head` | Def. 34 | — |
| `def:grade-support` | Def. 35 | — |
| `def:grades` | Def. 36 | — |
| `def:active-grade` | Def. 37 | — |
| `def:tsq-views` | Def. 38 | — |
| `def:tsq-confirmation` | Def. 39 | — |
| `def:grade-root-choice` | Def. 40 | — |
| `def:stable-root` | Def. 41 | — |
| `def:action-root` | Def. 42 | — |
| `def:recovery-goldfish-vote` | Def. 45 | — |
| `def:official-confirmation` | Def. 46 | — |
| `def:ordinary-current-target` | Def. 47 | — |
| `def:height-vote-rule` | Def. 48 | — |
| `def:finality-vote-rule` | Def. 49 | — |
| `def:fg-rule` | Def. 50 | — |
| `ass:frontier-opportunities` (4a only) | Ass. 15 | — |

### Stated but not read by a figure

Definitions and assumptions the results need, which no algorithm figure reads.

| Paper | № | Lean |
| --- | --- | --- |
| `ass:fixed-electorate` | Ass. 1 | — |
| `ass:sg-fault-bound` | Ass. 2 | — |
| `def:slashing` | Def. 11 | `E1`, `E2` — E1 landed with Lemma 10 |

## Numbered results

Every numbered lemma, theorem, corollary and proposition of both papers.

**cited by** counts how often the paper's own proofs cite the result — a `\ref` inside a
`proof` environment, counted mechanically across both `.tex` files. It is a property of the
paper, so it is filled in from the start, and it is the best available guide to which results
carry the argument.

**Status**: ✅ *proved* — the statement of record covers the paper's sentence; 🟡 *partial* — a
deliberately narrower sentence is proved, and the note says which; 🔨 *stated* — written down
and **not proved**, with the note saying what is outstanding; ⛔ *absent* — no Lean
statement. A sortable, filterable view of this table is [mapping.html](mapping.html),
regenerated by `make mapping`.

| Paper | № | Lean | cited by | Status |
| --- | --- | --- | --- | --- |
| `lem:integer-thresholds` | Lem. 1 | `lemIntegerThresholds` — over every `b` under Assumption 1's bound | 3 proofs | ✅ proved |
| `lem:quorum-intersection` | Lem. 2 | `lemQuorumIntersection`, and `lemQuorumIntersectionNonByzantine` for its "consequently" | 3 | ✅ proved |
| `lem:target-bit-compression` | Lem. 9 | `lemTargetBitCompression` — the first sentence, as the two tallies' provenance (a re-export of `Witnessed` over `postState`); `lemTargetBitCompressionEvidence` and `lemTargetBitCompressionEvidenceE1` — the second sentence, one statement per slashing condition, the E1 half stated over `P` because a commit has no bit in either of the sentence's two arrays | 2 prose | ✅ proved |
| `lem:empty-slot-noop` | Lem. 3 | `lemEmptySlotNoop` as a record equation, `lemEmptySlotNoopFields` for the paper's list | 4 | ✅ proved |
| `lem:finalized-before-justified` | Lem. 4 | `lemFinalizedBeforeJustified` — both subjects the sentence names, the block post-state and the finality action state | 3 | ✅ proved |
| `lem:target-uniqueness` | Lem. 5 | `lemTargetUniqueness` — the paper's "unless" as the conclusion, with the evidence included on both chains | 6 | ✅ proved |
| `lem:height-progression` | Lem. 6 | `lemHeightProgression` — both halves, over a block post-state's transition | 3 | ✅ proved |
| `lem:height-target-freshness` | Lem. 7 | `lemHeightTargetFreshness`; the paper's definite "the post-state at `T`" as a value of `postState`, without Figure 3 | 1 | ✅ proved |
| `lem:chain-target-uniqueness` | Lem. 8 | `lemChainTargetUniqueness`, `lemChainTargetFirstBlock`, `lemChainTargetTransfer`, `lemChainTargetBothBits`, `lemChainTargetConflict` — one per clause, each docstring carrying the paper's sentence verbatim; the third sentence's scope clause is not stated, and the second sentence's mid-block reading is noted as uncovered in `lemChainTargetTransfer`'s docstring | 6 | ✅ proved |
| `lem:past-finalized` | Lem. 10 | `lemPastFinalized` — both subjects, finalization as the recorded pair `(F, h_F)` rather than `FC`, the accountable disjunct with E1 evidence as included pairs, `1 ≤ h ∧` for the paper's "for h ≥ 1" | 17 | ✅ proved |
| `lem:finalized-chain` | Lem. 11 | `lemFinalizedChain` — over two recorded pairs; "fault bound violated" as the accountable disjunct, `E1 ∨ E2` per Definition 11's "either condition" | 8 | ✅ proved |
| `thm:accountable-safety` | Thm. 5 | `thmAccountableSafety`, in `Analysis/Theorems.lean` — the "unless" as the conclusion, inclusions on the two chains in either order. **Stronger than the paper's statement**: each "finalize" is only the recorded pair `(F, h_F) = (C, h)` on the block's replayed post-state — a weaker hypothesis than Definition 21's certificate, and `postState` replays without Figure 3's validity checks. Kernel-clean 2026-08-16 | prose only | ✅ proved |
| `lem:store-monotonicity` | Lem. 12 | not yet stated | 10 | ⛔ absent |
| `thm:store-merge` | Thm. 7 | not yet stated | — | ⛔ absent |
| `cor:merged-action-inputs` | Cor. 1 | not yet stated | — | ⛔ absent |
| `lem:local-finality-irreversible` | Lem. 13 | not yet stated | 3 | ⛔ absent |
| `lem:finalized-root-viable` | Lem. 14 | not yet stated | 2 | ⛔ absent |
| `lem:filtered-hmax-monotone` | Lem. 15 | not yet stated | 2 | ⛔ absent |
| `lem:store-fork-choice-total` | Lem. 16 | not yet stated | 6 | ⛔ absent |
| `lem:finalized-lockin` | Lem. 17 | not yet stated | 4 | ⛔ absent |
| `lem:nonjustifiable-fg` | Lem. 18 | not yet stated | 5 | ⛔ absent |
| `lem:aged-containment` | Lem. 19 | not yet stated | 2 | ⛔ absent |
| `lem:aged-walk-total` | Lem. 20 | not yet stated | 2 | ⛔ absent |
| `lem:direct-roots-chain` | Lem. 21 | not yet stated | 3 | ⛔ absent |
| `cor:g3-chain` | Cor. 2 | not yet stated | 2 | ⛔ absent |
| `lem:g3-g2` | Lem. 22 | not yet stated | 2 | ⛔ absent |
| `lem:g2-g1` | Lem. 23 | not yet stated | 2 | ⛔ absent |
| `lem:g1-g0` | Lem. 24 | not yet stated | 2 | ⛔ absent |
| `lem:g1-acceptance` | Lem. 25 | not yet stated | 3 | ⛔ absent |
| `lem:fresh-support-clears` | Lem. 26 | not yet stated | 3 | ⛔ absent |
| `lem:tsq-uniqueness` | Lem. 27 | not yet stated | 4 | ⛔ absent |
| `lem:tsq-adoption` | Lem. 28 | not yet stated | 4 | ⛔ absent |
| `lem:fork-margin` | Lem. 29 | not yet stated | 3 | ⛔ absent |
| `cor:tsq-walk` | Cor. 3 | not yet stated | 3 | ⛔ absent |
| `lem:tsq-liveness` | Lem. 30 | not yet stated | 2 | ⛔ absent |
| `cor:tsq-honest-witness` | Cor. 4 | not yet stated | 2 | ⛔ absent |
| `lem:tsq-common-knowledge` | Lem. 31 | not yet stated | 2 | ⛔ absent |
| `lem:tsq-monotonicity` | Lem. 32 | not yet stated | 2 | ⛔ absent |
| `lem:recovery-rooted-persistence` | Lem. 33 | not yet stated | 3 | ⛔ absent |
| `lem:recovery-rooted-confirmation` | Lem. 34 | not yet stated | 3 | ⛔ absent |
| `lem:no-forward-move` | Lem. 35 | not yet stated | 5 | ⛔ absent |
| `lem:common-recognition` | Lem. 36 | not yet stated | 3 | ⛔ absent |
| `lem:honest-proposer-stable-root` | Lem. 37 | not yet stated | 3 | ⛔ absent |
| `lem:forward-root` | Lem. 38 | not yet stated | 2 | ⛔ absent |
| `lem:honest-proposer-votes` | Lem. 39 | not yet stated | 2 | ⛔ absent |
| `lem:root-no-regression` | Lem. 40 | not yet stated | 3 | ⛔ absent |
| `lem:root-backing` | Lem. 41 | not yet stated | 3 | ⛔ absent |
| `lem:same-slot-target` | Lem. 42 | not yet stated | 2 | ⛔ absent |
| `lem:official-confirmation-root-safety` | Lem. 43 | not yet stated | 4 | ⛔ absent |
| `lem:signer-safety` | Lem. 44 | not yet stated | 3 | ⛔ absent |
| `lem:height-vote-confirmation` | Lem. 45 | not yet stated | 3 | ⛔ absent |
| `lem:height-increase-confirmation` | Lem. 46 | not yet stated | 3 | ⛔ absent |
| `lem:pre-confirmation-cap` | Lem. 47 | not yet stated | 2 | ⛔ absent |
| `lem:debt-dichotomy` | Lem. 48 | not yet stated | 2 | ⛔ absent |
| `lem:no-height-h-justification` | Lem. 49 | not yet stated | 3 | ⛔ absent |
| `lem:selectable-roots` | Lem. 50 | not yet stated | 3 | ⛔ absent |
| `lem:honest-proposer-coverage` | Lem. 51 | not yet stated | 7 | ⛔ absent |
| `lem:first-confirmation-simplex-roots` | Lem. 52 | not yet stated | 3 | ⛔ absent |
| `lem:honest-proposal-sg-batch` | Lem. 53 | not yet stated | 3 | ⛔ absent |
| `lem:next-batch-clears` | Lem. 54 | not yet stated | 2 | ⛔ absent |
| `lem:rederivation-ancestry` | Lem. 55 | not yet stated | 2 | ⛔ absent |
| `lem:pre-confirmation-finality-compatible` | Lem. 56 | not yet stated | 2 | ⛔ absent |
| `lem:gate-closure` | Lem. 57 | not yet stated | 3 | ⛔ absent |
| `lem:closing-action-existence` | Lem. 58 | not yet stated | — | ⛔ absent |
| `lem:honest-proposal-confirms` | Lem. 59 | not yet stated | — | ⛔ absent |
| `lem:no-hidden-h-advance` | Lem. 60 | not yet stated | 2 | ⛔ absent |
| `lem:first-confirmation-heads` | Lem. 61 | not yet stated | 2 | ⛔ absent |
| `lem:first-confirmation-clears` | Lem. 62 | not yet stated | 2 | ⛔ absent |
| `lem:predrain-height-retention` | Lem. 63 | not yet stated | — | ⛔ absent |
| `lem:predrain-simplex-roots` | Lem. 64 | not yet stated | — | ⛔ absent |
| `lem:drain-stable-roots` | Lem. 65 | not yet stated | — | ⛔ absent |
| `lem:confirmation-round-slots` | Lem. 66 | not yet stated | — | ⛔ absent |
| `lem:drain-confirms` | Lem. 67 | not yet stated | — | ⛔ absent |
| `lem:first-confirmation-persists` | Lem. 68 | not yet stated | — | ⛔ absent |
| `lem:post-healing-proposer` | Lem. 69 | not yet stated | — | ⛔ absent |
| `cor:post-drain-confirms` | Cor. 5 | not yet stated | — | ⛔ absent |
| `lem:saved-target-transfers` | Lem. 70 | not yet stated | 2 | ⛔ absent |
| `lem:lock-alignment` | Lem. 71 | not yet stated | — | ⛔ absent |
| `lem:common-progress` | Lem. 72 | not yet stated | — | ⛔ absent |
| `lem:usable-common-action` | Lem. 73 | not yet stated | — | ⛔ absent |
| `lem:common-action-advances` | Lem. 74 | not yet stated | — | ⛔ absent |
| `lem:height-catchup` | Lem. 75 | not yet stated | — | ⛔ absent |
| `lem:leave-nonjustifiable-height` | Lem. 76 | not yet stated | — | ⛔ absent |
| `lem:honest-proposer-forces-first-confirmation` | Lem. 77 | not yet stated | — | ⛔ absent |
| `lem:recovery-height-justifies` | Lem. 78 | not yet stated | — | ⛔ absent |
| `lem:fresh-ordinary-justify` | Lem. 79 | not yet stated | — | ⛔ absent |
| `lem:honest-proposer-finalizes` | Lem. 80 | not yet stated | — | ⛔ absent |
| `lem:post-healing-finality` | Lem. 81 | not yet stated | — | ⛔ absent |
| `prop:opportunity-budget` | Prop. 1 | not yet stated | — | ⛔ absent |
| `thm:eventual-healing` | Thm. 17 | not yet stated | — | ⛔ absent |
| `cor:end-to-end` | Cor. 6 | not yet stated | — | ⛔ absent |
| `cor:recurring-healing` | Cor. 7 | not yet stated | — | ⛔ absent |
