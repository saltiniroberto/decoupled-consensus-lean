# The style of the library `Spec`

The library is written so that each routine reads like a paper's pseudocode, line by line, while
staying a plain Lean definition. This page states the rules it is written by. Each rule comes with
one place that follows it. When some places do not follow a rule, the rule says so, with the
number of places and up to three of them.

A "routine" on this page is a `def` of the library that computes something: everything except the
type declarations and the notation. "The routine files" are the fifteen files outside
`lean/Spec/Defs/`.

## Names

**A time is `t`, a slot is `s`, a validator is `v`.** Each may carry a numeric subscript or a
prime: `t₀`, `t_0`, `t_1`, `s'`. Example: `positive … (t_0 t_1 : Time) (v : V)`
(`lean/Spec/Protocol/Grades.lean:227`). Not followed in 9 places: the time `Γ` of
`occurrenceBefore` and `beforeCutoff` (`lean/Spec/Objects.lean:589`, `lean/Spec/Objects.lean:599`),
local times with a letter subscript, `t_x`, `t_vote`, `t_H` (`lean/Spec/Objects.lean:602`, and
three more), the slot `cur` of `goldfish_eligible` and `goldfish_fork_choice`
(`lean/Spec/Protocol/ForkChoice/Goldfish.lean:235`), and the validator `i` of
`Electorate.weight_pos` (`lean/Spec/Objects.lean:306`).

**A time comes before a validator in an argument list.** Example: `rawInputs st eta r t v`
(`lean/Spec/Protocol/Grades.lean:181`).

**Every variable bound by `∀` or `∃` states its domain** where it is bound: a bound, `∀ C ∈ T`
(`lean/Spec/Objects.lean:565`), or a type. Not followed in 3 places: `∀ i` in
`Electorate.weight_pos` (`lean/Spec/Objects.lean:306`) and `∃! a` in `pickUnique?` and its
decision procedure (`lean/Spec/Objects.lean:536`, `lean/Spec/Objects.lean:547`).

**The result types are named by acronym, as one family:** `DRE` for a routine that can fail
(`lean/Spec/Defs/Raise.lean:65`) and `DREB` for a duty that can fail and sends objects
(`lean/Spec/Broadcast.lean:47`). The suffix `M` marks the variant of a set operation whose
function can fail: `Finset.filterM` (`lean/Spec/Defs/FinsetM.lean:46`).

**A relation between two blocks is named in words and written with dot notation on its first
block**, the ancestor: `A.ancestorEq B` (`A` is an ancestor of `B`, or `B` itself),
`A.ancestorStrict B` (an ancestor that is not `B`), `A.compatible B`, `A.deeper B`. Example:
`st.F.ancestorEq σ.J` (`lean/Spec/Protocol/Blocks.lean:105`). A lookup that takes a set of blocks
first is called as a function: `Block.deepest? T`, `blockWithRoot T r`
(`lean/Spec/Objects.lean:579`).

## Routines and their shape

**A routine is a `def` with its result type written at the declaration.** A routine of more than
one step is an `Id.run do` block, or a `do` block in its result type `DRE` or `DREB`. Example:
`update_finality` (`lean/Spec/Protocol/Blocks.lean:101`).

**A routine takes the state it changes as an argument and returns it, and works inside on a
mutable copy under the same name**, `let mut st := st`. A state is a store, a node state, a chain
state or a signing history. Example: `on_goldfish_vote` (`lean/Spec/Protocol/GoldfishVotes.lean:72`).

**`let x := e` introduces a name; `let mut x := e` introduces one that a later line overwrites;
an overwrite is written with an arrow, never with `:=`.** Example: `let mut fields … := none`, then
`fields ← (…)` (`lean/Spec/Protocol/Attestations.lean:176`).

**A field of a local record is updated with the arrow, `n.awakeSince ← none`, never with
`{ n with … }`.** Example: `wake` (`lean/Spec/NodeState.lean:62`).

**A state is updated one step per line.** The result of a call that returns a state is not passed,
in the same expression, as the state another call works on. Example: `state_transition`
(`lean/Spec/Protocol/ChainState.lean:194`), whose two steps are two lines.

**When a routine's two results are taken apart and one of them overwrites an existing name while
the other is new, the destructuring assignment gives each field its own arrow**: `:=` for a new
name, `←` for an overwrite. Example: `let {fst ← signingHistory, snd := a} := …`
(`lean/Spec/Protocol/ValidatorClient.lean:238`). Where every part is new, Lean's own pattern is
used: `let (h_c, T_c, ν) := fields.value` (`lean/Spec/Protocol/ValidatorClient.lean:141`). Where
every part overwrites, Lean's own re-assignment is used: `(st, signingHistory) ← attest …`
(`lean/Spec/Node.lean:149`).

**A case split is an `if`.** `match` and `|` alternatives appear only in a definition by cases on
the constructors of an inductive type, which has no other spelling: the readers of a block
(`lean/Spec/Objects.lean:252`), `rememberTimeout` (`lean/Spec/Protocol/ValidatorClient.lean:224`),
and the recursions on a block or a number. Example of a split: `currentSGVote`
(`lean/Spec/Protocol/Grades.lean:458`).

**An optional value is read as `x.value`, under a plain test `if x ≠ none then`, in a routine that
keeps its own result type.** No `if _ : …` is written. The test that a read relies on stands alone
in its `if`. Example: `NodeState.awake_since` (`lean/Spec/NodeState.lean:91`). A dependent `if`
with a name stays where the proof is used by name: `if h : ∃! a, …` in `pickUnique?`
(`lean/Spec/Objects.lean:547`). In a routine that can fail, `let y ← x` reads an optional value
and fails when it is empty; it is used for a read that is meant to fail then, such as a stamp
(`lean/Spec/Protocol/Grades.lean:171`).

**Absence is written `none`.** The symbol `⊥` appears in the routines only as the least stamp,
the genesis block's (`lean/Spec/Objects.lean:176`).

**No existential quantifier ranges over an optional value.** Every `∃` of the library ranges over a
finite set: `∃ W ∈ T, …` (`lean/Spec/Protocol/ForkChoice/Goldfish.lean:194`).

**In a routine, "and" and "or" are written `&&` and `||`.** `∧` and `∨` appear only where a line
states a proposition: under a quantifier, or in a definition whose value is a `Prop`. Example:
`if t = C.proposal_time s && P.proposer s = n.v && awake_for_grade1 then`
(`lean/Spec/Node.lean:142`).

**A value that goes where an optional value is expected is written bare**, and Lean's coercion
wraps it: `n.awakeSince ← t` (`lean/Spec/NodeState.lean:71`). `some` is written for a value whose
own type is already optional underneath, where the bare value would be coerced differently, an
empty value staying empty: a stamp, of type `WithBot Time`, as in `some genesisStamp` (`lean/Spec/Store.lean:235`) and
`some (max t_vote t_H)` (`lean/Spec/Objects.lean:644`). One more `some` stands for a plain value:
`some (T.choose …)` in `pickUnique?` (`lean/Spec/Objects.lean:548`).

**A structure value is built with its constructor's name and named arguments.** Example:
`FinalityPair.mk (height := h_j) (target := J)` (`lean/Spec/Protocol/ValidatorClient.lean:101`); a
block is built as `.node (parent := …) (slot := …) …` (`lean/Spec/Protocol/Blocks.lean:294`). Not
followed in 13 places, which use the anonymous constructor `⟨…⟩`: `pending_round_grades`
(`lean/Spec/Store.lean:85`), `round_grade_read` (`lean/Spec/Protocol/Grades.lean:447`),
`proposal_input` (`lean/Spec/Protocol/Blocks.lean:191`), and ten more. Two more places build a node
state with the brace form, which names the fields (`lean/Spec/Node.lean:88`,
`lean/Spec/Node.lean:151`).

**No numbered projection.** A component is read by its field's name, `p.target`, never `.1` or
`.2`. The only `.1` and `.2` of the library are inside the proof of a decision procedure
(`lean/Spec/Objects.lean:540`).

**A loop is a `for` with a visible bound.** Example: `for _ in [:g.depth + 1]` in
`deepest_compatible_ancestor` (`lean/Spec/Store.lean:127`), and `for` over a list whose order the
docstring says matters. There is no `while` and no `repeat`. Not followed in 2 places, which count
their steps down with an argument: `ghost_walk`, bounded by `|tree|`
(`lean/Spec/Protocol/ForkChoice/Goldfish.lean:163`), and `chain_up`, bounded by the block's depth
(`lean/Spec/Protocol/Grades.lean:71`).

**A read that may find nothing fails, rather than answering a default.** Example: the saved grade
of a phase fails while that grade result is still pending, rather than answering "no block"
(`lean/Spec/Store.lean:309`). Not followed by the chain-state map `st.σ`
(`lean/Spec/Store.lean:205`): it gives every block a chain state, and a block the store never
processed reads the initial one.

**There is one failure value, and it carries nothing** (`lean/Spec/Defs/Raise.lean:49`).

**A routine takes the weakest result type that fits what it does:** a plain value when it neither
fails nor sends, `DRE α` when it may fail, `DREB V α` when it also sends. Example:
`on_goldfish_vote` is plain (`lean/Spec/Protocol/GoldfishVotes.lean:71`),
`update_confirmation` is `DRE` (`lean/Spec/Protocol/GoldfishVotes.lean:174`), and `goldfish_vote`
is `DREB` (`lean/Spec/Protocol/GoldfishVotes.lean:114`).

**A duty sends an object with `broadcast` and returns only what it changes.** No caller collects
the objects a duty it calls sent: they are already in the list `DREB` keeps. Example:
`broadcast (NamedObject.gfVote vote)` (`lean/Spec/Protocol/GoldfishVotes.lean:122`). The one place
a duty is run is the wiring of `lean/Sts.lean`, which runs the tick from an empty list with
`.run []`.

## Sets

**The size of a finite set is `|s|`.** Example: `2 ≤ |votes_by votes v|`
(`lean/Spec/Protocol/ForkChoice/Goldfish.lean:52`).

**An operation on a set is written in the notation a paper uses**: `S ∪ {x}` to add an element
(`lean/Spec/Protocol/ChainState.lean:107`), `{x ∈ S | p x}` for the members that pass a test
(`lean/Spec/Protocol/ForkChoice/Goldfish.lean:47`), `∅`, `∈`, `∉`. There is no `insert`, no
`.card` and no `Finset.filter` in a routine.

**A projection of a set is the image comprehension**, `{f x | x ∈ s}`, or `{f x | x ∈ s, p x}`
with a test. Example: `{Protocol.sgVote a | a ∈ st.sg_pool r}` (`lean/Spec/Store.lean:264`). A
routine writes no `Finset.image`. A union over a family of sets is a definition that the routines
read by name, such as `Store.included_votes` (`lean/Spec/Store.lean:268`); `biUnion` appears only in
the bodies of those three definitions.

**A filter whose test may fail is the raising set-builder**, `let y ← {x ∈ᴹ s | p}`. Example:
`rawInputs` (`lean/Spec/Protocol/Grades.lean:183`); 12 places follow it. Not followed in 5 places,
which call `Finset.filterM` directly: `beforeCutoff` (`lean/Spec/Objects.lean:601`),
`raw_supporters` (`lean/Spec/Protocol/ForkChoice/Goldfish.lean:98`), `is_best_in`
(`lean/Spec/Protocol/ForkChoice/Goldfish.lean:129`), and two more in the same file.

## Types and records

**A field or a parameter whose type is a function names the function's argument**, so that a
docstring can refer to it: `σ : (B : Block V) → ChainState V` (`lean/Spec/Store.lean:205`),
`proposer : (s : Slot) → V` (`lean/Spec/Config.lean:89`). Not followed in 20 places: the fields
`Electorate.weight` and `Committees.members` (`lean/Spec/Objects.lean:304`,
`lean/Spec/Objects.lean:311`), the type `TimestampMap` and the three parameters of that type, the
parameters `score`, `eligible` and `σ` of the walk and the viability test
(`lean/Spec/Protocol/ForkChoice/Goldfish.lean:118` and eleven more), the parameter `test` of
`deepest_clear`, and the field `GradeRead.clear`.

**An instant with a fixed formula is a definition over the parameters, not a field of them.**
Example: `C.vote_time s` (`lean/Spec/Config.lean:131`).

**An indexed field of the store or of the signing history is read with brackets**: `st.σ[B]`,
`st.gf_votes[s]`, `signingHistory.target[h_j]`. Example: `lean/Spec/Protocol/Blocks.lean:103`. The
brackets are the instance `funGetElem` (`lean/Spec/Store.lean:180`), which reads `f[a]` as `f a`
and is active in the namespace `Spec`. Not followed in 3 places, which read a stamp map by
application inside a read that fails when the stamp is absent: `st.timestamp_block H`
(`lean/Spec/Protocol/Grades.lean:171`), `st.timestamp_sg_vote u`
(`lean/Spec/Protocol/Grades.lean:184`), `st.timestamp_block B`
(`lean/Spec/Protocol/ForkChoice/Views.lean:69`).

## Notation

Each piece of notation, with the file that defines it. The notation of `lean/Spec/Defs/` is in the
namespace `DC` and is active in a file that writes `open scoped DC`; the rest is in the namespace
`Spec` and is active inside it.

| written | meaning | defined in | used at |
| --- | --- | --- | --- |
| `none` | an absent optional value | Lean | `lean/Spec/NodeState.lean:62` |
| `⊥` | the empty optional value, in `Option.value`'s argument `x ≠ ⊥`; in the routines, Mathlib's least element of `WithBot`, the least stamp | `lean/Spec/Defs/Model.lean:61` | `lean/Spec/Objects.lean:176` |
| `if x ≠ none then … x.value …` | the read of an optional value under the test that it is not empty; the `if` hands the fact of its condition to its branches when the condition mentions `none`, `⊥` or `pending` | `lean/Spec/Defs/Raise.lean:75`, `lean/Spec/Objects.lean:103` | `lean/Spec/NodeState.lean:91` |
| `result.block` | the block of a grade result, under the test `if result ≠ .pending then` | `lean/Spec/Objects.lean:341` | `lean/Spec/Store.lean:141` |
| `let y ← x` | in a routine that can fail: the value of the optional `x`, or of the grade result `x`, failing when it is empty or pending | `lean/Spec/Defs/Raise.lean:112`, `lean/Spec/Objects.lean:350` | `lean/Spec/Store.lean:309` |
| `x ← e`, `σ.f ← e` | overwrite a name or a field of a local record with a plain value | `lean/Spec/Defs/Notation.lean:77` | `lean/Spec/Protocol/ChainState.lean:107` |
| `σ.f.g ← e` | overwrite one field reached by a path of fields | `lean/Spec/Objects.lean:120` | `lean/Spec/Protocol/Grades.lean:324` |
| `σ.f, σ.g ← e` | overwrite two fields with the same value | `lean/Spec/Defs/Notation.lean:93` | `lean/Spec/Protocol/ChainState.lean:143` |
| `σ.f[i] ← e` | overwrite one entry of a field that holds a function | `lean/Spec/Defs/Notation.lean:104` | `lean/Spec/Protocol/GoldfishVotes.lean:77` |
| `x ⇐ e` | overwrite a name with the result of a computation that may fail or send | `lean/Spec/Defs/Notation.lean:122` | `lean/Spec/Node.lean:143` |
| `let {f := x, g ← y} := e`, `… ⇐ e` | take a structure apart: `:=` introduces, `←` overwrites | `lean/Spec/Defs/Notation.lean:169`, `lean/Spec/Defs/Notation.lean:174` | `lean/Spec/Protocol/ValidatorClient.lean:238` |
| `f[a]` | read a field that holds a function at `a` | `lean/Spec/Store.lean:180` | `lean/Spec/Protocol/Blocks.lean:103` |
| `\|s\|` | the size of a finite set | `lean/Spec/Defs/Notation.lean:256` | `lean/Spec/Protocol/ForkChoice/Goldfish.lean:52` |
| `{x ∈ s \| p}` | the members of `s` that pass `p` | Mathlib | `lean/Spec/Protocol/ForkChoice/Goldfish.lean:47` |
| `let y ← {x ∈ᴹ s \| p}` | the same, when `p` may fail | `lean/Spec/Defs/Notation.lean:223` | `lean/Spec/Protocol/Grades.lean:183` |
| `{f x \| x ∈ s}`, `{f x \| x ∈ s, p x}` | the image of `s`, of the members that pass `p` | `lean/Spec/Defs/Notation.lean:236`, `lean/Spec/Defs/Notation.lean:240` | `lean/Spec/Store.lean:264` |
| `p <[lex] q` | the pair `p` is smaller than `q` in lexicographic order | `lean/Spec/Objects.lean:132` | `lean/Spec/Protocol/Blocks.lean:105` |

The two assignment arrows say whether the right-hand side computes: `←` takes a plain value, `⇐` a
computation that may fail or send.

## Docstrings and comments

**Every declaration carries a docstring that says what it means.** Every declaration of the routine
files has one; a structure whose fields have none lists them in its own docstring, as `Store` does
(`lean/Spec/Store.lean:183`).

**A docstring cites nothing and tells no history.** It names no outside document, no other
project's file, no date and no person; the one kind of date allowed is "measured" with a date, on
a fact about how Lean behaves. Example: `Store.tau` (`lean/Spec/Store.lean:284`).

## The extraction

`extract/extract.py` renders the library into a document shaped like a paper (`extract/README.md`).
It reads every Lean file under `lean/Spec/`, `lean/Spec/Defs/` included. It takes into the document only
what a file marks:

- a section of a module header, or of a `/-! … -/` comment, headed `## Extract` is prose of the
  document;
- a comment `/-! ## Figure … -/` standing immediately before a `def` makes that routine a figure,
  rendered as pseudocode; a comment `/-! ## New figure — Caption -/` starts a new figure;
- a docstring that opens with a form in backticks, such as `` `C.slotOf t`: ``
  (`lean/Spec/Config.lean:122`), gives the declaration the symbol the document writes for it.

A file with nothing marked contributes no section. Today the one marked section is the
`## Extract` of `lean/Spec/Defs/Model.lean` (`lean/Spec/Defs/Model.lean:18`), and no routine
carries a `## Figure` comment.

## What the library does not contain

**No theorem.** No file of the library holds a `theorem`, a `lemma` or an `example`. The proofs it
holds are those a definition cannot exist without:

- the instance that any two failures are equal (`lean/Spec/Defs/Raise.lean:55`), and the
  instances that `Finset.unionM` at `DRE` is commutative and associative
  (`lean/Spec/Defs/Raise.lean:82`, `lean/Spec/Defs/Raise.lean:93`), which `Finset.filterM` needs;
- the decision procedures: `decidableExistsUniqueMem` (`lean/Spec/Objects.lean:535`),
  `supportsDecidable` and `opposesDecidable` (`lean/Spec/Protocol/Grades.lean:142`,
  `lean/Spec/Protocol/Grades.lean:148`);
- the injectivity inside the order on roots (`lean/Spec/Objects.lean:156`);
- the arguments that `Option.value` and `GradeResult.block` find by a tactic
  (`lean/Spec/Defs/Raise.lean:75`, `lean/Spec/Objects.lean:341`).

**No `axiom`, no `native_decide`, no `sorry`.**

**No model of executions.** The library holds no delivery bound and no instant after which
delivery is bounded (`lean/Spec/Config.lean:21`), no adversary, and no relay: the receiving
routines send nothing. Sending a delivered object again is the wiring's `relayedObjects`
(`lean/Sts.lean:135`).

**The placement under the sts framework is outside the library.** `lean/Sts.lean` is its own
library, and no file of `Spec` imports it. A tick that fails is not a step: the node state is kept
and nothing is sent (`lean/Sts.lean:174`). The objects are one type, `NamedObject V`
(`lean/Spec/Objects.lean:316`).
