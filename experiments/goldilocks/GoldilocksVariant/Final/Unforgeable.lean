module
public import GoldilocksVariant.Final.RunFacts
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Routines.WalkEndLemmas

@[expose] public section

/-!
# The adversary's half of unforgeability on the projection of a run of Goldilocks

For a run `π` of `variantProtocolOf M S` under the condition on executions `UnforgeableSends author
carries π` (the adversary's half of unforgeability, read with Goldilocks's authors and inclusions),
the field `other_sent` of `EnvFactsBy` on the trace `toTrace (M.initial S.C) π` with the activity
`activityOf π`, read with the vocabulary `Vocab.goldilocks` (`toTrace_other_sent`).

The condition on the run says that the adversary puts on the wire no object of an honest validator,
nor any object it includes, that is not already on the wire alone or included in a message, signed by
anyone. The field asks for the validator's own signed message. `origin_of_object` closes the gap: in
every configuration of the run, an object of a validator outside the corrupted set that is on the
wire, alone or included in a message, is on the wire under that validator's own signature. It is
proved by induction over the run (`wire_exec`), together with the fact that every Goldfish vote and
every attestation a validator holds in memory is on the wire, alone or included in a message.

No condition on crashes is needed: a crash during a reaction is a step that is neither a tick nor a
delivery, so the condition on the run covers what it sends.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GoldilocksVariant.Final

open RStsVariant2 (Exec Execution Envelope Action Step Config Local NodeStepResult NodeEffect
  NodeAction applyNodeStepResult applyEffects receive)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity)
open GoldilocksCorrectness.Record (GoldilocksModel Facts)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks author)
open GoldilocksCorrectness.Statements.Routines (carries)
open Goldilocks (NamedObject RootOrder Block GoldfishVote Attestation Slot)
open Goldilocks.Sts (Setup)
open Framework.StsMultisetLog (SignedMsg)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## 1. The invariants -/

/-- `OnWire c o`: the object `o` is on the wire in the configuration `c`, as the object of a signed
message or included in it.

The variables:
- `c`: the configuration; `o`: the object. -/
def OnWire {N : Type} (c : Config V (NamedObject V) N) (o : NamedObject V) : Prop :=
  ∃ sm ∈ c.sent.map traceMsg, o = sm.msg ∨ carries sm.msg o

/-- `HeldOn M c n`: every Goldfish vote and every attestation the node state `n` holds is on the
wire in the configuration `c`.

The variables:
- `M`: the model; `c`: the configuration; `n`: the node state. -/
def HeldOn (M : GoldilocksModel V) (c : Config V (NamedObject V) M.N) (n : M.N) : Prop :=
  (∀ (s : Slot) (vote : GoldfishVote V), vote ∈ M.votesHeld n s → OnWire c (.gfVote vote)) ∧
    ∀ a ∈ M.attestationsHeld n, OnWire c (.attest a)

/-- `StOk M c v`: when `v`'s local state `l` is known in the configuration `c`, its memory state
runs as `v` and holds only votes and attestations on the wire in `c`.

The variables:
- `M`: the model; `c`: the configuration; `v`: the validator. -/
def StOk (M : GoldilocksModel V) (c : Config V (NamedObject V) M.N) (v : V) : Prop :=
  ∀ l : Local V (NamedObject V) M.N, c[v] = some l → M.validator l.st = v ∧ HeldOn M c l.st

/-- `OriginOk c`: in the configuration `c`, every object on the wire, alone or included in a
message, whose author is a validator outside the corrupted set, is on the wire under that
validator's own signature.

The variables:
- `c`: the configuration. -/
def OriginOk {N : Type} (c : Config V (NamedObject V) N) : Prop :=
  ∀ sm ∈ c.sent.map traceMsg, ∀ (o' : NamedObject V) (u : V), (o' = sm.msg ∨ carries sm.msg o') →
    author o' = some u → u ∉ c.adv → (⟨u, o'⟩ : SignedMsg V (NamedObject V)) ∈ c.sent.map traceMsg

/-- An object on the wire stays on it: the sent log only grows.

The variables:
- `c`, `c'`: the configurations, the sent log of `c` contained in that of `c'`; `o`: the object. -/
theorem OnWire.mono {N : Type} {c c' : Config V (NamedObject V) N} (hle : c.sent ≤ c'.sent)
    {o : NamedObject V} (h : OnWire c o) : OnWire c' o := by
  obtain ⟨sm, hsm, h⟩ := h
  exact ⟨sm, Multiset.mem_of_le (Multiset.map_le_map hle) hsm, h⟩

/-- What a node state holds stays on the wire: the sent log only grows.

The variables:
- `c`, `c'`: the configurations, the sent log of `c` contained in that of `c'`; `n`: the node
  state. -/
theorem HeldOn.mono {M : GoldilocksModel V} {c c' : Config V (NamedObject V) M.N}
    (hle : c.sent ≤ c'.sent) {n : M.N} (h : HeldOn M c n) : HeldOn M c' n :=
  ⟨fun s vote hv => (h.1 s vote hv).mono hle, fun a ha => (h.2 a ha).mono hle⟩

/-- A node state with the same validator and the same held votes and attestations as one that
runs as `v` and holds only what is on the wire does too.

The variables:
- `c`: the configuration; `v`: the validator; `n`: the node state known to run as `v` and to hold
  only what is on the wire; `n'`: the other node state. -/
theorem stOk_of_same {M : GoldilocksModel V} {c : Config V (NamedObject V) M.N} {v : V}
    {n n' : M.N} (hv : M.validator n' = M.validator n) (hV : M.votesHeld n' = M.votesHeld n)
    (hA : M.attestationsHeld n' = M.attestationsHeld n) (h : M.validator n = v ∧ HeldOn M c n) :
    M.validator n' = v ∧ HeldOn M c n' := by
  refine ⟨hv.trans h.1, fun s vote hvote => h.2.1 s vote ?_, fun a ha => h.2.2 a ?_⟩
  · rw [← hV]; exact hvote
  · rw [← hA]; exact ha

/-! ## 2. The memory invariant, step by step -/

/-- A step of `variantProtocolOf M S` keeps `StOk` at every validator.

Why: a tick adds to the memory only votes and attestations of the objects it sends
(`TickFacts1.tick_prov`, `TickFacts1.tick_prov_attestations`), a delivery only those of the
delivered message (`ReceiveFacts.receive_new`, `ReceiveFacts.receive_new_attestations`), and both
keep the validator (`NodeInvFacts`); a restart wakes the memory or the disk, which hold the same
(`NodeOk`, `WakeFacts.wake_readers`); a validator coming online holds nothing; every other step
leaves the memory states, and the sent log only grows.

The variables:
- `F`: the model's facts; `h`: the step from `c` to `c'` labelled `a`; `hN`: `NodeOk` in `c`;
  `hS`: `StOk` in `c`. -/
theorem stOk_step {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    {a : Action V (NamedObject V) Empty} {c c' : Config V (NamedObject V) M.N}
    (h : Step (variantProtocolOf M S) a c c') (hN : ∀ v : V, NodeOk M S c v)
    (hS : ∀ v : V, StOk M c v) : ∀ v : V, StOk M c' v := by
  have hle := h.sent_le
  refine (h.elim (motive := fun _ d d' => d.sent ≤ d'.sent → (∀ v : V, NodeOk M S d v) →
      (∀ v : V, StOk M d v) → ∀ v : V, StOk M d' v)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial) hle hN hS
  case setClock =>
    intro d w t _ _ hle _ hS v l hl
    rw [RStsVariant2.setClock_getElem] at hl
    obtain ⟨h1, h2⟩ := hS v l hl
    exact ⟨h1, h2.mono hle⟩
  case tick =>
    intro d w l t res _ _ hl ht hres hle hN hS v l' hl'
    by_cases hvw : v = w
    · subst hvw
      rw [RStsVariant2.applyNodeStepResult_getElem_self_of_some _ v res d hl] at hl'
      obtain rfl := Option.some_injective _ hl'
      obtain ⟨hv, hH⟩ := hS v l hl
      obtain ⟨r, hr, hi, hit, -⟩ := hN v l hl
      obtain rfl : t = r := Option.some_injective _ (ht.symm.trans hr)
      rcases variant_step_tick hres with ⟨q, hq, rfl⟩ | rfl
      · have hsent : (applyNodeStepResult (variantProtocolOf M S) v
            ⟨q.1, q.2.map (fun o => .send ⟨o, .all⟩)⟩ d).sent.map traceMsg =
            d.sent.map traceMsg + (q.2 : Multiset (NamedObject V)).map (SignedMsg.mk v) :=
          sent_applyNodeStepResult_broadcasts _ q.2 d
        have ownW : ∀ o ∈ q.2, (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈
            (applyNodeStepResult (variantProtocolOf M S) v
              ⟨q.1, q.2.map (fun o => .send ⟨o, .all⟩)⟩ d).sent.map traceMsg := by
          intro o ho
          rw [hsent]
          exact Multiset.mem_add.2 (Or.inr (Multiset.mem_map.2 ⟨o, by simpa using ho, rfl⟩))
        have hP := F.tk.tick_prov S.C S.P S.X l.st (t : Int) q.1 q.2 hq
        refine ⟨?_, fun s vote hvote => ?_, fun a ha => ?_⟩
        · obtain ⟨-, h2, -⟩ := F.nd.tick_nodeInv S.C S.P S.X l.st (t : Int) hi hit q.1 q.2 hq
          exact h2.trans hv
        · by_cases hn : vote ∈ M.votesHeld l.st s
          · exact (hH.1 s vote hn).mono hle
          · obtain ⟨o, ho, hc⟩ := hP.1 s vote hvote hn
            refine ⟨⟨v, o⟩, ownW o ho, ?_⟩
            rcases hc with rfl | ⟨B, rfl, hB⟩
            · exact Or.inl rfl
            · exact Or.inr (Or.inl ⟨vote, hB, rfl⟩)
        · by_cases hn : a ∈ M.attestationsHeld l.st
          · exact (hH.2 a hn).mono hle
          · rcases F.tk.tick_prov_attestations S.C S.P S.X l.st (t : Int) q.1 q.2 hq a ha hn
              with h1 | ⟨B, hB, hB'⟩
            · exact ⟨⟨v, _⟩, ownW _ h1, Or.inl rfl⟩
            · exact ⟨⟨v, _⟩, ownW _ hB, Or.inr (Or.inr ⟨a, hB', rfl⟩)⟩
      · exact ⟨hv, hH.mono hle⟩
    · rw [RStsVariant2.applyNodeStepResult_getElem_other _ w v res d hvw] at hl'
      obtain ⟨h1, h2⟩ := hS v l' hl'
      exact ⟨h1, h2.mono hle⟩
  case deliver =>
    intro d w e l t res he _ _ _ hl _ hres hle hN hS v l' hl'
    by_cases hvw : v = w
    · subst hvw
      rw [RStsVariant2.applyNodeStepResult_getElem_self_of_some _ v res _
        (by rw [RStsVariant2.receive_getElem]; exact hl)] at hl'
      obtain rfl := Option.some_injective _ hl'
      obtain ⟨hv, hH⟩ := hS v l hl
      obtain ⟨r, -, hi, -, -⟩ := hN v l hl
      have hres' := variant_step_recv hres
      subst hres'
      have hwire : traceMsg e ∈ (applyNodeStepResult (variantProtocolOf M S) v
          ⟨M.receive S.C S.P S.X l.st e.toSignedMsg.msg,
            (M.relayedObjects e.toSignedMsg.msg).toList.map (fun o => .send ⟨o, .all⟩)⟩
          (receive v e.toSignedMsg d)).sent.map traceMsg :=
        Multiset.mem_of_le (Multiset.map_le_map hle) (Multiset.mem_map_of_mem _ he)
      refine ⟨?_, fun s vote hvote => ?_, fun a ha => ?_⟩
      · obtain ⟨-, h2, -⟩ := F.nd.receive_nodeInv S.C S.P S.X l.st e.toSignedMsg.msg hi
        exact h2.trans hv
      · by_cases hn : vote ∈ M.votesHeld l.st s
        · exact (hH.1 s vote hn).mono hle
        · refine ⟨traceMsg e, hwire, ?_⟩
          rcases (F.rcv.receive_new S.C S.P S.X _ e.toSignedMsg.msg).1 s vote hvote hn
            with h | ⟨B, h, hB⟩
          · exact Or.inl h.symm
          · show _ = e.msg ∨ carries e.msg _
            rw [show e.msg = e.toSignedMsg.msg from rfl, h]
            exact Or.inr (Or.inl ⟨vote, hB, rfl⟩)
      · by_cases hn : a ∈ M.attestationsHeld l.st
        · exact (hH.2 a hn).mono hle
        · refine ⟨traceMsg e, hwire, ?_⟩
          rcases F.rcv.receive_new_attestations S.C S.P S.X _ e.toSignedMsg.msg a ha hn
            with h | ⟨B, h, hB⟩
          · exact Or.inl h.symm
          · show _ = e.msg ∨ carries e.msg _
            rw [show e.msg = e.toSignedMsg.msg from rfl, h]
            exact Or.inr (Or.inr ⟨a, hB, rfl⟩)
    · rw [RStsVariant2.applyNodeStepResult_getElem_other _ w v res _ hvw,
        RStsVariant2.receive_getElem] at hl'
      obtain ⟨h1, h2⟩ := hS v l' hl'
      exact ⟨h1, h2.mono hle⟩
  case deliverAdv =>
    intro d w e _ _ _ hle _ hS v l hl
    rw [RStsVariant2.receive_getElem] at hl
    obtain ⟨h1, h2⟩ := hS v l hl
    exact ⟨h1, h2.mono hle⟩
  case corrupt =>
    intro d w _ hle _ hS v l hl
    by_cases hvw : v = w
    · subst hvw
      exact absurd ((RStsVariant2.Config.setNode_self v none d).symm.trans hl) (by simp)
    · have hl' : d[v] = some l := (RStsVariant2.Config.setNode_other w v none d hvw).symm.trans hl
      obtain ⟨h1, h2⟩ := hS v l hl'
      exact ⟨h1, h2.mono hle⟩
  case crash =>
    intro d w _ hle _ hS v l hl
    obtain ⟨h1, h2⟩ := hS v l hl
    exact ⟨h1, h2.mono hle⟩
  case crashDuring =>
    intro d w na k l t res _ _ _ hres hle _ hS v l' hl'
    have hl : (RStsVariant2.applyCrashDuring w res k (na.prepare w d))[v] = d[v] := by
      rw [RStsVariant2.applyCrashDuring_getElem]
      rw [applyEffects_getElem_of_sends
        (fun ef hef => variant_step_sends hres ef (List.mem_of_mem_take hef)) _]
      exact RStsVariant2.NodeAction.prepare_getElem w v d na
    obtain ⟨h1, h2⟩ := hS v l' (hl.symm.trans hl')
    exact ⟨h1, h2.mono hle⟩
  case restart =>
    intro d w keep t _ _ ht hle hN hS v l' hl'
    by_cases hvw : v = w
    · subst hvw
      have hl'' := (RStsVariant2.Config.setNode_self v _ d).symm.trans hl'
      cases hl : d[v] with
      | some l =>
        rw [hl] at hl''
        obtain rfl := Option.some_injective _ hl''
        obtain ⟨-, -, -, -, -, -, h5⟩ := hN v l hl
        have hsrc : M.validator (if keep then l.st else l.disk) = M.validator l.st ∧
            M.votesHeld (if keep then l.st else l.disk) = M.votesHeld l.st ∧
            M.attestationsHeld (if keep then l.st else l.disk) = M.attestationsHeld l.st := by
          cases keep
          · show M.validator l.disk = _ ∧ M.votesHeld l.disk = _ ∧ M.attestationsHeld l.disk = _
            rcases h5 with h5 | ⟨t', h5⟩
            · rw [h5]; exact ⟨rfl, rfl, rfl⟩
            · have hw := F.wk.wake_readers l.disk t'
              rw [h5]
              exact ⟨hw.1.symm, hw.2.2.2.2.2.2.2.1.symm, hw.2.2.2.2.2.2.1.symm⟩
          · exact ⟨rfl, rfl, rfl⟩
        have hw := F.wk.wake_readers (if keep then l.st else l.disk) (t : Int)
        obtain ⟨h1, h2⟩ := hS v l hl
        exact stOk_of_same (hw.1.trans hsrc.1) (hw.2.2.2.2.2.2.2.1.trans hsrc.2.1)
          (hw.2.2.2.2.2.2.1.trans hsrc.2.2) ⟨h1, h2.mono hle⟩
      | none =>
        rw [hl] at hl''
        obtain rfl := Option.some_injective _ hl''
        have hinit : ∀ c₀ : Config V (NamedObject V) M.N,
            M.validator (M.initial S.C v) = v ∧ HeldOn M c₀ (M.initial S.C v) := by
          intro c₀
          refine ⟨(F.init.initial_clock S.C v).2, fun s vote hvote => ?_, fun a ha => ?_⟩
          · rw [show M.votesHeld (M.initial S.C v) s = [] from F.init.initial_votesHeld S.C v s]
              at hvote
            simp at hvote
          · rw [show M.attestationsHeld (M.initial S.C v) = [] from
              F.init.initial_attestationsHeld S.C v] at ha
            simp at ha
        show M.validator ((variantProtocolOf M S).init t v) = v ∧
          HeldOn M _ ((variantProtocolOf M S).init t v)
        show M.validator (M.wake (M.initial S.C v) t) = v ∧
          HeldOn M _ (M.wake (M.initial S.C v) t)
        have hw := F.wk.wake_readers (M.initial S.C v) (t : Int)
        exact stOk_of_same hw.1 hw.2.2.2.2.2.2.2.1 hw.2.2.2.2.2.2.1 (hinit _)
    · have hl : d[v] = some l' := (RStsVariant2.Config.setNode_other w v _ d hvw).symm.trans hl'
      obtain ⟨h1, h2⟩ := hS v l' hl
      exact ⟨h1, h2.mono hle⟩
  case custom =>
    intro d w ev; exact ev.elim
  case adversarial =>
    intro d w m recipients _ hle _ hS v l hl
    obtain ⟨h1, h2⟩ := hS v l hl
    exact ⟨h1, h2.mono hle⟩

/-! ## 3. The origin of an object, step by step -/

/-- `OriginOk` carries over to a configuration whose sent log, read as signed messages, is the old
one with some messages added, each of which forges no validator outside the corrupted set.

The variables:
- `c`, `c'`: the configurations; `N`: the signed messages added. -/
theorem originOk_of_add {N₀ : Type} {c c' : Config V (NamedObject V) N₀}
    {N : Multiset (SignedMsg V (NamedObject V))} (hadv : c.adv ⊆ c'.adv)
    (hsent : c'.sent.map traceMsg = c.sent.map traceMsg + N) (hO : OriginOk c)
    (hN : ∀ sm ∈ N, ∀ (o' : NamedObject V) (u : V), (o' = sm.msg ∨ carries sm.msg o') →
      author o' = some u → u ∉ c.adv →
      (⟨u, o'⟩ : SignedMsg V (NamedObject V)) ∈ c'.sent.map traceMsg) :
    OriginOk c' := by
  intro sm hsm o' u ho' hu hadv'
  have hu' : u ∉ c.adv := fun h => hadv' (hadv h)
  rw [hsent] at hsm
  rcases Multiset.mem_add.1 hsm with h | h
  · rw [hsent]
    exact Multiset.mem_add.2 (Or.inl (hO sm h o' u ho' hu hu'))
  · exact hN sm h o' u ho' hu hu'

/-- **The induction over the run.** In every configuration of a run of `variantProtocolOf M S`
under the adversary's half of unforgeability, every validator's memory runs as that validator and
holds only votes and attestations on the wire (`StOk`), and every object on the wire whose author
is outside the corrupted set is on the wire under its author's own signature (`OriginOk`).

Why: nothing is known or sent at the start. At a tick, the objects sent are the validator's own
(`TickFacts3`), and a block's votes and attestations are ones it holds, so on the wire, whose origin
the induction gives. At a delivery, the relays are the delivered object or objects it includes. At
any other step, the condition on the run gives, for each new envelope, a copy of a signed message
already on the wire, or an envelope signed by a corrupted validator whose honest objects are on the
wire already, alone or included, and so, by the induction, under their authors' signatures.

The variables:
- `F`: the model's facts; `π`: the run; `hU`: the adversary's half of unforgeability. -/
theorem wire_exec {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S)) (hU : RStsVariant2.UnforgeableSends author carries π)
    (i : ℕ) : (∀ v : V, StOk M π[i] v) ∧ OriginOk π[i] := by
  induction i with
  | zero =>
    refine ⟨fun v l hl => absurd ((π.init.1 v).symm.trans hl) (by simp), ?_⟩
    intro sm hsm
    rw [show π[0].sent = 0 from π.init.2.2.2] at hsm
    simp at hsm
  | succ i ih =>
    obtain ⟨hS, hO⟩ := ih
    have hs := π.step_at i
    refine ⟨stOk_step F hs (nodeOk_exec F π i) hS, ?_⟩
    have hadv := hs.adv_subset
    rcases hl : π.lbl i with ⟨p, t⟩ | ⟨p⟩ | ⟨p, e⟩ | ⟨p⟩ | ⟨p⟩ | ⟨p, na, k⟩ | ⟨p, keep⟩ |
        ⟨p, ev⟩ | ⟨p, m, recipients⟩
    rotate_left
    · -- a tick of `p`: its own objects, and the votes and attestations of a block it holds
      rw [hl] at hs
      obtain ⟨-, l, t, res, hlv, ht, hres, heq⟩ := hs
      rw [RStsVariant2.NodeAction.prepare_getElem] at hlv
      have heq' : π[i + 1] = applyNodeStepResult (variantProtocolOf M S) p res π[i] := heq
      obtain ⟨hv, hV, hA⟩ := hS p l hlv
      have hv' : l.st.v = p := hv
      obtain ⟨r, hr, hI, -, -⟩ := nodeOk_exec F π i p l hlv
      rw [RStsVariant2.NodeAction.prepare_clock] at ht
      obtain rfl : t = r := Option.some_injective _ (ht.symm.trans hr)
      rcases variant_step_tick hres with ⟨q, hq, rfl⟩ | rfl
      · have hsent : π[i + 1].sent.map traceMsg =
            π[i].sent.map traceMsg + (q.2 : Multiset (NamedObject V)).map (SignedMsg.mk p) := by
          rw [heq']; exact sent_applyNodeStepResult_broadcasts _ q.2 _
        have hle : π[i].sent.map traceMsg ≤ π[i + 1].sent.map traceMsg := by
          rw [hsent]; exact Multiset.le_add_right _ _
        have own : ∀ o ∈ q.2, (⟨p, o⟩ : SignedMsg V (NamedObject V)) ∈
            π[i + 1].sent.map traceMsg := by
          intro o ho
          rw [hsent]
          exact Multiset.mem_add.2 (Or.inr (Multiset.mem_map.2 ⟨o, by simpa using ho, rfl⟩))
        have fromWire : ∀ (o' : NamedObject V) (u : V), OnWire π[i] o' → author o' = some u →
            u ∉ π[i].adv → (⟨u, o'⟩ : SignedMsg V (NamedObject V)) ∈ π[i + 1].sent.map traceMsg :=
          fun o' u ⟨sm, hsm, hw⟩ hu hu' => Multiset.mem_of_le hle (hO sm hsm o' u hw hu hu')
        refine originOk_of_add hadv hsent hO ?_
        intro sm hsm o' u ho' hu hu'
        obtain ⟨o, ho, rfl⟩ := Multiset.mem_map.1 hsm
        have ho : o ∈ q.2 := by simpa using ho
        cases o with
        | gfVote vote =>
          obtain ⟨-, hvi, -⟩ :=
            F.tk3.tick_vote_head S.C S.P S.X l.st (t : Int) q.1 q.2 vote hq hI ho
          rcases ho' with rfl | hc
          · have hu' : vote.val_index = u := Option.some_injective _ hu
            rw [← hu', hvi, hv']
            exact own _ ho
          · exact hc.elim
        | attest a =>
          obtain ⟨-, -, source, head, -, -, ⟨τ, -, -, ha⟩, -⟩ :=
            F.tk3.tick_attestation S.C S.P S.X l.st (t : Int) q.1 q.2 a hq hI ho
          rcases ho' with rfl | hc
          · have hu' : a.val_index = u := Option.some_injective _ hu
            have hai : a.val_index = l.st.v := by rw [ha]
            rw [← hu', hai, hv']
            exact own _ ho
          · exact hc.elim
        | block B =>
          obtain ⟨-, -, -, -, H, votes, support_votes, hvotes, -, hPH, hB⟩ :=
            F.tk3.tick_proposal S.C S.P S.X l.st (t : Int) q.1 q.2 B hq hI ho
          rcases ho' with rfl | hc
          · have hp : B.proposer? = some l.st.v := by rw [hB]; rfl
            have hu' : l.st.v = u := Option.some_injective _ (hp.symm.trans hu)
            rw [← hu', hv']
            exact own _ ho
          · rcases hc with ⟨vote, hvote, rfl⟩ | ⟨a, ha, rfl⟩
            · have hvote' : vote ∈ M.votesHeld l.st (S.C.slot (t : Int) - 1) := by
                show vote ∈ l.st.votesHeld _
                rw [← hvotes]
                rw [hB] at hvote
                exact hvote
              exact fromWire _ u (hV _ vote hvote') hu hu'
            · obtain ⟨vs, svs, -, hEnd⟩ := hPH
              have hHT : H ∈ l.st.tree :=
                GoldilocksCorrectness.Record.Proofs.Routines.walk_end_mem_T M F S.C S.P S.X _ hI
                  (t : Int) H
                  ((@GoldilocksCorrectness.Proofs.Routines.walkEnd_mem_tree_or_eq V _ M.tieBreak
                    _ _ _ _ _ hEnd).symm)
                  (F.nd.nodeInv_finalized_mem_tree hI) (F.nd.nodeInv_justifiedInTree hI)
              have ha' : a ∈ M.attestationsHeld l.st := by
                rw [hB] at ha
                change a ∈ M.proposal_attestations l.st H at ha
                rw [F.ndAdded.proposal_attestations_eq hI hHT, List.mem_filter] at ha
                exact ha.1
              exact fromWire _ u (hA a ha') hu hu'
      · have hsent : π[i + 1].sent.map traceMsg =
            π[i].sent.map traceMsg + (([] : List (NamedObject V)) : Multiset _).map
              (SignedMsg.mk p) := by
          rw [heq']; exact sent_applyNodeStepResult_broadcasts _ [] _
        refine originOk_of_add hadv hsent hO ?_
        intro sm hsm
        simp at hsm
    · -- a delivery: to a corrupted validator nothing is sent; to an honest one, relays
      rw [hl] at hs
      have he := hs.deliver_sent.1
      obtain ⟨-, hf⟩ := hs
      rcases hf with ⟨-, heq⟩ | ⟨-, l, t, res, hlv, -, hres, heq⟩
      · intro sm hsm
        rw [heq] at hsm ⊢
        exact hO sm hsm
      · have heq' : π[i + 1] =
            applyNodeStepResult (variantProtocolOf M S) p res (receive p e.toSignedMsg π[i]) := heq
        rw [variant_step_recv hres] at heq'
        have hsent : π[i + 1].sent.map traceMsg =
            π[i].sent.map traceMsg +
              (((M.relayedObjects e.toSignedMsg.msg).toList : List (NamedObject V)) :
                Multiset _).map (SignedMsg.mk p) := by
          rw [heq']; exact sent_applyNodeStepResult_broadcasts _ _ _
        have hle : π[i].sent.map traceMsg ≤ π[i + 1].sent.map traceMsg := by
          rw [hsent]; exact Multiset.le_add_right _ _
        have hwire : traceMsg e ∈ π[i].sent.map traceMsg := Multiset.mem_map_of_mem _ he
        refine originOk_of_add hadv hsent hO ?_
        intro sm hsm o' u ho' hu hu'
        obtain ⟨o, ho, rfl⟩ := Multiset.mem_map.1 hsm
        have ho : o ∈ M.relayedObjects e.msg := by simpa using ho
        refine Multiset.mem_of_le hle (hO (traceMsg e) hwire o' u ?_ hu hu')
        show o' = e.msg ∨ carries e.msg o'
        rcases (F.rcv.mem_relayedObjects_iff _ _).1 ho with rfl | ⟨B, hB, hvo⟩
        · exact ho'
        · rw [hB]
          rcases hvo with ⟨vote, hvote, rfl⟩ | ⟨a, ha, rfl⟩
          · rcases ho' with rfl | hc
            · exact Or.inr (Or.inl ⟨vote, hvote, rfl⟩)
            · exact hc.elim
          · rcases ho' with rfl | hc
            · exact Or.inr (Or.inr ⟨a, ha, rfl⟩)
            · exact hc.elim
    all_goals
      -- any other step: the adversary's half of unforgeability
      refine fun sm hsm o' u ho' hu hu' => ?_
      by_cases hold : sm ∈ π[i].sent.map traceMsg
      · exact Multiset.mem_of_le (Multiset.map_le_map hs.sent_le)
          (hO sm hold o' u ho' hu (fun h => hu' (hadv h)))
      · obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 hsm
        have heo : e ∉ π[i].sent := fun h => hold (Multiset.mem_map_of_mem _ h)
        have hnew : e ∈ π[i + 1].sent - π[i].sent := by
          rw [← Multiset.count_pos, Multiset.count_sub, Multiset.count_eq_zero.2 heo,
            Nat.sub_zero]
          exact Multiset.count_pos.2 he
        rcases hU i e (fun p' h => by simp [hl] at h) (fun p' e' h => by simp [hl] at h) hnew
          with ⟨e', he', hcopy⟩ | ⟨-, hadvO⟩
        · exact absurd (Multiset.mem_map.2 ⟨e', he', by
            show (⟨e'.sender, e'.msg⟩ : SignedMsg V (NamedObject V)) = ⟨e.sender, e.msg⟩
            rw [show e'.sender = e'.toSignedMsg.sender from rfl,
              show e'.msg = e'.toSignedMsg.msg from rfl, hcopy]⟩) hold
        · obtain ⟨e', he', hw⟩ := hadvO o' u ho' hu (fun h => hu' (hadv h))
          exact Multiset.mem_of_le (Multiset.map_le_map hs.sent_le)
            (hO (traceMsg e') (Multiset.mem_map_of_mem _ he') o' u
              (by rcases hw with h | h
                  · exact Or.inl h.symm
                  · exact Or.inr h) hu (fun h => hu' (hadv h)))

/-- **An honest validator's object on the wire is on the wire under its own signature.** In every
configuration `i` of a run of `variantProtocolOf M S` under the adversary's half of unforgeability,
an object on the wire, alone or included in a message, whose author `u` is outside the corrupted
set, is on the wire as `u`'s own signed message.

The variables:
- `F`: the model's facts; `π`: the run; `hU`: the adversary's half of unforgeability; `i`: the
  configuration; `sm`: the signed message on the wire; `o'`: its object or one it includes; `u`:
  its author. -/
theorem origin_of_object {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S)) (hU : RStsVariant2.UnforgeableSends author carries π)
    (i : ℕ) (sm : SignedMsg V (NamedObject V)) (hsm : sm ∈ π[i].sent.map traceMsg)
    (o' : NamedObject V) (u : V) (ho' : o' = sm.msg ∨ carries sm.msg o')
    (hu : author o' = some u) (hu' : u ∉ π[i].adv) :
    (⟨u, o'⟩ : SignedMsg V (NamedObject V)) ∈ π[i].sent.map traceMsg :=
  (wire_exec F π hU i).2 sm hsm o' u ho' hu hu'

/-! ## 4. The field `other_sent` -/

/-- **The adversary's half of unforgeability on the trace** (the trace layer's `other_sent`, for
Goldilocks's run, read with `Vocab.goldilocks`). A step of the kind `other` puts on the wire only
copies of messages already on it, or messages signed by a validator in the adversary set whose
object, and every object it includes, attributed to a validator honest up to that step, is already
on the wire under that validator's own signature.

Why: a trace step of the kind `other` of the projection's own sends nothing. A step of the run that
the trace reads as `other` is neither a tick (a tick has a clock, and the trace reads it as a tick)
nor a delivery that sends (a delivery the trace reads as `other` is to a corrupted validator, and
sends nothing), so the condition on the run gives, for a new envelope, a copy of a signed message
already on the wire, or an envelope signed by a corrupted validator whose honest objects are on the
wire, alone or included; `origin_of_object` gives them under their authors' signatures.

The variables:
- `F`: the model's facts; `π`: the run; `hU`: the adversary's half of unforgeability; `j`: the
  trace step; `sm`: the signed message. -/
theorem toTrace_other_sent {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S)) (hU : RStsVariant2.UnforgeableSends author carries π) :
    ∀ (j : ℕ) (sm : SignedMsg V (NamedObject V)),
      (toTrace (M.initial S.C) π).lbl j = Event.other →
      sm ∈ (toTrace (M.initial S.C) π).sent (j + 1) - (toTrace (M.initial S.C) π).sent j →
      sm ∈ (toTrace (M.initial S.C) π).sent j ∨
      (sm.sender ∈ (activityOf π).corrupted j ∧
       ∀ (o' : NamedObject V) (u : V), (o' = sm.msg ∨ Vocab.goldilocks.carries sm.msg o') →
         Vocab.goldilocks.author o' = some u → (activityOf π).HonestThroughStep j u →
         (⟨u, o'⟩ : SignedMsg V (NamedObject V)) ∈ (toTrace (M.initial S.C) π).sent j) := by
  intro j sm hlbl hsm
  by_cases hold : sm ∈ (toTrace (M.initial S.C) π).sent j
  · exact Or.inl hold
  right
  have hsm' := Multiset.mem_of_le (Multiset.sub_le_self _ _) hsm
  rcases newIdx_or_other (M.initial S.C) π j with ⟨i, rfl⟩ | ⟨-, hob⟩
  swap
  · rw [toTrace_sent, toTrace_sent, hob] at hsm
    have h0 := Multiset.count_pos.2 hsm
    rw [Multiset.count_sub, Nat.sub_self] at h0
    exact absurd h0 (lt_irrefl 0)
  rw [toTrace_sent_newIdx] at hold
  rw [toTrace_sent_newIdx_succ] at hsm'
  rw [toTrace_lbl_newIdx] at hlbl
  rw [corrupted_activityOf_newIdx, toTrace_sent_newIdx]
  have hs := π.step_at i
  obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 hsm'
  have heo : e ∉ π[i].sent := fun h => hold (Multiset.mem_map_of_mem _ h)
  have hnew : e ∈ π[i + 1].sent - π[i].sent := by
    rw [← Multiset.count_pos, Multiset.count_sub, Multiset.count_eq_zero.2 heo, Nat.sub_zero]
    exact Multiset.count_pos.2 he
  -- the step is neither a tick nor a delivery
  have hnt : ∀ p : V, π.lbl i ≠ .tick p := by
    intro p hp
    rw [hp] at hs
    obtain ⟨-, t, -, ht⟩ :=
      RStsVariant2.nodeSpec_enabled_known (Pr := variantProtocolOf M S) (v := p) (na := .tick)
        (c := π[i]) hs.1
    have : eventOf π i = Event.tick p t := (eventOf_eq_tick π).2 ⟨hp, ht⟩
    rw [this] at hlbl; cases hlbl
  have hnd : ∀ (p : V) (e' : Envelope V (NamedObject V)), π.lbl i ≠ .deliver p e' := by
    intro p e' hp
    rw [hp] at hs
    by_cases hadv : p ∈ π[i].adv
    · obtain ⟨-, -, heq⟩ := hs.deliver_eq_of_mem_adv hadv
      exact heo (by rw [heq] at he; exact he)
    · have hen : (RStsVariant2.nodeSpec (variantProtocolOf M S) p (.deliver e')).Enabled π[i] :=
        hs.1.resolve_left (fun h' => hadv h'.1)
      obtain ⟨-, hcr, l, -, hlv, -⟩ := hen
      have : eventOf π i = Event.deliver p (traceMsg e') :=
        (eventOf_eq_deliver π).2 ⟨e', hp, rfl, hcr, by rw [hlv]; simp, hadv⟩
      rw [this] at hlbl; cases hlbl
  rcases hU i e hnt hnd hnew with ⟨e', he', hcopy⟩ | ⟨hsadv, hadvO⟩
  · exact absurd (Multiset.mem_map.2 ⟨e', he', by
      show (⟨e'.sender, e'.msg⟩ : SignedMsg V (NamedObject V)) = ⟨e.sender, e.msg⟩
      rw [show e'.sender = e'.toSignedMsg.sender from rfl,
        show e'.msg = e'.toSignedMsg.msg from rfl, hcopy]⟩) hold
  refine ⟨hsadv, fun o' u ho' hu hH => ?_⟩
  have hu' : u ∉ π[i].adv := by
    have := hH (newIdx π i) le_rfl
    rwa [corrupted_activityOf_newIdx] at this
  obtain ⟨e', he', hw⟩ := hadvO o' u ho' hu hu'
  exact origin_of_object F π hU i (traceMsg e') (Multiset.mem_map_of_mem _ he') o' u
    (by rcases hw with h | h
        · exact Or.inl h.symm
        · exact Or.inr h) hu hu'

end GoldilocksVariant.Final
