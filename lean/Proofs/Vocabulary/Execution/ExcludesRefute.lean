module
public import Proofs.Vocabulary.Execution.Runtime
public import Proofs.Vocabulary.Execution.BodyRetention
public import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.ModelProperties.Block_compatible
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Proofs.Vocabulary.ModelProperties.NamedReceipt_excludes

@[expose] public section

/-!
# Refuting exclusion from a later read

Compatibility, or a finalized prefix, at a later read refutes exclusion at a deadline.
-/
namespace DecoupledConsensusModel.Proofs

open DecoupledConsensusModel
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem compatible_of_preceq_of_compatible {A C B : Block V}
    (hAC : Block.Preceq A C) (hCB : Block.compatible C B = true) :
    Block.compatible A B = true := by
  simp only [Block.compatible, Bool.or_eq_true] at hCB ⊢
  rcases hCB with hCB | hBC
  · exact Or.inl (Block.preceq_trans hAC hCB)
  · simpa only [Block.compatible, Bool.or_eq_true] using
      (Block.compatible_of_preceq_common hAC hBC)

/-- Compatibility at a later indexed read refutes exclusion at the deadline. -/
theorem not_excludes_of_compatible_later
    (S : Setup V) (rho : NamedRun V) {w : V} {B : NamedBlock V}
    {d : Time} {j : Nat}
    (hj : ∃ n, NamedRun.stateBeforeTime S rho d =
      NamedRun.stateBefore S rho n ∧ n ≤ j)
    (hcompat : Block.compatible
      (NamedRun.stateBefore S rho j w).st.core.F B.erase = true) :
    NamedReceipt.excludes (NamedRun.stateBeforeTime S rho d w).st (.block B) = false := by
  rcases hj with ⟨n, hn, hjn⟩
  have hmono := NamedRuntime.stateBefore_F_mono S rho w hjn
  have hFB : Block.compatible
      (NamedRun.stateBeforeTime S rho d w).st.core.F B.erase = true := by
    rw [hn]
    exact compatible_of_preceq_of_compatible hmono hcompat
  exact Proofs.ModelProperties.excludes_block_eq_false_of_compatible hFB

theorem stateBeforeTime_eq_stateBefore_filter_length
    (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time) :
    NamedRun.stateBeforeTime S rho t =
      NamedRun.stateBefore S rho
        (rho.events.filter (fun e => decide (e.time < t))).length := by
  let p : NamedEvent V → Bool := fun e => decide (e.time < t)
  have hpref : rho.events.filter p <+: rho.events := by
    rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (fun e f hk hf => by
        simp only [p, decide_eq_true_eq] at hf ⊢
        exact (Proofs.Bridges.time_le_of_key_le hk).trans_lt hf) _ hsorted]
    exact List.takeWhile_prefix p
  have hpre : rho.events.filter p =
      rho.events.take (rho.events.filter p).length :=
    List.prefix_iff_eq_take.mp hpref
  change (rho.events.filter p).foldl (NamedWorld.step S) NamedWorld.init =
    (rho.events.take (rho.events.filter p).length).foldl
      (NamedWorld.step S) NamedWorld.init
  exact congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init) hpre

theorem strict_filter_length_mono (rho : NamedRun V) {d read : Time}
    (hdr : d ≤ read) :
    (rho.events.filter (fun e => decide (e.time < d))).length ≤
      (rho.events.filter (fun e => decide (e.time < read))).length :=
  (List.monotone_filter_right rho.events
    (fun e he => by
      simp only [decide_eq_true_eq] at he ⊢
      exact lt_of_lt_of_le he hdr)).length_le

theorem index_succ_le_strict_filter_length (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (cut : Time)
    {j : Nat} {e : NamedEvent V} (he : rho.events[j]? = some e)
    (ht : e.time < cut) :
    j + 1 ≤ (rho.events.filter (fun x => decide (x.time < cut))).length := by
  obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp he
  have htake : (rho.events.take (j + 1)).filter (fun x => decide (x.time < cut)) =
      rho.events.take (j + 1) := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    have hklt : k < j + 1 := by
      have hlen := (List.getElem?_eq_some_iff.mp hk).1
      rw [List.length_take] at hlen
      exact hlen.trans_le (Nat.min_le_left _ _)
    have hkRun : rho.events[k]? = some x := by
      simpa only [List.getElem?_take_of_lt hklt] using hk
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hklt) with hkj | rfl
    · obtain ⟨hkLen, hkGet⟩ := List.getElem?_eq_some_iff.mp hkRun
      have hkey := (List.pairwise_iff_getElem.mp hsorted) k j hkLen hjLen hkj
      rw [hkGet, hjGet] at hkey
      exact (Proofs.Bridges.time_le_of_key_le hkey).trans_lt ht
    · have hxe : x = e := Option.some.inj (hkRun.symm.trans he)
      simpa only [hxe] using ht
  have hsplit : rho.events.filter (fun x => decide (x.time < cut)) =
      (rho.events.take (j + 1)).filter (fun x => decide (x.time < cut)) ++
      (rho.events.drop (j + 1)).filter (fun x => decide (x.time < cut)) := by
    conv_lhs => rw [← List.take_append_drop (j + 1) rho.events]
    rw [List.filter_append]
  have hlength := congrArg List.length hsplit
  rw [htake, List.length_append, List.length_take,
    Nat.min_eq_left (Nat.succ_le_of_lt hjLen)] at hlength
  omega

theorem stateBefore_F_preceq_stateBeforeTime_of_prefix
    (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {w : V} {d : Time} {i : Nat}
    (hi : i ≤ (rho.events.filter (fun e => decide (e.time < d))).length) :
    Block.Preceq (NamedRun.stateBefore S rho i w).st.core.F
      (NamedRun.stateBeforeTime S rho d w).st.core.F := by
  let n := (rho.events.filter (fun e => decide (e.time < d))).length
  rw [stateBeforeTime_eq_stateBefore_filter_length S rho hsorted d]
  exact NamedRuntime.stateBefore_F_mono S rho w hi

theorem finalized_preceq_at_prefix_of_storeBeforeRoot_preceq
    (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {w : V} {B : Block V} {d : Time}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho d w).st.core.toHealing.toFG) B)
    {i : Nat} (hi : i ≤
      (rho.events.filter (fun e => decide (e.time < d))).length) :
    Block.Preceq (NamedRun.stateBefore S rho i w).st.core.F B := by
  let n := (rho.events.filter (fun e => decide (e.time < d))).length
  have hmono := NamedRuntime.stateBefore_F_mono S rho w hi
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho d w
  have hFJ' : Block.preceq
      (NamedRun.stateBeforeTime S rho d w).st.core.toHealing.toFG.F
      (NamedRun.stateBeforeTime S rho d w).st.core.toHealing.toFG.J = true := by
    rw [ModelProperties.toHealing_F, ModelProperties.toHealing_J,
      ModelProperties.preceq_eq_true_iff_Preceq]
    exact hFJ
  have hFroot := Proofs.Records.preceq_get_fg_root_of_F
    (st := (NamedRun.stateBeforeTime S rho d w).st.core.toHealing.toFG) hFJ'
  rw [ModelProperties.preceq_eq_true_iff_Preceq, ModelProperties.toHealing_F] at hFroot
  have hFtime : Block.Preceq
      (NamedRun.stateBeforeTime S rho d w).st.core.F B :=
    ModelProperties.Preceq_trans hFroot hroot
  rw [stateBeforeTime_eq_stateBefore_filter_length S rho hsorted d] at hFtime
  exact ModelProperties.Preceq_trans hmono hFtime

/-- Compatibility at a later strict time read refutes exclusion. -/
theorem not_excludes_of_compatible_later_time
    (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {w : V} {B : NamedBlock V} {d read : Time} (hdr : d ≤ read)
    (hcompat : Block.compatible
      (NamedRun.stateBeforeTime S rho read w).st.core.F B.erase = true) :
    NamedReceipt.excludes (NamedRun.stateBeforeTime S rho d w).st (.block B) = false := by
  let nd := (rho.events.filter (fun e => decide (e.time < d))).length
  let nr := (rho.events.filter (fun e => decide (e.time < read))).length
  have hnd := stateBeforeTime_eq_stateBefore_filter_length S rho hsorted d
  have hnr := stateBeforeTime_eq_stateBefore_filter_length S rho hsorted read
  have hlen : nd ≤ nr := by
    exact strict_filter_length_mono rho hdr
  have hFidx : Block.compatible
      (NamedRun.stateBefore S rho nr w).st.core.F B.erase = true := by
    rw [← hnr]
    exact hcompat
  exact not_excludes_of_compatible_later S rho ⟨nd, hnd, hlen⟩ hFidx

/-- The finalized-prefix form follows from the compatible form. -/
theorem not_excludes_of_F_preceq_later_time
    (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {w : V} {B : NamedBlock V} {d read : Time} (hdr : d ≤ read)
    (hF : Block.Preceq (NamedRun.stateBeforeTime S rho read w).st.core.F B.erase) :
    NamedReceipt.excludes (NamedRun.stateBeforeTime S rho d w).st (.block B) = false := by
  apply not_excludes_of_compatible_later_time S rho hsorted hdr
  exact ModelProperties.compatible_eq_true_of_Preceq hF

end DecoupledConsensusModel.Proofs

end
