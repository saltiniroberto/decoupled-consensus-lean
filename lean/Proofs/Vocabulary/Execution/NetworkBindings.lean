module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedAdmissible
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Authentication of actual handler calls

An object an actual handler call processes, whose author is honest, was emitted by that author no
later than the call.
-/
namespace DecoupledConsensusModel.Proofs.NamedNetworkBindings
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]


private theorem direct_index_processes_at (S : Setup V) (rho : NamedRun V)
    {i : Nat} {receiver : V} {o : NamedObject V} {t : Time}
    (hcall : NamedRun.processesAtIndex S rho i receiver o)
    (htimed : ∃ e : NamedEvent V, rho.events[i]? = some e ∧ e.node = receiver ∧ e.time = t) :
    NamedRun.processes S rho receiver o t := by
  obtain ⟨e, he, _, ht⟩ := htimed
  rcases hcall with ⟨time, hi, hem⟩ | ⟨time, hi⟩
  · have heq : NamedEvent.tick receiver time = e := Option.some.inj (hi.symm.trans he)
    have htime : time = t := by
      simpa only [NamedEvent.time] using (congrArg NamedEvent.time heq).trans ht
    subst time
    exact Or.inl ⟨i, hi, hem⟩
  · have heq : NamedEvent.deliver receiver o time = e := Option.some.inj (hi.symm.trans he)
    have htime : time = t := by
      simpa only [NamedEvent.time] using (congrArg NamedEvent.time heq).trans ht
    subst time
    exact Or.inr ⟨i, hi⟩

/-- A block handler call at event index `i` processes the block at that event's time. -/
private theorem block_call_processes_at (S : Setup V) (rho : NamedRun V)
    {i : Nat} {receiver : V} {B : NamedBlock V} {before : Protocol.NamedStore V} {t : Time}
    (hcall : Execution.NamedReceiptCalls.blockCallAt S rho i receiver B before)
    (htimed : ∃ e : NamedEvent V, rho.events[i]? = some e ∧ e.node = receiver ∧ e.time = t) :
    NamedRun.processes S rho receiver (.block B) t := by
  apply direct_index_processes_at S rho ?_ htimed
  rcases hcall with ⟨time, hi, _⟩ | ⟨time, hi, hem, _⟩
  · exact Or.inr ⟨time, hi⟩
  · exact Or.inl ⟨time, hi, hem⟩

/-- Authentication of actual handler calls, derived from the three full-object clauses. -/
private theorem authentic_actual_handles_of_clauses (S : Setup V) (rho : NamedRun V)
    (hDirect : ∀ receiver o t, NamedRun.processes S rho receiver o t →
      ∀ author ∈ rho.honest, o.author = some author →
        ∃ sent, sent ≤ t ∧ NamedRun.emits S rho author o sent)
    (hCarriedGF : ∀ receiver B t, NamedRun.processes S rho receiver (.block B) t →
      ∀ u ∈ B.gf_votes, u.val_index ∈ rho.honest →
        ∃ sent, sent ≤ t ∧ NamedRun.emits S rho u.val_index (.gfVote u) sent)
    (hCarriedRow : ∀ receiver B t, NamedRun.processes S rho receiver (.block B) t →
      ∀ a ∈ B.attestations, a.val_index ∈ rho.honest →
        ∃ sent, sent ≤ t ∧ NamedRun.emits S rho a.val_index (.attest a) sent)
    {i : Nat} {receiver author : V} {o : NamedObject V} {t : Time}
    (h : NamedRun.actualHandlesAt S rho i receiver o t)
    (hHon : author ∈ rho.honest) (hAuthor : o.author = some author) :
    ∃ sent, sent ≤ t ∧ NamedRun.emits S rho author o sent := by
  obtain ⟨hcall, htimed⟩ := h
  cases o with
  | block B =>
    exact hDirect receiver (.block B) t
      (direct_index_processes_at S rho hcall htimed) author hHon hAuthor
  | gfVote u =>
    rcases hcall with hdirect | ⟨B, j, before, hcarrier, _, _, hindex⟩
    · exact hDirect receiver (.gfVote u) t
        (direct_index_processes_at S rho hdirect htimed) author hHon hAuthor
    · have hval : u.val_index = author := Option.some.inj hAuthor
      have hbody := block_call_processes_at S rho hcarrier htimed
      have hmember : u ∈ B.gf_votes := List.mem_of_getElem? hindex
      have hsigner : u.val_index ∈ rho.honest := hval.symm ▸ hHon
      simpa only [hval] using hCarriedGF receiver B t hbody u hmember hsigner
  | attest a =>
    rcases hcall with hdirect | ⟨B, j, before, hcarrier, _, _, hindex⟩
    · exact hDirect receiver (.attest a) t
        (direct_index_processes_at S rho hdirect htimed) author hHon hAuthor
    · have hval : a.val_index = author := Option.some.inj hAuthor
      have hbody := block_call_processes_at S rho hcarrier htimed
      have hmember : a ∈ B.attestations := List.mem_of_getElem? hindex
      have hsigner : a.val_index ∈ rho.honest := hval.symm ▸ hHon
      simpa only [hval] using hCarriedRow receiver B t hbody a hmember hsigner

/-- Under `NamedUnforgeable`, an object an actual handler call processes at `t`, whose author is
    honest, was emitted by that author no later than `t`. -/
theorem actual_handles_authenticated (S : Setup V) (rho : NamedRun V)
    (auth : NamedUnforgeable S rho)
    {i : Nat} {receiver author : V} {o : NamedObject V} {t : Time}
    (h : NamedRun.actualHandlesAt S rho i receiver o t)
    (hHon : author ∈ rho.honest) (hAuthor : o.author = some author) :
    ∃ sent, sent ≤ t ∧ NamedRun.emits S rho author o sent :=
  authentic_actual_handles_of_clauses S rho auth.unforgeable auth.carried_gf
    auth.carried_attest h hHon hAuthor


#print axioms actual_handles_authenticated
end DecoupledConsensusModel.Proofs.NamedNetworkBindings

end
