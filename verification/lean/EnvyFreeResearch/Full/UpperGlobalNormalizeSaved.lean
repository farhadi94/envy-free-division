import EnvyFreeResearch.Full.UpperGlobalNormalizeCore

/-! Nonterminal normalization only freezes owners: saved bundles, residue,
and their histories remain literally unchanged. -/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalNormalize
open UpperGlobalPhysical UpperGlobal.Sink UpperZeroRows
variable {n : ℕ}

def Saved (before after : Anchor n) : Prop :=
  after.bundles=before.bundles ∧ after.residue=before.residue ∧ after.active ⊆ before.active

theorem Saved.refl (a : Anchor n) : Saved a a := ⟨rfl,rfl,fun _ h => h⟩

theorem Saved.trans {a b c : Anchor n} (hab : Saved a b) (hbc : Saved b c) : Saved a c :=
  ⟨hbc.1.trans hab.1,hbc.2.1.trans hab.2.1,hbc.2.2.trans hab.2.2⟩

def Request.SavedFrom (before : Anchor n) : Request n → Prop
  | .done _ => True
  | .two after _ _ | .snapshot after => Saved before after

theorem Request.SavedFrom.trans {a b : Anchor n} {request : Request n}
    (hab : Saved a b) (hr : request.SavedFrom b) : request.SavedFrom a := by
  cases request with
  | done _ => trivial
  | two _ _ _ => exact hab.trans hr
  | snapshot _ => exact hab.trans hr

theorem positiveCore_saved (fallback : Fin n) (chores : Bool) (fuel : ℕ) (a : Anchor n) :
    (positiveCore fallback chores fuel a).SavedFrom a := by
  induction fuel generalizing a with
  | zero => exact Saved.refl a
  | succ fuel ih =>
    by_cases h1 : a.active.card ≤ 1
    · simp only [positiveCore,h1,ite_true,Request.SavedFrom]
    · by_cases h2 : a.active.card ≤ 2
      · simpa only [positiveCore,h1,ite_false,h2,ite_true,Request.SavedFrom] using Saved.refl a
      · by_cases hs : sinkAvailable (direction chores) a = true
        · have hp := selectedFreeze_progress (direction chores) a ((sinkAvailable_iff _ _).mp hs)
          have hsaved : Saved a (selectedFreeze (direction chores) a) := ⟨rfl,rfl,hp.2.1⟩
          simpa only [positiveCore,h1,h2,hs,ite_false,ite_true] using (ih _).trans hsaved
        · have hf : sinkAvailable (direction chores) a = false := Bool.eq_false_iff.mpr hs
          simpa only [positiveCore,h1,h2,hf,ite_false,Bool.false_eq_true,Request.SavedFrom] using Saved.refl a

theorem normalize_saved (fallback : Fin n) (chores : Bool) (fuel : ℕ) (a : Anchor n) :
    (normalize fallback chores fuel a).SavedFrom a := by
  unfold normalize
  split_ifs
  · trivial
  · exact positiveCore_saved _ _ _ _
  · exact Request.SavedFrom.trans (a:=a) (b:=freezeZero a)
      ⟨rfl,rfl,positiveRows_subset _ _⟩ (positiveCore_saved fallback chores fuel (freezeZero a))
  · trivial

end EnvyFreeResearch.Full.UpperGlobalNormalize
