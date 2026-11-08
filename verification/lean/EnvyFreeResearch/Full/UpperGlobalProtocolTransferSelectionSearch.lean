import EnvyFreeResearch.Full.UpperGlobalProtocolTransferSelectionData

/-! Deterministic finite first-valid search. This can examine k! permutations;
only query complexity, not efficient arithmetic runtime, is claimed. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobal.Transfer.Selection
open MeasureTheory
open scoped Classical

variable {k : ℕ}

instance (k : ℕ) : MeasurableSpace (Option (Candidate k)) := ⊤
instance (k : ℕ) : DiscreteMeasurableSpace (Option (Candidate k)) := ⟨fun _ => trivial⟩

def candidateList (k : ℕ) : List (Candidate k) := Finset.univ.toList

def optionValid (tau : ℝ) (data : CachedData k) : Option (Candidate k) → Prop
  | none => False
  | some c => Valid tau data c

def select (tau : ℝ) (data : CachedData k) : Option (Candidate k) :=
  firstSafe none (optionValid tau data) ((candidateList k).map some)

theorem optionValid_measurable (tau : ℝ) (c : Option (Candidate k)) :
    MeasurableSet {data : CachedData k | optionValid tau data c} := by
  cases c with
  | none => exact MeasurableSet.empty
  | some c => exact valid_measurable tau c

theorem select_measurable (tau : ℝ) : Measurable (select (k := k) tau) :=
  firstSafe_measurable none (optionValid tau) _ (optionValid_measurable tau)

theorem select_correct (tau : ℝ) (data : CachedData k)
    (hexists : ∃ c, Valid tau data c) :
    ∃ c, select tau data=some c ∧ Valid tau data c := by
  have hgood : optionValid tau data (select tau data) := by
    apply firstSafe_good
    obtain ⟨c,hc⟩ := hexists
    refine ⟨some c,?_,hc⟩
    exact List.mem_map.mpr ⟨c,by simp [candidateList],rfl⟩
  cases heq : select tau data with
  | none => rw [heq] at hgood; exact hgood.elim
  | some c => exact ⟨c,rfl,by simpa only [heq,optionValid] using hgood⟩

def candidateEquiv (k : ℕ) : Candidate k ≃
    ((Equiv.Perm (Fin k) × Fin k × Fin k) ⊕ (Fin k × Fin k)) where
  toFun
    | .commit alpha b h => .inl (alpha,b,h)
    | .shrink p q => .inr (p,q)
  invFun
    | .inl (alpha,b,h) => .commit alpha b h
    | .inr (p,q) => .shrink p q
  left_inv c := by cases c <;> rfl
  right_inv c := by rcases c with ⟨alpha,b,h⟩ | ⟨p,q⟩ <;> rfl

theorem candidateList_length (k : ℕ) :
    (candidateList k).length=Nat.factorial k*k^2+k^2 := by
  rw [candidateList,Finset.length_toList,Finset.card_univ]
  rw [Fintype.card_congr (candidateEquiv k)]
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_perm,Fintype.card_fin,pow_two]

end EnvyFreeResearch.Full.UpperGlobal.Transfer.Selection
