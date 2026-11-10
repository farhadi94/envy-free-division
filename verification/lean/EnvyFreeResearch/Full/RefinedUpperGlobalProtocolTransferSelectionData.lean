import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolTransferSelected

/-! Finite transfer candidates and cached input data. The graph, all gap
entries and residue masses are already recorded; validation issues no queries. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobal.Transfer.Selection
open MeasureTheory
open scoped Classical

inductive Candidate (k : ℕ) where
  | commit (alpha : Equiv.Perm (Fin k)) (b h : Fin k)
  | shrink (p q : Fin k)
  deriving Fintype

instance (k : ℕ) : MeasurableSpace (Candidate k) := ⊤
instance (k : ℕ) : DiscreteMeasurableSpace (Candidate k) := ⟨fun _ => trivial⟩

abbrev CachedData (k : ℕ) :=
  (Fin k → Fin k → Bool) × (Fin k → Fin k → ℝ) × (Fin k → ℝ)

def Valid {k : ℕ} (tau : ℝ) (data : CachedData k) : Candidate k → Prop
  | .commit alpha b h => data.1 b h=true ∧
      (∀ i, data.2.1 i (alpha i) ≤ tau*data.2.2 i) ∧
      2*data.2.2 b ≤ data.2.1 b (alpha h)
  | .shrink p q => data.1 p q=true ∧ tau*data.2.2 p < data.2.1 p q

theorem graph_measurable {k : ℕ} (i j : Fin k) :
    Measurable (fun data : CachedData k => data.1 i j) := by fun_prop

theorem gap_measurable {k : ℕ} (i j : Fin k) :
    Measurable (fun data : CachedData k => data.2.1 i j) := by fun_prop

theorem residue_measurable {k : ℕ} (i : Fin k) :
    Measurable (fun data : CachedData k => data.2.2 i) := by fun_prop

theorem valid_measurable {k : ℕ} (tau : ℝ) (c : Candidate k) :
    MeasurableSet {data : CachedData k | Valid tau data c} := by
  cases c with
  | commit alpha b h =>
    have hgraph : MeasurableSet {data : CachedData k | data.1 b h=true} :=
      (graph_measurable b h) (measurableSet_singleton true)
    have hown : MeasurableSet {data : CachedData k | ∀ i, data.2.1 i (alpha i) ≤ tau*data.2.2 i} := by
      simp only [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro i
      exact measurableSet_le (gap_measurable i (alpha i)) ((residue_measurable i).const_mul tau)
    have hlarge : MeasurableSet {data : CachedData k | 2*data.2.2 b ≤ data.2.1 b (alpha h)} :=
      measurableSet_le ((residue_measurable b).const_mul 2) (gap_measurable b (alpha h))
    exact hgraph.inter (hown.inter hlarge)
  | shrink p q =>
    have hgraph : MeasurableSet {data : CachedData k | data.1 p q=true} :=
      (graph_measurable p q) (measurableSet_singleton true)
    exact hgraph.inter (measurableSet_lt ((residue_measurable p).const_mul tau) (gap_measurable p q))

end EnvyFreeResearch.Full.RefinedUpperGlobal.Transfer.Selection
