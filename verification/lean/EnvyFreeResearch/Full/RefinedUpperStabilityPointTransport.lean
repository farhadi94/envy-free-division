import EnvyFreeResearch.Full.RefinedUpperStabilityProcedure
import EnvyFreeResearch.Full.RefinedUpperStabilitySortedControl

/-! Transport of the concrete cumulative-grid procedure to physical intervals. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open UpperRepresentativeSupply
open scoped Classical
variable {Row : Type*} {a M : ℕ}

def intervalValues (F : Row → ℝ → ℝ) (r : Row) (c : ℝ × ℝ) : ℝ := max 0 (F r c.2-F r c.1)

lemma intervalValues_nonneg (F : Row → ℝ → ℝ) (r : Row) (c : ℝ × ℝ) : 0 ≤ intervalValues F r c :=
  le_max_left _ _

lemma pointValues_intervalValues (F : Row → ℝ → ℝ) (hF : ∀ r, Monotone (F r))
    (points : Fin (M+2) → ℝ) (hm : Monotone points) :
    (fun r => intervalValues F r ∘ intervalLabel points) = pointValues F points := by
  funext r c
  apply max_eq_right
  exact sub_nonneg.mpr (hF r (hm (by simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ]; omega)))

lemma pointRun_interval_run (F : Row → ℝ → ℝ) (hF : ∀ r, Monotone (F r))
    (coarse : Fin (a+2) → ℝ) (jobs : List (Row × Row))
    (points : Fin (M+2) → ℝ) (hm : Monotone points) :
    run (intervalValues F) (intervalParent coarse) (List.ofFn (intervalLabel points)) jobs ∅ =
      (pointRun F coarse jobs points).map
        (fun result => (result.1.map (fun p => (intervalLabel points p.1,intervalLabel points p.2)),result.2)) := by
  have h := run_map (intervalLabel points) (intervalValues F) (intervalParent coarse)
    (List.finRange (M+1)) jobs ∅
  rw [pointValues_intervalValues F hF points hm] at h
  unfold pointRun pointParents
  simpa only [List.finRange, List.map_ofFn,Function.comp_def] using h

lemma pointSelect_interval_select (F : Row → ℝ → ℝ) (hF : ∀ r, Monotone (F r))
    (coarse : Fin (a+2) → ℝ) (points : Fin (M+2) → ℝ) (hm : Monotone points)
    (final : Finset (Fin (a+1))) (i j : Row) :
    select (intervalValues F i) (intervalValues F j)
      (available (intervalParent coarse) final (List.ofFn (intervalLabel points))) =
      (select (pointValues F points i) (pointValues F points j)
        (available (pointParents coarse points) final (List.finRange (M+1)))).map
        (fun p => (intervalLabel points p.1,intervalLabel points p.2)) := by
  have hv := pointValues_intervalValues F hF points hm
  have hc : List.ofFn (intervalLabel points) = (List.finRange (M+1)).map (intervalLabel points) := by
    simp [List.finRange,List.map_ofFn,Function.comp_def]
  rw [hc,available_map]
  have hs := RefinedUpperWitnessSelector.select_map (intervalLabel points)
    (fun c => (intervalValues F i c,intervalValues F j c))
    (available (pointParents coarse points) final (List.finRange (M+1)))
  have hvi := congrFun hv i
  have hvj := congrFun hv j
  change (intervalValues F i ∘ intervalLabel points) = pointValues F points i at hvi
  change (intervalValues F j ∘ intervalLabel points) = pointValues F points j at hvj
  simp only [select, ← hvi, ← hvj, pointParents, Function.comp_def]
  unfold pointParents at hs ⊢
  simpa only [Function.comp_def] using hs

end EnvyFreeResearch.Full.RefinedUpperPeeling
