import EnvyFreeResearch.Full.RefinedUpperPreparationSurvival
import EnvyFreeResearch.Full.RefinedUpperPreparationIncrement
import EnvyFreeResearch.Full.RefinedUpperBoundaryError

/-! Local equality of original and retained measures inside every surviving
coarse parent, closing the physical retained-buffer interpolation bridge. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open MeasureTheory Set UpperRecordedDomain UpperLogicalCells RefinedUpperPeeling UpperGridInterpolation
open scoped Classical

lemma retained_interval_eq {a : ℕ} (B T : Set ℝ) (coarse : Fin (a+2) → ℝ)
    (removed : Finset (Fin (a+1)))
    (hT : T = ⋃ p, if p ∉ removed then cell B coarse p else ∅)
    (l r : ℝ) (p : Fin (a+1)) (hfit : intervalFits coarse (l,r) p)
    (hp : p ∉ removed) : T ∩ Ioc l r = B ∩ Ioc l r := by
  have hsub : T ⊆ B := by
    rw [hT]
    apply iUnion_subset
    intro q
    split_ifs
    · exact empty_subset _
    · exact cell_subset _ _ _
  apply subset_antisymm (inter_subset_inter_left _ hsub)
  intro x hx
  refine ⟨?_,hx.2⟩
  rw [hT]
  apply mem_iUnion.mpr
  refine ⟨p,?_⟩
  rw [if_pos hp]
  apply Or.inl
  exact ⟨hx.1,hfit.1.trans_lt hx.2.1,hx.2.2.trans hfit.2⟩

lemma normalized_retained_increment {a : ℕ} (μ : Measure ℝ) [IsFiniteMeasure μ]
    (B T : List Component) (coarse : Fin (a+2) → ℝ) (removed : Finset (Fin (a+1)))
    (hT : domain T = ⋃ p, if p ∉ removed then cell (domain B) coarse p else ∅)
    (l r : ℝ) (hlr : l ≤ r) (p : Fin (a+1)) (hfit : intervalFits coarse (l,r) p)
    (hp : p ∉ removed) (N : ℝ) :
    domainCumulative μ T r/N-domainCumulative μ T l/N =
      domainCumulative μ B r/N-domainCumulative μ B l/N := by
  rw [← sub_div,← sub_div,domainCumulative_sub μ T l r hlr,
    domainCumulative_sub μ B l r hlr,retained_interval_eq _ _ coarse removed hT l r p hfit hp]

/-- Both prefix and suffix errors for the physical retained buffer follow
from the original-buffer stability certificate, even with grid-dependent
normalizers and arbitrary holes in the original buffer. -/
theorem retained_physicalError_le {n a m : ℕ} {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Agent → Fin n) (origin : UpperCorrectionExecution.State n) (T : List Component)
    (N : Agent → ℝ) (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (coarse : Fin (a+2) → ℝ) (removed : Finset (Fin (a+1)))
    (hT : domain T = ⋃ p, if p ∉ removed then cell (domain origin.cells) coarse p else ∅)
    (cuts : Fin (m+2) → ℝ) (hcuts : Monotone cuts) (hzero : cuts 0 = 0)
    (e : Fin (m+1)) (p : Fin (a+1))
    (hfit : intervalFits coarse (cuts e.castSucc,cuts e.succ) p) (hsurvive : p ∉ removed)
    (z : ℝ) (hl : cuts e.castSucc ≤ z) (hr : z ≤ cuts e.succ) (i j : Agent) (A : ℝ)
    (hp : |((μ (active i)).real (domain origin.cells)/N i)*
        intervalValues (physicalCumulative μ active origin) i (cuts e.castSucc,z)-
      ((μ (active j)).real (domain origin.cells)/N j)*
        intervalValues (physicalCumulative μ active origin) j (cuts e.castSucc,z)| ≤ 2*A)
    (hs : |((μ (active i)).real (domain origin.cells)/N i)*
        intervalValues (physicalCumulative μ active origin) i (z,cuts e.succ)-
      ((μ (active j)).real (domain origin.cells)/N j)*
        intervalValues (physicalCumulative μ active origin) j (z,cuts e.succ)| ≤ 2*A) :
    UpperGridInterpolation.physicalError (fun r => μ (active r)) N T cuts z i j ≤ 2*A := by
  have hpref (r : Agent) :
      normalizedCumulative (fun r => μ (active r)) N T r z-
        normalizedCumulative (fun r => μ (active r)) N T r (cuts e.castSucc) =
      ((μ (active r)).real (domain origin.cells)/N r)*
        intervalValues (physicalCumulative μ active origin) r (cuts e.castSucc,z) := by
    rw [intervalValues_renormalized μ active origin r (hpositive r) _ _ hl]
    unfold normalizedCumulative
    rw [normalized_retained_increment (μ (active r)) origin.cells T coarse removed hT _ _ hl p
      ⟨hfit.1,hr.trans hfit.2⟩ hsurvive,← sub_div,domainCumulative_sub _ _ _ _ hl]
  have suffix (r : Agent) :
      normalizedCumulative (fun r => μ (active r)) N T r (cuts e.succ)-
        normalizedCumulative (fun r => μ (active r)) N T r z =
      ((μ (active r)).real (domain origin.cells)/N r)*
        intervalValues (physicalCumulative μ active origin) r (z,cuts e.succ) := by
    rw [intervalValues_renormalized μ active origin r (hpositive r) _ _ hr]
    unfold normalizedCumulative
    rw [normalized_retained_increment (μ (active r)) origin.cells T coarse removed hT _ _ hr p
      ⟨hfit.1.trans hl,hfit.2⟩ hsurvive,← sub_div,domainCumulative_sub _ _ _ _ hr]
  apply RefinedUpperBoundaryError.physicalError_le (fun r => μ (active r)) N T cuts hcuts hzero z e hl hr i j A
  · simpa only [hpref] using hp
  · simpa only [suffix] using hs

end EnvyFreeResearch.Full.RefinedUpperPreparation
