import EnvyFreeResearch.Full.UpperShrinkCarveInvariants
import EnvyFreeResearch.Full.UpperShrinkCarveInitialMoments
import EnvyFreeResearch.Full.UpperShrinkCarveSparse
import EnvyFreeResearch.Full.UpperShrinkCarveAssemblyFinal
import EnvyFreeResearch.Full.UpperShrinkCarvePhysicalIndexed

/-! The actual initialized median/floating loop and final material grouping
satisfy the physical carving contract. Its moments, error, caches and complete
partition are consequences of execution, rather than premises describing an
assumed successful carve. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage

variable {n k : ℕ} (μ : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]

theorem initialized_valid (policy : Policy n)
    (hp : Admissible (Chores.measureProfile μ) policy) (active : Fin k → Fin n)
    (origin : State n) (ho : WellFormed μ origin) (G tau : ℝ) (J : ℕ)
    (hn : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (hf : 0 ≤ UpperShrink.fraction k G) (hcap : (k:ℝ)*UpperShrink.fraction k G ≤ 1)
    (hprecision : (k:ℝ)^2 / 2^J ≤ UpperShrink.error tau G) :
    (meshCarve (roundsExecute policy active
      (fun i => (μ (active i)).real (domain origin.cells)) J
      (initial origin (UpperShrink.fraction k G)))).Valid μ active origin G tau := by
  let normal : Fin k → ℝ := fun i => (μ (active i)).real (domain origin.cells)
  let start : Mesh n k := initial origin (UpperShrink.fraction k G)
  let final := roundsExecute policy active normal J start
  have hstart := initial_physical μ origin ho (k:=k) (UpperShrink.fraction k G)
  have hv := initial_fractions_valid origin (UpperShrink.fraction k G) hf hcap
  have hphy : final.Physical μ (domain origin.cells) := rounds_physical μ policy hp active normal J start _ hstart
  have hfv : final.FractionsValid := rounds_fractions_valid policy active normal J start hv
  have hbound := rounds_split_bound μ policy hp active normal J start _ hstart hv normal
    (initial_split_bound μ active origin (UpperShrink.fraction k G))
  apply meshCarve_valid μ active origin final
    (fun e => hphy.pieces _ (List.get_mem _ e))
    (hphy.indexed_disjoint μ) hphy.truthful
    (hphy.indexed_cover μ) hn G tau
    (fun e c => (hfv _ (List.get_mem _ e)).1 c)
    (fun e => (hfv _ (List.get_mem _ e)).2)
  · intro i j
    change (∑ e, weights active normal final i e*(final.pieces.get e).fraction (some j)) = _
    rw [cached_moment μ active normal final hphy.pieces]
    have hm := rounds_moment μ policy hp active normal J start _ hstart hv
      (fun i => ne_of_gt (hn i)) i j
    change moment (μ (active i)) final.pieces j = _ at hm
    rw [hm,initial_moment _ origin ho.2.1]
    change (normal i*UpperShrink.fraction k G)/normal i=UpperShrink.fraction k G
    exact mul_div_cancel_left₀ _ (ne_of_gt (hn i))
  · intro i
    have hsmall : ∀ i e, e ∈ UpperWholePayments.splitCells (meshFractions final) →
        weights active normal final i e ≤ 1/2^J := by
      intro i e he
      rw [weights,total_correct μ _ (hphy.pieces _ (List.get_mem _ e))]
      have hs : split (final.pieces.get e) := (Finset.mem_filter.mp he).2
      have hb := hbound _ (List.get_mem _ e) hs i
      apply (div_le_iff₀ (hn i)).mpr
      simpa only [normal,one_div,div_eq_mul_inv,mul_comm,one_mul] using hb
    have hc : (UpperWholePayments.splitCells (meshFractions final)).card ≤ k^2 := by
      rw [mesh_split_count]
      exact rounds_sparse policy active normal J start hv
    have hsum := sparse_split_mass (weights active normal final) (meshFractions final)
      (1/2^J) (by positivity) (by simpa using hc) hsmall i
    change (∑ e ∈ UpperWholePayments.splitCells (meshFractions final),weights active normal final i e) ≤ _
    apply hsum.trans
    simpa only [Fintype.card_fin,div_eq_mul_inv,one_mul] using hprecision

end EnvyFreeResearch.Full.UpperShrinkCarve
