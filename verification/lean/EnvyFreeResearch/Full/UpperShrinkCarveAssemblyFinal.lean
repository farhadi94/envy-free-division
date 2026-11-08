import EnvyFreeResearch.Full.UpperShrinkCarveAssemblyMesh

/-! The actual finite mesh's cached moments imply the physical Shrink contract.
This endpoint does not assume a successful carve allocation as an input. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperEndpointCache
variable {n k : ℕ}

theorem mesh_weights_correct (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (active : Fin k → Fin n)
    (normal : Fin k → ℝ) (mesh : Mesh n k)
    (hpieces : ∀ e, WellFormed μ (meshStates mesh e)) (i : Fin k) (e : Fin mesh.pieces.length) :
    weights active normal mesh i e = (μ (active i)).real (domain (meshStates mesh e).cells) / normal i := by
  unfold weights
  change total (meshStates mesh e) (active i) / normal i = _
  rw [total_correct μ _ (hpieces e)]

theorem meshCarve_valid (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (active : Fin k → Fin n)
    (origin : State n) (mesh : Mesh n k)
    (hpieces : ∀ e, WellFormed μ (meshStates mesh e))
    (hpair : Pairwise (fun e f => Disjoint (domain (meshStates mesh e).cells) (domain (meshStates mesh f).cells)))
    (htruth : Truthful μ mesh.history)
    (hcover : (⋃ e, domain (meshStates mesh e).cells)=domain origin.cells)
    (hnormal : ∀ i, 0 < (μ (active i)).real (domain origin.cells)) (G tau : ℝ)
    (hbox : ∀ e c, 0 ≤ meshFractions mesh e c ∧ meshFractions mesh e c ≤ 1)
    (hrow : ∀ e, ∑ c, meshFractions mesh e c=1)
    (hmoment : ∀ i j, ∑ e, weights active (fun i => (μ (active i)).real (domain origin.cells)) mesh i e *
      meshFractions mesh e (some j)=UpperShrink.fraction k G)
    (hloss : ∀ i, ∑ e ∈ UpperWholePayments.splitCells (meshFractions mesh),
      weights active (fun i => (μ (active i)).real (domain origin.cells)) mesh i e ≤ UpperShrink.error tau G) :
    (meshCarve mesh).Valid μ active origin G tau := by
  rw [meshCarve_eq]
  apply assembled_valid μ active origin (meshStates mesh) mesh.history hpieces hpair htruth
    (fun _ => Subset.rfl) hcover hnormal _ G tau hbox hrow
  · simpa only [mesh_weights_correct μ active _ mesh hpieces] using hmoment
  · simpa only [mesh_weights_correct μ active _ mesh hpieces] using hloss

end EnvyFreeResearch.Full.UpperShrinkCarve
