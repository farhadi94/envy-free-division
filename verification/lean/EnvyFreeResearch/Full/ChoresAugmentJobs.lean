import EnvyFreeResearch.Full.ChoresAugmentBatch
import EnvyFreeResearch.Full.ChoresAugmentQuantile

/-! The cached threshold creates the physical transfer jobs. Equal-length
reserved and designated lists are paired in their deterministic list order. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Augment
open Set OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open scoped Classical

variable {n : ℕ} {Label : Type*} [DecidableEq Label]

def thresholdJobs (c : Fin n) (threshold : ℝ) (pieces : Label → List (Parent n))
    (sources destinations : List Label) : List (TransferJob Label) :=
  (sources.zip destinations).map (fun sd =>
    ⟨sd.1,sd.2,threshold-OrderedUnion.cachedValue (pieces sd.2) c⟩)

theorem threshold_jobs_sources (c : Fin n) (threshold : ℝ) (pieces : Label → List (Parent n))
    (sources destinations : List Label) (hlen : sources.length=destinations.length) :
    (thresholdJobs c threshold pieces sources destinations).map TransferJob.source=sources := by
  simp only [thresholdJobs,List.map_map]
  exact List.map_fst_zip hlen.le

theorem threshold_jobs_destinations (c : Fin n) (threshold : ℝ) (pieces : Label → List (Parent n))
    (sources destinations : List Label) (hlen : sources.length=destinations.length) :
    (thresholdJobs c threshold pieces sources destinations).map TransferJob.destination=destinations := by
  simp only [thresholdJobs,List.map_map]
  exact List.map_snd_zip hlen.symm.le

theorem threshold_jobs_length (c : Fin n) (threshold : ℝ) (pieces : Label → List (Parent n))
    (sources destinations : List Label) (hlen : sources.length=destinations.length) :
    (thresholdJobs c threshold pieces sources destinations).length=sources.length := by
  have h := congrArg List.length (threshold_jobs_sources c threshold pieces sources destinations hlen)
  simpa using h

theorem threshold_batch_correct (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (c : Fin n) (threshold : ℝ) (pieces : Label → List (Parent n)) (hv : FamilyValid P pieces)
    (sources destinations : List Label) (hlen : sources.length=destinations.length)
    (hs : sources.Nodup) (hd : destinations.Nodup)
    (hcross : ∀ s ∈ sources, ∀ d ∈ destinations, s ≠ d)
    (hlow : ∀ d ∈ destinations, OrderedUnion.cachedValue (pieces d) c ≤ threshold)
    (hcap : ∀ s ∈ sources, threshold ≤ OrderedUnion.cachedValue (pieces s) c)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ next trace, Executes oracle (transferBatch c (thresholdJobs c threshold pieces sources destinations) pieces)
        prior next trace ∧
      trace.length ≤ sources.length*n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ sources.length ∧
      FamilyValid P next ∧ familyMaterial next=familyMaterial pieces ∧
      (∀ j, j ∉ sources → j ∉ destinations → next j=pieces j) ∧
      (∀ j, j ∉ sources → material (pieces j) ⊆ material (next j)) ∧
      (∀ j, j ∉ sources → ∀ i, OrderedUnion.cachedValue (pieces j) i ≤ OrderedUnion.cachedValue (next j) i) ∧
      ∀ d ∈ destinations, OrderedUnion.cachedValue (next d) c=threshold := by
  let jobs := thresholdJobs c threshold pieces sources destinations
  have hss : jobs.map TransferJob.source=sources := threshold_jobs_sources c threshold pieces sources destinations hlen
  have hdd : jobs.map TransferJob.destination=destinations := threshold_jobs_destinations c threshold pieces sources destinations hlen
  have hcross' : ∀ a ∈ jobs, ∀ b ∈ jobs, a.source ≠ b.destination := by
    intro a ha b hb
    apply hcross a.source
    · rw [← hss]; exact List.mem_map.mpr ⟨a,ha,rfl⟩
    · rw [← hdd]; exact List.mem_map.mpr ⟨b,hb,rfl⟩
  have hamount (j : TransferJob Label) (hj : j ∈ jobs) :
      j.amount=threshold-OrderedUnion.cachedValue (pieces j.destination) c := by
    obtain ⟨sd,hsd,rfl⟩ := List.mem_map.mp hj
    rfl
  have hfit : ∀ j ∈ jobs, 0 ≤ j.amount ∧ j.amount ≤ OrderedUnion.cachedValue (pieces j.source) c := by
    intro j hj
    have hs' : j.source ∈ sources := hss ▸ List.mem_map.mpr ⟨j,hj,rfl⟩
    have hd' : j.destination ∈ destinations := hdd ▸ List.mem_map.mpr ⟨j,hj,rfl⟩
    rw [hamount j hj]
    exact supplement_feasible _ _ _ (cachedValue_nonnegative P hmono (hv.1 j.destination).1 c)
      (hlow j.destination hd') (hcap j.source hs')
  obtain ⟨next,trace,hexec,hQ,hC,hv',hcover,hother,hsub,hmon,htarget⟩ :=
    transfer_batch_correct P hmono oracle hpolicy c jobs (hss ▸ hs) (hdd ▸ hd) hcross' pieces hv hfit prior
  have hlength : jobs.length=sources.length := threshold_jobs_length c threshold pieces sources destinations hlen
  refine ⟨next,trace,hexec,?_,?_,hv',hcover,?_,?_,?_,?_⟩
  · simpa only [hlength] using hQ
  · simpa only [hlength] using hC
  · simpa only [hss,hdd] using hother
  · simpa only [hss] using hsub
  · simpa only [hss] using hmon
  · intro d hd'
    have hm : d ∈ jobs.map TransferJob.destination := hdd.symm ▸ hd'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
    rw [htarget j hj,hamount j hj]
    ring

end EnvyFreeResearch.Full.Chores.Augment
