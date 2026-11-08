import EnvyFreeResearch.Full.ChoresTerminalPool

/-! The terminal physical allocation includes all earlier closed packages,
not only the newly compensated cohort. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion ChoreComposition
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Outer.Data n RootId) (original : RootId → Snapshot.Output n)
  (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H)
  (package : Package (Fin n) RootId) (hp : package.Valid)
  (hids : package.ids.Perm ((List.ofFn data.packages).flatMap Package.ids))
  (next : Fin data.size → Fin n → List (Parent n))
  (G : PackageGeometry.Pieces RootId (Fin n))
  (hsub : ∀ root p, material (ComponentPhysical.patchCache data.frames data.cache next root p) ⊆ G.piece root p)
  (hv : ∀ root p, Valid (measureProfile cost) (ComponentPhysical.patchCache data.frames data.cache next root p) ∧
    Ordered (ComponentPhysical.patchCache data.frames data.cache next root p))
  (hreal : ∀ a ∈ package.allocations, ∀ i p,
    a.cost i p=(cost i).real (material (ComponentPhysical.patchCache data.frames data.cache next a.root p)))

include good hp hids hsub hv hreal

theorem final_pool_sound :
    (Outer.poolAllocation (finalPool data package)
      (ComponentPhysical.patchCache data.frames data.cache next)).Sound cost id
      (Outer.poolDomain (finalPool data package) (ComponentPhysical.patchCache data.frames data.cache next)) := by
  apply Outer.pool_allocation_sound (finalPool data package)
    (final_pool_valid data original cost r H good package hp)
    ((final_pool_ids data original cost r H good package hids).nodup_iff.mpr (Finset.nodup_toList _))
    G _ hsub cost hv
  intro a ha i p
  change a ∈ (data.closed++[package]).flatMap Package.allocations at ha
  rw [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] at ha
  rcases List.mem_append.mp ha with ha | ha
  · exact closed_cost_after_patch data original cost r H good next a ha i p
  · exact hreal a ha i p

omit hp hsub hv hreal in
theorem final_pool_domain :
    Outer.poolDomain (finalPool data package) (ComponentPhysical.patchCache data.frames data.cache next)=
      ⋃ root, ⋃ p, material (ComponentPhysical.patchCache data.frames data.cache next root p) :=
  Outer.pool_domain_all_roots _ _ (final_pool_ids data original cost r H good package hids)

end EnvyFreeResearch.Full.Chores.Terminal
