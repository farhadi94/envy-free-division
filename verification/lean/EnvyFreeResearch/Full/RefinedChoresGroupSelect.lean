import EnvyFreeResearch.Full.RefinedChoresDataGroup
import EnvyFreeResearch.Full.ChoresRevealPendingGeometry

/-! Normal cohorts are selected from the computed finite scan classes.
The only synchronization is label, source component and dyadic mass bucket. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Chores Chores.Frontier RefinedChoresPool
open scoped Classical
variable {n : ℕ} {RootId : Type*} (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)

theorem normal_class_scan (s : Fin data.size) (p : Fin n) (C : Finset (Fin n))
    (b : Fin (buckets n)) (h : data.classify normal original r H s = .inl (.inl (p,C,b))) :
    data.sourceLabel normal s = p ∧ data.sourceSet normal s = C ∧
      rawBucket n (data.packages s).ids.length = b ∧
      ∃ q, data.scan normal original r H s = .outside q := by
  unfold Data.classify at h
  cases hs : data.scan normal original r H s with
  | outside q =>
    rw [hs] at h
    have he := Sum.inl.inj (Sum.inl.inj h)
    exact ⟨congrArg (fun t => t.1) he,congrArg (fun t => t.2.1) he,
      congrArg (fun t => t.2.2) he,⟨q,rfl⟩⟩
  | atomic a => simp only [hs] at h; cases h
  | exhausted q => simp only [hs] at h; cases h

theorem normal_group_exists (p : Fin n) (C : Finset (Fin n)) (b : Fin (buckets n))
    (hcount : n+1 ≤ (Finset.univ.filter (fun s => data.classify normal original r H s = .inl (.inl (p,C,b)))).card)
    (hr : ∀ i, 0 ≤ r i) (hH : 0 < H) : Nonempty (Group data normal original r H) := by
  have hcard : Fintype.card (Fin (C.card+1)) ≤
      (Finset.univ.filter (fun s => data.classify normal original r H s = .inl (.inl (p,C,b)))).card := by
    have hc : C.card ≤ n := (Finset.card_le_card (Finset.subset_univ C)).trans_eq (by simp)
    simp only [Fintype.card_fin]
    omega
  obtain ⟨roots,hroots⟩ := Function.Embedding.exists_of_card_le_finset hcard
  have hf (s : Fin (C.card+1)) :=
    (Finset.mem_filter.mp (hroots ⟨s,rfl⟩)).2
  have hd (s : Fin (C.card+1)) := normal_class_scan data normal original r H (roots s) p C b (hf s)
  let target : Fin (C.card+1) → Fin n := fun s => (hd s).2.2.2.choose
  have hscan (s : Fin (C.card+1)) : data.scan normal original r H (roots s) = .outside (target s) :=
    (hd s).2.2.2.choose_spec
  refine ⟨⟨p,C,roots,fun s => (hd s).1,fun s => (hd s).2.1,b,fun s => (hd s).2.2.1,target,hscan,?_⟩⟩
  intro s
  have hs := hscan s
  simp only [Data.scan,(hd s).1,(hd s).2.1] at hs
  have h := (Reveal.scan_outside_stop _ p r H C (target s) hs (hr p) hH).1
  exact (Finset.mem_sdiff.mp h.1).2

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.normal_group_exists
