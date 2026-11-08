import EnvyFreeResearch.Full.UpperSnapshotSmallRecorded
import EnvyFreeResearch.Full.UpperVirtualGrid
import EnvyFreeResearch.Full.UpperCorrectionPieces

/-! Virtual boundary witnesses for actual shared-circle pieces. The original
physical component joins are supplied by intersection and incur no endpoint
charges. No independence or regularity of the returned roots is assumed. -/
noncomputable section
open Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperRecordedDomain UpperDomainDifference UpperPhysical UpperAggregateInterpolation
  UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
variable {J g : ℕ}

def prefixRecord (hJ : 0 < J) (q : Fin (J+1) → I) (start : Circle)
    (points : Fin J → ℝ) (j : Fin (J+1)) : Correction :=
  ⟨q j,start,points ⟨0,hJ⟩,boundary hJ points j⟩

def virtualPart (hJ : 0 < J) (virtual : List Component) (q : Fin (J+1) → I)
    (start : Circle) (points : Fin J → ℝ) (j : Fin J) : List Component :=
  applyCorrection (UpperCorrectionPieces.take virtual (prefixRecord hJ q start points j.succ))
    (prefixRecord hJ q start points j.castSucc)

theorem virtualPart_domain (hJ : 0 < J) (virtual : List Component) (q : Fin (J+1) → I)
    (start : Circle) (points : Fin J → ℝ) (j : Fin J) :
    domain (virtualPart hJ virtual q start points j) = part hJ (domain virtual) q start points j := by
  rw [virtualPart,applyCorrection,removeCorrection_domain,UpperCorrectionPieces.take_domain]
  unfold correctionPiece prefixRecord
  dsimp only
  have hsub := physicalPiece_subset (domain virtual) (q j.succ) start (points ⟨0,hJ⟩) (boundary hJ points j.succ)
  have hinter : physicalPiece (domain virtual) (q j.succ) start (points ⟨0,hJ⟩) (boundary hJ points j.succ) =
      physicalPiece (domain virtual) (q j.succ) start (points ⟨0,hJ⟩) (boundary hJ points j.succ) ∩ domain virtual :=
    (inter_eq_left.mpr hsub).symm
  conv_lhs => arg 2; arg 1; rw [hinter]
  rw [physicalPiece_inter]
  unfold part circularPrefix
  ext x
  simp only [mem_sdiff, mem_inter_iff]
  tauto

theorem part_inter (hJ : 0 < J) (R V : Set ℝ) (q : Fin (J+1) → I)
    (start : Circle) (points : Fin J → ℝ) (j : Fin J) :
    part hJ (R ∩ V) q start points j = R ∩ part hJ V q start points j := by
  unfold part circularPrefix
  rw [physicalPiece_inter,physicalPiece_inter]
  ext x
  simp only [mem_sdiff,mem_inter_iff]
  tauto

theorem boundary_mem (hJ : 0 < J) (points : Fin J → ℝ) (j : Fin (J+1)) :
    ∃ p, points p = boundary hJ points j := by
  unfold boundary
  split_ifs <;> exact ⟨_,rfl⟩

theorem virtualPart_recorded (hJ : 0 < J) (cuts : Fin (g+2) → ℝ)
    (virtual : List Component) (hvirtual : ∀ p, Recorded virtual p → ∃ e, cuts e = p)
    (q : Fin (J+1) → I) (start : Circle) (points : Fin J → ℝ) (j : Fin J) :
    RecordedEndpoints cuts points (virtualPart hJ virtual q start points j) := by
  have hp (p : ℝ) (hp : Recorded (virtualPart hJ virtual q start points j) p) :
      (∃ e, cuts e = p) ∨ ∃ e, points e = p := by
    rcases removeCorrection_recorded _ _ _ _ _ hp with hp | hp | hp
    · exact Or.inr ⟨⟨0,hJ⟩,hp.symm⟩
    · exact Or.inr (by simpa only [hp,prefixRecord] using boundary_mem hJ points j.castSucc)
    · rcases UpperCorrectionPieces.take_recorded _ _ hp with hp | hp | hp
      · exact Or.inr ⟨⟨0,hJ⟩,hp.symm⟩
      · exact Or.inr (by simpa only [hp,prefixRecord] using boundary_mem hJ points j.succ)
      · exact Or.inl (hvirtual p hp)
  intro c hc
  exact ⟨hp c.left ⟨c,hc,Or.inl rfl⟩,hp c.right ⟨c,hc,Or.inr rfl⟩⟩

theorem actual_part_supported {n : ℕ} (hJ : 0 < J) (policy : Policy n)
    (origin : State n) (cutter : Fin n)
    (cuts : Fin (g+2) → ℝ) (hzero : cuts 0 = 0) (hone : cuts (Fin.last (g+1)) = 1)
    (q : Fin (J+1) → I) (start : Circle) (j : Fin J) :
    ∃ virtual, RecordedEndpoints cuts (partitionRun policy origin cutter q start).1 virtual ∧
      domain (partState hJ policy origin cutter q start j).cells = domain origin.cells ∩ domain virtual := by
  refine ⟨virtualPart hJ (UpperVirtualGrid.atoms cuts) q start (partitionRun policy origin cutter q start).1 j,
    virtualPart_recorded hJ cuts _ (fun _ => UpperVirtualGrid.atoms_recorded cuts hzero hone) q start _ j,?_⟩
  rw [virtualPart_domain,UpperVirtualGrid.atoms_domain,partState_domain]
  unfold actualPart
  rw [← part_inter]
  congr 1
  exact (inter_eq_left.mpr (domain_subset_unit origin.cells)).symm


 theorem virtualPart_recorded_of_supported {Generated : Type*} (hJ : 0 < J)
    (cuts : Fin (g+2) → ℝ) (allPoints : Generated → ℝ)
    (virtual : List Component) (hvirtual : RecordedEndpoints cuts allPoints virtual)
    (q : Fin (J+1) → I) (start : Circle) (points : Fin J → ℝ)
    (hpoints : ∀ j, ∃ e, allPoints e = points j) (j : Fin J) :
    RecordedEndpoints cuts allPoints (virtualPart hJ virtual q start points j) := by
  have hb (j : Fin (J+1)) : ∃ e, allPoints e = boundary hJ points j := by
    obtain ⟨p,hp⟩ := boundary_mem hJ points j
    obtain ⟨e,he⟩ := hpoints p
    exact ⟨e,he.trans hp⟩
  have hp (p : ℝ) (hp : Recorded (virtualPart hJ virtual q start points j) p) :
      (∃ e, cuts e = p) ∨ ∃ e, allPoints e = p := by
    rcases removeCorrection_recorded _ _ _ _ _ hp with hp | hp | hp
    · exact Or.inr (by simpa only [hp,prefixRecord] using hpoints ⟨0,hJ⟩)
    · exact Or.inr (by simpa only [hp,prefixRecord] using hb j.castSucc)
    · rcases UpperCorrectionPieces.take_recorded _ _ hp with hp | hp | hp
      · exact Or.inr (by simpa only [hp,prefixRecord] using hpoints ⟨0,hJ⟩)
      · exact Or.inr (by simpa only [hp,prefixRecord] using hb j.succ)
      · obtain ⟨c,hc,hcend⟩ := hp
        rcases hcend with hcend | hcend
        · simpa only [hcend] using (hvirtual c hc).1
        · simpa only [hcend] using (hvirtual c hc).2
  intro c hc
  exact ⟨hp c.left ⟨c,hc,Or.inl rfl⟩,hp c.right ⟨c,hc,Or.inr rfl⟩⟩

end EnvyFreeResearch.Full.UpperSnapshotSmall
