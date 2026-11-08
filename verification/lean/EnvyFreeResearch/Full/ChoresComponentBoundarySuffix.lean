import EnvyFreeResearch.Full.ChoresComponentBoundaryScope
import EnvyFreeResearch.Full.ChoresSubCoreLeavesAffine

/-! Coordinate provenance of the actual suffix recorders. A stored suffix
coordinate x represents the physical boundary 1-x. Both plateau branches
reuse a stored boundary; strict insertion uses a literal physical Cut reply.
The separate virtual bottom has coordinate zero, so it introduces only the
already inherited right endpoint 1. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram Persistent Suffix
open scoped Classical

variable {n : ℕ}

theorem affine_insert_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (left right : Record n)
    (hl : 1-left.point ∈ points) (hr : 1-right.point ∈ points)
    (i : Fin n) (target : ℝ × ℚ) (prior : History (Query (Fin n)) ℝ)
    (out : Record n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (affineInsertProgram left right i target) prior out trace) :
    1-out.point ∈ Known points trace ∧ Scoped points trace := by
  by_cases heql : target.1 = (left.formal i).1
  · simp only [affineInsertProgram, ite_eq_left heql] at h
    cases h
    exact ⟨by simpa only [makeRecord, known_nil] using hl, trivial⟩
  · by_cases heqr : target.1 = (right.formal i).1
    · simp only [affineInsertProgram, ite_eq_right heql, ite_eq_left heqr] at h
      cases h
      exact ⟨by simpa only [makeRecord, known_nil] using hr, trivial⟩
    · simp only [affineInsertProgram, ite_eq_right heql, ite_eq_right heqr] at h
      obtain ⟨e, first, second, he, hsecond, htrace⟩ := Executes.split_bind _ _ h
      cases hsecond
      simp only [List.append_nil] at htrace
      subst trace
      refine ⟨?_, endpoint_scoped oracle points i _ _ _ hr hl prior e first he⟩
      have hp := endpoint_from_trace oracle i (1-right.point) (1-left.point) _ prior e first he
      change 1-(1-e.point) ∈ Known points first
      rw [sub_sub_cancel]
      exact Or.inr hp

theorem clipped_insert_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (left right : ClippedRecord n)
    (hl : 1-left.record.point ∈ points) (hr : 1-right.record.point ∈ points)
    (i : Fin n) (target : ℝ × ℚ) (prior : History (Query (Fin n)) ℝ)
    (out : ClippedRecord n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (clippedInsertProgram left right i target) prior out trace) :
    1-out.record.point ∈ Known points trace ∧ Scoped points trace := by
  by_cases heql : target.1 = (left.record.formal i).1
  · simp only [clippedInsertProgram, ite_eq_left heql] at h
    cases h
    exact ⟨by simpa only [makeClippedRecord, makeRecord, known_nil] using hl, trivial⟩
  · by_cases heqr : target.1 = (right.record.formal i).1
    · simp only [clippedInsertProgram, ite_eq_right heql, ite_eq_left heqr] at h
      cases h
      exact ⟨by simpa only [makeClippedRecord, makeRecord, known_nil] using hr, trivial⟩
    · simp only [clippedInsertProgram, ite_eq_right heql, ite_eq_right heqr] at h
      obtain ⟨e, first, second, he, hsecond, htrace⟩ := Executes.split_bind _ _ h
      cases hsecond
      simp only [List.append_nil] at htrace
      subst trace
      refine ⟨?_, endpoint_scoped oracle points i _ _ _ hr hl prior e first he⟩
      have hp := endpoint_from_trace oracle i (1-right.record.point) (1-left.record.point) _ prior e first he
      change 1-(1-e.point) ∈ Known points first
      rw [sub_sub_cancel]
      exact Or.inr hp

theorem affine_ensure_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (records : List (Record n))
    (hold : ∀ r ∈ records, 1-r.point ∈ points) (i : Fin n) (target : ℝ × ℚ)
    (prior : History (Query (Fin n)) ℝ) (out : EnsureResult n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (affineEnsureProgram records i target) prior out trace) :
    (∀ r ∈ out.records, 1-r.point ∈ Known points trace) ∧
      1-out.selected.point ∈ Known points trace ∧ Scoped points trace := by
  have hvalid := Persistent.locate_valid i target records
  cases hloc : Persistent.locate i target records with
  | failed => simp only [affineEnsureProgram, hloc] at h; cases h
  | reused r =>
    simp only [affineEnsureProgram, hloc] at h
    cases h
    rw [hloc] at hvalid
    simpa only [known_nil] using And.intro hold ⟨hold r hvalid.1, trivial⟩
  | bracket pre left right post =>
    rw [hloc] at hvalid
    have hdecomp := hvalid.1
    simp only [affineEnsureProgram, hloc] at h
    obtain ⟨fresh, first, second, hfresh, hsecond, htrace⟩ := Executes.split_bind _ _ h
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    have hnew := affine_insert_known oracle points left right
      (hold left (by simp [hdecomp])) (hold right (by simp [hdecomp])) i target prior fresh first hfresh
    refine ⟨?_, hnew⟩
    intro r hr
    simp only [List.mem_append, List.mem_cons] at hr
    rcases hr with hr | rfl | rfl | rfl | hr
    · exact Or.inl (hold r (by simp [hdecomp, hr]))
    · exact Or.inl (hold r (by simp [hdecomp]))
    · exact hnew.1
    · exact Or.inl (hold r (by simp [hdecomp]))
    · exact Or.inl (hold r (by simp [hdecomp, hr]))

theorem lookup_ensure_known {Payload : Type*} (view : Payload → Record n)
    (insert : Payload → Payload → Fin n → ℝ × ℚ → Program (Query (Fin n)) ℝ Payload)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hinsert : ∀ points left right, 1-(view left).point ∈ points → 1-(view right).point ∈ points →
      ∀ i target prior out trace, Executes oracle (insert left right i target) prior out trace →
        1-(view out).point ∈ Known points trace ∧ Scoped points trace)
    (points : Set ℝ) (records : List Payload)
    (hold : ∀ r ∈ records, 1-(view r).point ∈ points) (i : Fin n) (target : ℝ × ℚ)
    (prior : History (Query (Fin n)) ℝ) (out : Lookup.Result Payload)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Lookup.ensureProgram view insert records i target) prior out trace) :
    (∀ r ∈ out.records, 1-(view r).point ∈ Known points trace) ∧
      1-(view out.selected).point ∈ Known points trace ∧ Scoped points trace := by
  have hvalid := Lookup.locate_valid view i target records
  cases hloc : Lookup.locate view i target records with
  | failed => simp only [Lookup.ensureProgram, hloc] at h; cases h
  | reused r =>
    simp only [Lookup.ensureProgram, hloc] at h
    cases h
    rw [hloc] at hvalid
    simpa only [known_nil] using And.intro hold ⟨hold r hvalid.1, trivial⟩
  | bracket pre left right post =>
    rw [hloc] at hvalid
    have hdecomp := hvalid.1
    simp only [Lookup.ensureProgram, hloc] at h
    obtain ⟨fresh, first, second, hfresh, hsecond, htrace⟩ := Executes.split_bind _ _ h
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    have hnew := hinsert points left right
      (hold left (by simp [hdecomp])) (hold right (by simp [hdecomp])) i target prior fresh first hfresh
    refine ⟨?_, hnew⟩
    intro r hr
    simp only [List.mem_append, List.mem_cons] at hr
    rcases hr with hr | rfl | rfl | rfl | hr
    · exact Or.inl (hold r (by simp [hdecomp, hr]))
    · exact Or.inl (hold r (by simp [hdecomp]))
    · exact hnew.1
    · exact Or.inl (hold r (by simp [hdecomp]))
    · exact Or.inl (hold r (by simp [hdecomp, hr]))

theorem clipped_ensure_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (records : List (ClippedRecord n))
    (hold : ∀ r ∈ records, 1-r.record.point ∈ points) (i : Fin n) (target : ℝ × ℚ)
    (prior : History (Query (Fin n)) ℝ) (out : Lookup.Result (ClippedRecord n))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (clippedEnsureProgram records i target) prior out trace) :
    (∀ r ∈ out.records, 1-r.record.point ∈ Known points trace) ∧
      1-out.selected.record.point ∈ Known points trace ∧ Scoped points trace :=
  lookup_ensure_known ClippedRecord.record clippedInsertProgram oracle
    (clipped_insert_known oracle) points records hold i target prior out trace h

theorem affine_virtual_known (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (bottom : Record n) (hbottom : 1-bottom.point ∈ points)
    (records : List (Record n)) (hold : ∀ r ∈ records, 1-r.point ∈ points)
    (i : Fin n) (target : ℝ × ℚ) (prior : History (Query (Fin n)) ℝ) (out : EnsureResult n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (affineVirtualEnsureProgram bottom records i target) prior out trace) :
    (∀ r ∈ out.records, 1-r.point ∈ Known points trace) ∧
      1-out.selected.point ∈ Known points trace ∧ Scoped points trace := by
  cases records with
  | nil => simp only [affineVirtualEnsureProgram] at h; cases h
  | cons first rest =>
    by_cases hbelow : recordLT target (first.formal i)
    · simp only [affineVirtualEnsureProgram, ite_eq_left hbelow] at h
      obtain ⟨fresh, t₁, t₂, hf, ht₂, ht⟩ := Executes.split_bind _ _ h
      cases ht₂
      simp only [List.append_nil] at ht
      subst trace
      have hnew := affine_insert_known oracle points bottom first hbottom
        (hold first List.mem_cons_self) i target prior fresh t₁ hf
      refine ⟨?_, hnew⟩
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hnew.1
      · exact Or.inl (hold r hr)
    · simp only [affineVirtualEnsureProgram, ite_eq_right hbelow] at h
      exact affine_ensure_known oracle points (first::rest) hold i target prior out trace h

end EnvyFreeResearch.Full.Chores.Boundary
