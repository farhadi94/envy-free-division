import EnvyFreeResearch.Full.ChoresSuffixInsertion

/-! Clipped suffix insertion retains both the original affine value and the
clipped formal row. Negative affine values cannot be reconstructed from a
zero clipped value, so they are explicitly kept in the immutable record. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Suffix
open Set OracleProtocol IntervalOracle QueryProgram InitialPartition Persistent
open scoped Classical

variable {n : ℕ}

structure ClippedRecord (n : ℕ) where
  record : Record n
  raw : Fin n → ℝ

def ClippedSound (P : Profile (Fin n)) (offset : Fin n → ℝ) (r : ClippedRecord n) : Prop :=
  (∀ i, r.raw i = affineValue P offset i r.record.point) ∧
  ∀ i, (r.record.formal i).1 = max 0 (r.raw i)

def clippedValue (P : Profile (Fin n)) (offset : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  max 0 (affineValue P offset i x)

theorem clippedValue_monotone (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    (offset : Fin n → ℝ) (i : Fin n) : Monotone (clippedValue P offset i) :=
  fun _ _ h => max_le_max le_rfl (affineValue_monotone P hmono offset i h)

theorem ClippedSound.value {P : Profile (Fin n)} {offset : Fin n → ℝ} {r : ClippedRecord n}
    (h : ClippedSound P offset r) (i : Fin n) :
    (r.record.formal i).1 = clippedValue P offset i r.record.point := by
  rw [h.2 i,h.1 i]
  rfl

def makeClippedRecord (left right : ClippedRecord n) (i : Fin n) (target : ℝ × ℚ)
    (point : ℝ) (raw : Fin n → ℝ) : ClippedRecord n :=
  ⟨makeRecord left.record right.record i target point (fun j => max 0 (raw j)),raw⟩

theorem make_clipped_sound (P : Profile (Fin n)) (offset : Fin n → ℝ)
    (left right : ClippedRecord n) (i : Fin n) (target : ℝ × ℚ) (point : ℝ) (raw : Fin n → ℝ)
    (hraw : ∀ j, raw j = affineValue P offset j point) :
    ClippedSound P offset (makeClippedRecord left right i target point raw) :=
  ⟨hraw,fun _ => rfl⟩

def clippedFromEndpoint (left right : ClippedRecord n) (i : Fin n) (target : ℝ × ℚ)
    (endpoint : EndpointRecord n) : ClippedRecord n :=
  makeClippedRecord left right i target (1-endpoint.point) (fun j => right.raw j-endpoint.value j)

def clippedInsertProgram (left right : ClippedRecord n) (i : Fin n) (target : ℝ × ℚ) :
    Program (Query (Fin n)) ℝ (ClippedRecord n) :=
  if target.1 = (left.record.formal i).1 then
    .returned (makeClippedRecord left right i target left.record.point left.raw)
  else if target.1 = (right.record.formal i).1 then
    .returned (makeClippedRecord left right i target right.record.point right.raw)
  else (endpointProgram i (1-right.record.point) (1-left.record.point) (right.raw i-target.1)).bind
    (fun endpoint => .returned (clippedFromEndpoint left right i target endpoint))

theorem clipped_insert_correct (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (offset : Fin n → ℝ) (left right : ClippedRecord n) (i : Fin n) (target : ℝ × ℚ)
    (hleft : ClippedSound P offset left) (hright : ClippedSound P offset right)
    (hbefore : Before left.record right.record)
    (hl0 : 0 ≤ left.record.point) (hr1 : right.record.point ≤ 1)
    (hlt : recordLT (left.record.formal i) target) (hrt : recordLT target (right.record.formal i))
    (prior : History (Query (Fin n)) ℝ) :
    ∃ fresh : ClippedRecord n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (clippedInsertProgram left right i target) prior fresh trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      ClippedSound P offset fresh ∧ Before left.record fresh.record ∧
      Before fresh.record right.record ∧ fresh.record.formal i = target := by
  have hprim : ∀ j, (left.record.formal j).1 ≤ (right.record.formal j).1 :=
    fun j => recordLT_primary_le (hbefore.2 j)
  have ht0 : 0 ≤ target.1 := by
    have h := recordLT_primary_le hlt
    rw [hleft.2 i] at h
    exact (le_max_left _ _).trans h
  by_cases hl : target.1 = (left.record.formal i).1
  · let fresh := makeClippedRecord left right i target left.record.point left.raw
    have hs := makeRecord_spec left.record right.record i target left.record.point
      (fun j => max 0 (left.raw j)) hbefore ⟨le_rfl,hbefore.1⟩
      (fun j => by rw [← hleft.2 j]; exact ⟨le_rfl,hprim j⟩)
      ((hleft.2 i).symm.trans hl.symm) hlt hrt
    refine ⟨fresh,[],?_,Nat.zero_le _,by simp,
      make_clipped_sound P offset left right i target _ _ hleft.1,hs.1,hs.2⟩
    simpa only [clippedInsertProgram,ite_eq_left hl] using
      (Executes.returned (oracle := oracle) fresh prior)
  · by_cases hr : target.1 = (right.record.formal i).1
    · let fresh := makeClippedRecord left right i target right.record.point right.raw
      have hs := makeRecord_spec left.record right.record i target right.record.point
        (fun j => max 0 (right.raw j)) hbefore ⟨hbefore.1,le_rfl⟩
        (fun j => by rw [← hright.2 j]; exact ⟨hprim j,le_rfl⟩)
        ((hright.2 i).symm.trans hr.symm) hlt hrt
      refine ⟨fresh,[],?_,Nat.zero_le _,by simp,
        make_clipped_sound P offset left right i target _ _ hright.1,hs.1,hs.2⟩
      simpa only [clippedInsertProgram,ite_eq_right hl,ite_eq_left hr] using
        (Executes.returned (oracle := oracle) fresh prior)
    · have hrightpos : 0 < max 0 (right.raw i) := by
        rw [← hright.2 i]
        exact lt_of_le_of_lt ht0 (lt_of_le_of_ne (recordLT_primary_le hrt) hr)
      have hrawpos : 0 < right.raw i := (lt_max_iff.mp hrightpos).resolve_left (lt_irrefl 0)
      have hrightEq : (right.record.formal i).1 = right.raw i :=
        (hright.2 i).trans (max_eq_right hrawpos.le)
      have hleftle : left.raw i ≤ target.1 := by
        have h := recordLT_primary_le hlt
        rw [hleft.2 i] at h
        exact (le_max_right _ _).trans h
      have hbound : 0 ≤ 1-right.record.point ∧ 1-right.record.point ≤ 1-left.record.point ∧
          1-left.record.point ≤ 1 := by
        constructor
        · linarith
        constructor
        · linarith [hbefore.1]
        · linarith
      have htotal : 0 ≤ P.cumulative i (1-left.record.point)-P.cumulative i (1-right.record.point) :=
        sub_nonneg.mpr (hmono i hbound.2.1)
      have htarget0 : 0 ≤ right.raw i-target.1 := by
        rw [← hrightEq]
        exact sub_nonneg.mpr (recordLT_primary_le hrt)
      have htarget1 : right.raw i-target.1 ≤
          P.cumulative i (1-left.record.point)-P.cumulative i (1-right.record.point) := by
        have hL := hleft.1 i
        have hR := hright.1 i
        unfold affineValue at hL hR
        linarith
      have hlegal : Legal P (.cut i (1-right.record.point) (1-left.record.point) (right.raw i-target.1)) := by
        refine ⟨hbound.1,hbound.2.1,hbound.2.2,?_⟩
        change min 0 _ ≤ _ ∧ _ ≤ max 0 _
        rw [min_eq_left htotal,max_eq_right htotal]
        exact ⟨htarget0,htarget1⟩
      obtain ⟨endpoint,trace,hexec,hlen,hcuts,hpoint,hvalues,htarget⟩ :=
        endpoint_program_correct P oracle hpolicy i (1-right.record.point) (1-left.record.point)
          (right.raw i-target.1) hlegal prior
      have hnewpoint : 1-endpoint.point ∈ Icc left.record.point right.record.point := by
        constructor <;> linarith [hpoint.1,hpoint.2]
      have hraw : ∀ j, right.raw j-endpoint.value j = affineValue P offset j (1-endpoint.point) := by
        intro j
        rw [hright.1 j,hvalues j]
        unfold affineValue
        rw [show (1 : ℝ)-(1-endpoint.point) = endpoint.point by ring]
        ring
      have hbetween : ∀ j, (left.record.formal j).1 ≤ max 0 (right.raw j-endpoint.value j) ∧
          max 0 (right.raw j-endpoint.value j) ≤ (right.record.formal j).1 := by
        intro j
        rw [hraw j,hleft.value j,hright.value j]
        exact ⟨clippedValue_monotone P hmono offset j hnewpoint.1,
          clippedValue_monotone P hmono offset j hnewpoint.2⟩
      have hcopy : max 0 (right.raw i-endpoint.value i) = target.1 := by
        rw [htarget,show right.raw i-(right.raw i-target.1) = target.1 by ring,max_eq_right ht0]
      have hs := makeRecord_spec left.record right.record i target (1-endpoint.point)
        (fun j => max 0 (right.raw j-endpoint.value j)) hbefore hnewpoint hbetween hcopy hlt hrt
      let fresh := clippedFromEndpoint left right i target endpoint
      refine ⟨fresh,trace,?_,hlen.le,hcuts.le,
        make_clipped_sound P offset left right i target _ _ hraw,hs.1,hs.2⟩
      simpa only [clippedInsertProgram,ite_eq_right hl,ite_eq_right hr,List.append_nil] using
        hexec.bind (fun endpoint => Program.returned (clippedFromEndpoint left right i target endpoint))
          (Executes.returned fresh (prior++trace))

end EnvyFreeResearch.Full.Chores.Suffix
