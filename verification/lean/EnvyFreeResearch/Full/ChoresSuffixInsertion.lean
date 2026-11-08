import EnvyFreeResearch.Full.ChoresInitialPartition

/-! Persistent affine suffix records. The stored coordinate x represents the
physical suffix starting at 1-x, so increasing record coordinates increase
every original nonnegative suffix value. An insertion copies the complete
formal target and never changes a neighboring record. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Suffix
open Set OracleProtocol IntervalOracle QueryProgram InitialPartition Persistent
open scoped Classical

variable {n : ℕ}

def affineValue (P : Profile (Fin n)) (offset : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  P.cumulative i 1-P.cumulative i (1-x)-offset i

def AffineSound (P : Profile (Fin n)) (offset : Fin n → ℝ) (r : Record n) : Prop :=
  ∀ i, (r.formal i).1 = affineValue P offset i r.point

theorem affineValue_monotone (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    (offset : Fin n → ℝ) (i : Fin n) : Monotone (affineValue P offset i) := by
  intro x y hxy
  have h := hmono i (show 1-y ≤ 1-x by linarith)
  unfold affineValue
  linarith

def fromSuffixEndpoint (left right : Record n) (i : Fin n) (target : ℝ × ℚ)
    (endpoint : EndpointRecord n) : Record n :=
  makeRecord left right i target (1-endpoint.point)
    (fun j => (right.formal j).1-endpoint.value j)

/-- Both primary-tie branches reuse a physical endpoint. The strict-primary
branch is a single ordinary endpoint-recording operation. The offset need
not be known to the program: it cancels in the cached cost difference. -/
def affineInsertProgram (left right : Record n) (i : Fin n) (target : ℝ × ℚ) :
    Program (Query (Fin n)) ℝ (Record n) :=
  if target.1 = (left.formal i).1 then
    .returned (makeRecord left right i target left.point (fun j => (left.formal j).1))
  else if target.1 = (right.formal i).1 then
    .returned (makeRecord left right i target right.point (fun j => (right.formal j).1))
  else (endpointProgram i (1-right.point) (1-left.point) ((right.formal i).1-target.1)).bind
    (fun endpoint => .returned (fromSuffixEndpoint left right i target endpoint))

/-- Actual affine insertion with arbitrary enclosing history and all legal
root choices. No strict positivity of the original costs is required. A
restricted-domain caller compiles its entire protocol once to the original
oracle using the ordered-union translator. -/
theorem affine_insert_correct (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (offset : Fin n → ℝ) (left right : Record n) (i : Fin n) (target : ℝ × ℚ)
    (hleft : AffineSound P offset left) (hright : AffineSound P offset right)
    (hbefore : Before left right) (hl0 : 0 ≤ left.point) (hr1 : right.point ≤ 1)
    (hlt : recordLT (left.formal i) target) (hrt : recordLT target (right.formal i))
    (prior : History (Query (Fin n)) ℝ) :
    ∃ fresh : Record n, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (affineInsertProgram left right i target) prior fresh trace ∧
      trace.length ≤ n ∧ trace.countP (fun qr => isCutQuery qr.1) ≤ 1 ∧
      AffineSound P offset fresh ∧ Before left fresh ∧ Before fresh right ∧ fresh.formal i = target := by
  have hprim : ∀ j, (left.formal j).1 ≤ (right.formal j).1 :=
    fun j => recordLT_primary_le (hbefore.2 j)
  by_cases hl : target.1 = (left.formal i).1
  · let fresh := makeRecord left right i target left.point (fun j => (left.formal j).1)
    have hs := makeRecord_spec left right i target left.point (fun j => (left.formal j).1)
      hbefore ⟨le_rfl,hbefore.1⟩ (fun j => ⟨le_rfl,hprim j⟩) hl.symm hlt hrt
    refine ⟨fresh,[],?_,Nat.zero_le _,by simp,?_,hs.1,hs.2⟩
    · simpa only [affineInsertProgram,ite_eq_left hl] using
        (Executes.returned (oracle := oracle) fresh prior)
    · exact hleft
  · by_cases hr : target.1 = (right.formal i).1
    · let fresh := makeRecord left right i target right.point (fun j => (right.formal j).1)
      have hs := makeRecord_spec left right i target right.point (fun j => (right.formal j).1)
        hbefore ⟨hbefore.1,le_rfl⟩ (fun j => ⟨hprim j,le_rfl⟩) hr.symm hlt hrt
      refine ⟨fresh,[],?_,Nat.zero_le _,by simp,?_,hs.1,hs.2⟩
      · simpa only [affineInsertProgram,ite_eq_right hl,ite_eq_left hr] using
          (Executes.returned (oracle := oracle) fresh prior)
      · exact hright
    · have hbound : 0 ≤ 1-right.point ∧ 1-right.point ≤ 1-left.point ∧ 1-left.point ≤ 1 := by
        constructor
        · linarith
        constructor
        · linarith [hbefore.1]
        · linarith
      have htotal : 0 ≤ P.cumulative i (1-left.point)-P.cumulative i (1-right.point) :=
        sub_nonneg.mpr (hmono i hbound.2.1)
      have htarget0 : 0 ≤ (right.formal i).1-target.1 := sub_nonneg.mpr (recordLT_primary_le hrt)
      have htarget1 : (right.formal i).1-target.1 ≤
          P.cumulative i (1-left.point)-P.cumulative i (1-right.point) := by
        have ht := recordLT_primary_le hlt
        have hL := hleft i
        have hR := hright i
        unfold affineValue at hL hR
        linarith
      have hlegal : Legal P (.cut i (1-right.point) (1-left.point) ((right.formal i).1-target.1)) := by
        refine ⟨hbound.1,hbound.2.1,hbound.2.2,?_⟩
        change min 0 _ ≤ _ ∧ _ ≤ max 0 _
        rw [min_eq_left htotal,max_eq_right htotal]
        exact ⟨htarget0,htarget1⟩
      obtain ⟨endpoint,trace,hexec,hlen,hcuts,hpoint,hvalues,htarget⟩ :=
        endpoint_program_correct P oracle hpolicy i (1-right.point) (1-left.point)
          ((right.formal i).1-target.1) hlegal prior
      have hnewpoint : 1-endpoint.point ∈ Icc left.point right.point := by
        constructor <;> linarith [hpoint.1,hpoint.2]
      have hprimary : ∀ j, (right.formal j).1-endpoint.value j =
          affineValue P offset j (1-endpoint.point) := by
        intro j
        rw [hright j,hvalues j]
        unfold affineValue
        rw [show (1 : ℝ)-(1-endpoint.point) = endpoint.point by ring]
        ring
      have hbetween : ∀ j, (left.formal j).1 ≤ (right.formal j).1-endpoint.value j ∧
          (right.formal j).1-endpoint.value j ≤ (right.formal j).1 := by
        intro j
        rw [hprimary j,hleft j,hright j]
        exact ⟨affineValue_monotone P hmono offset j hnewpoint.1,
          affineValue_monotone P hmono offset j hnewpoint.2⟩
      have hcopy : (right.formal i).1-endpoint.value i = target.1 := by rw [htarget]; ring
      have hs := makeRecord_spec left right i target (1-endpoint.point)
        (fun j => (right.formal j).1-endpoint.value j) hbefore hnewpoint hbetween hcopy hlt hrt
      let fresh := fromSuffixEndpoint left right i target endpoint
      refine ⟨fresh,trace,?_,hlen.le,hcuts.le,hprimary,hs.1,hs.2⟩
      simpa only [affineInsertProgram,ite_eq_right hl,ite_eq_right hr,List.append_nil] using
        hexec.bind (fun endpoint => Program.returned (fromSuffixEndpoint left right i target endpoint))
          (Executes.returned fresh (prior++trace))

end EnvyFreeResearch.Full.Chores.Suffix
