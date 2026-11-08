import EnvyFreeResearch.Full.ChoresComponentBoundaryRecord

/-! Query endpoints are drawn from inherited boundaries or earlier physical
Cut replies. This is a trace property, with no valuation or fairness premise. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Persistent
open scoped Classical

variable {n : ℕ}

def BoundsIn (points : Set ℝ) : Query (Fin n) → Prop
  | .eval _ a b => a ∈ points ∧ b ∈ points
  | .cut _ a b _ => a ∈ points ∧ b ∈ points

def Scoped (points : Set ℝ) : History (Query (Fin n)) ℝ → Prop
  | [] => True
  | (q, r) :: rest => BoundsIn points q ∧ Scoped (Known points [(q, r)]) rest

@[simp] theorem known_eval (points : Set ℝ) (i : Fin n) (a b r : ℝ) :
    Known points [(.eval i a b, r)] = points := by
  ext x
  simp [Known, cutReplies]

theorem known_set_mono {old more : Set ℝ} (h : old ⊆ more)
    (trace : History (Query (Fin n)) ℝ) : Known old trace ⊆ Known more trace := by
  intro x hx
  exact hx.elim (fun hx => Or.inl (h hx)) Or.inr

theorem Scoped.mono {old more : Set ℝ} (h : old ⊆ more)
    {trace : History (Query (Fin n)) ℝ} (ht : Scoped old trace) : Scoped more trace := by
  induction trace generalizing old more with
  | nil => trivial
  | cons qr rest ih =>
    refine ⟨?_, ih (known_set_mono h [qr]) ht.2⟩
    rcases qr with ⟨q, r⟩
    cases q <;> exact ⟨h ht.1.1, h ht.1.2⟩

theorem scoped_append (old : Set ℝ) (first second : History (Query (Fin n)) ℝ) :
    Scoped old (first ++ second) ↔ Scoped old first ∧ Scoped (Known old first) second := by
  induction first generalizing old with
  | nil => simp [Scoped]
  | cons qr rest ih =>
    change (BoundsIn old qr.1 ∧ Scoped (Known old [qr]) (rest ++ second)) ↔ _
    rw [ih]
    change _ ↔ (BoundsIn old qr.1 ∧ Scoped (Known old [qr]) rest) ∧
      Scoped (Known old ([qr] ++ rest)) second
    rw [known_append]
    tauto

theorem endpoint_tail_scoped
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (c : Fin n) (a b t x : ℝ) (ha : a ∈ points) (hx : x ∈ points)
    (done : History (Query (Fin n)) ℝ) (fuel : ℕ) (prior : History (Query (Fin n)) ℝ)
    (out : EndpointRecord n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (ofProtocol (endpointProtocol c a b t) fuel
      ((.cut c a b t, x) :: done)) prior out trace) : Scoped points trace := by
  induction fuel generalizing done prior trace with
  | zero =>
    cases hd : (recordingObservers c).drop done.length with
    | nil =>
      have hn : endpointProtocol c a b t () ((.cut c a b t, x) :: done) =
          .returned (completedRecord c t x done) := by simp [endpointProtocol, hd]
      rw [ofProtocol, hn] at h
      cases h
      trivial
    | cons j rest =>
      have hn : endpointProtocol c a b t () ((.cut c a b t, x) :: done) =
          .ask (.eval j a x) := by simp [endpointProtocol, hd]
      rw [ofProtocol, hn] at h
      cases h
  | succ fuel ih =>
    cases hd : (recordingObservers c).drop done.length with
    | nil =>
      have hn : endpointProtocol c a b t () ((.cut c a b t, x) :: done) =
          .returned (completedRecord c t x done) := by simp [endpointProtocol, hd]
      rw [ofProtocol, hn] at h
      cases h
      trivial
    | cons j rest =>
      have hn : endpointProtocol c a b t () ((.cut c a b t, x) :: done) =
          .ask (.eval j a x) := by simp [endpointProtocol, hd]
      rw [ofProtocol, hn] at h
      cases h with
      | ask q next prior reply out tail hreply hnext =>
        refine ⟨⟨ha, hx⟩, ?_⟩
        rw [known_eval]
        apply ih (done ++ [(Query.eval j a x, reply)]) (prior ++ [(Query.eval j a x, reply)]) tail
        simpa only [List.cons_append] using hnext

theorem endpoint_scoped
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (c : Fin n) (a b t : ℝ) (ha : a ∈ points) (hb : b ∈ points)
    (prior : History (Query (Fin n)) ℝ) (out : EndpointRecord n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (endpointProgram c a b t) prior out trace) : Scoped points trace := by
  cases n with
  | zero => exact Fin.elim0 c
  | succ n =>
    change Executes oracle (.ask (.cut c a b t) (fun reply =>
      ofProtocol (endpointProtocol c a b t) n [(.cut c a b t, reply)])) prior out trace at h
    cases h with
    | ask q next prior reply out tail hreply hnext =>
      refine ⟨⟨ha, hb⟩, ?_⟩
      exact endpoint_tail_scoped oracle (Known points [(.cut c a b t, reply)]) c a b t reply
        (Or.inl ha) (Or.inr (by simp [cutReplies])) [] n _ out tail hnext

theorem insertion_scoped
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (left right : Record n) (hl : left.point ∈ points) (hr : right.point ∈ points)
    (i : Fin n) (target : ℝ × ℚ) (prior : History (Query (Fin n)) ℝ) (out : Record n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (ofProtocol (insertionProtocol left right i target) n []) prior out trace) :
    Scoped points trace := by
  by_cases heql : target.1 = (left.formal i).1
  · simp only [insertionProtocol, ite_eq_left heql, ofProtocol] at h
    cases h
    trivial
  · by_cases heqr : target.1 = (right.formal i).1
    · simp only [insertionProtocol, ite_eq_right heql, ite_eq_left heqr, ofProtocol] at h
      cases h
      trivial
    · simp only [insertionProtocol, ite_eq_right heql, ite_eq_right heqr, ofProtocol_map] at h
      obtain ⟨e, first, second, he, hsecond, htrace⟩ := Executes.split_bind _ _ h
      cases hsecond
      simp only [List.append_nil] at htrace
      subst trace
      exact endpoint_scoped oracle points i left.point right.point _ hl hr prior e first he

theorem ensure_scoped
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (points : Set ℝ) (records : List (Record n)) (hold : ∀ r ∈ records, r.point ∈ points)
    (i : Fin n) (target : ℝ × ℚ) (prior : History (Query (Fin n)) ℝ) (out : EnsureResult n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (ofProtocol (ensureProtocol records i target) n []) prior out trace) :
    Scoped points trace := by
  have hlocvalid := locate_valid i target records
  cases hloc : locate i target records with
  | failed =>
    simp only [ensureProtocol, hloc, ofProtocol] at h
    cases h
  | reused r =>
    simp only [ensureProtocol, hloc, ofProtocol] at h
    cases h
    trivial
  | bracket pre left right post =>
    rw [hloc] at hlocvalid
    have hdecomp : records = pre ++ left :: right :: post := hlocvalid.1
    simp only [ensureProtocol, hloc, ofProtocol_map] at h
    obtain ⟨fresh, first, second, hfresh, hsecond, htrace⟩ := Executes.split_bind _ _ h
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    exact insertion_scoped oracle points left right (hold left (by simp [hdecomp]))
      (hold right (by simp [hdecomp])) i target prior fresh first hfresh

end EnvyFreeResearch.Full.Chores.Boundary
