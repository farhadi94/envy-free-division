import EnvyFreeResearch.Full.ChoresUnionOracle

/-! Cached evaluation on a finite union whose components have been refined
at all recorded query endpoints. No interval Eval is needed for a cached
window: its value is the sum of its contained component records. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set MeasureTheory IntervalOracle InitialPartition

variable {n : ℕ}

theorem mem_material_iff (ps : List (Parent n)) (x : ℝ) :
    x ∈ material ps ↔ ∃ p ∈ ps, x ∈ Ioc p.left p.right := by
  induction ps with
  | nil => simp [material]
  | cons p ps ih => simp [material,ih]

theorem valid_iff_forall (P : Profile (Fin n)) (ps : List (Parent n)) :
    Valid P ps ↔ ∀ p ∈ ps, ValidPart P p := by
  induction ps with
  | nil => simp [Valid]
  | cons p ps ih => simp [Valid,ih]

theorem valid_filter (P : Profile (Fin n)) {ps : List (Parent n)} (h : Valid P ps)
    (keep : Parent n → Bool) : Valid P (ps.filter keep) := by
  apply (valid_iff_forall _ _).mpr
  intro p hp
  exact (valid_iff_forall _ _).mp h p (List.mem_filter.mp hp).1

def Aligned (ps : List (Parent n)) (x : ℝ) : Prop :=
  ∀ p ∈ ps, p.right ≤ x ∨ x ≤ p.left

def window (a b : ℝ) (ps : List (Parent n)) : List (Parent n) :=
  ps.filter (fun p => decide (a ≤ p.left ∧ p.right ≤ b))

theorem mem_window {a b : ℝ} {ps : List (Parent n)} {p : Parent n} :
    p ∈ window a b ps ↔ p ∈ ps ∧ a ≤ p.left ∧ p.right ≤ b := by
  simp [window]

theorem window_ordered {a b : ℝ} {ps : List (Parent n)} (h : Ordered ps) :
    Ordered (window a b ps) := h.filter _

theorem window_valid (P : Profile (Fin n)) {a b : ℝ} {ps : List (Parent n)}
    (h : Valid P ps) : Valid P (window a b ps) := valid_filter P h _

theorem window_within (P : Profile (Fin n)) {a b : ℝ} {ps : List (Parent n)}
    (h : Valid P ps) : Within a b (window a b ps) := by
  intro p hp
  obtain ⟨hp,ha,hb⟩ := mem_window.mp hp
  exact ⟨ha,((valid_iff_forall _ _).mp h p hp).1.2.1,hb⟩

theorem window_material {a b : ℝ} {ps : List (Parent n)}
    (ha : Aligned ps a) (hb : Aligned ps b) :
    material (window a b ps) = material ps ∩ Ioc a b := by
  ext x
  constructor
  · intro hx
    obtain ⟨p,hp,hpx⟩ := (mem_material_iff _ _).mp hx
    obtain ⟨hp,hal,hbr⟩ := mem_window.mp hp
    exact ⟨(mem_material_iff _ _).mpr ⟨p,hp,hpx⟩,hal.trans_lt hpx.1,hpx.2.trans hbr⟩
  · rintro ⟨hx,hax,hxb⟩
    obtain ⟨p,hp,hpx⟩ := (mem_material_iff _ _).mp hx
    have hal : a ≤ p.left := (ha p hp).resolve_left (fun hpa =>
      (not_le_of_gt hax) (hpx.2.trans hpa))
    have hbr : p.right ≤ b := (hb p hp).resolve_right (fun hbp =>
      (not_le_of_gt hpx.1) (hxb.trans hbp))
    exact (mem_material_iff _ _).mpr ⟨p,mem_window.mpr ⟨hp,hal,hbr⟩,hpx⟩

/-- Every Eval of the restricted CDF between two recorded boundaries is a
pure cache sum. The component count has no effect on its oracle cost. -/
theorem cached_window_eval {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (ps : List (Parent n)) (hp : Valid (measureProfile cost) ps) (ho : Ordered ps)
    (U : Set ℝ) (hU : material ps = U) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (ha : Aligned ps a) (hb : Aligned ps b) (i : Fin n) :
    cachedValue (window a b ps) i =
      (restrictedProfile cost U).cumulative i b-(restrictedProfile cost U).cumulative i a := by
  symm
  apply cached_restricted_interval cost U ha0 hab _ (window_valid _ hp) (window_ordered ho)
  rw [window_material ha hb,hU]

/-- Any refinement inside old components preserves every old recorded
boundary. This statement uses physical containment only. -/
theorem aligned_of_refinement {old fresh : List (Parent n)} {x : ℝ}
    (hx : Aligned old x)
    (hcontained : ∀ q ∈ fresh, ∃ p ∈ old, p.left ≤ q.left ∧ q.right ≤ p.right) :
    Aligned fresh x := by
  intro q hq
  obtain ⟨p,hp,hl,hr⟩ := hcontained q hq
  rcases hx p hp with h | h
  · exact Or.inl (hr.trans h)
  · exact Or.inr (h.trans hl)

end EnvyFreeResearch.Full.Chores.OrderedUnion
