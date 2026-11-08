import EnvyFreeResearch.Full.UpperDomainDifferenceRefine

/-!
# Exact recorded-domain subtraction

Refine at actual circular-piece endpoints, then select whole refined atoms
by endpoint comparisons. Literal carrier equalities preserve every endpoint,
including zero amounts, full amounts, singleton fragments, and empty atoms.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperDomainDifference

open UpperRecordedDomain UpperCircular UpperPhysical

theorem separated_Ioc_iff (cs : List Component) (a b : ℝ)
    (ha : SeparatedAt a cs) (hb : SeparatedAt b cs)
    (c : Component) (hc : c ∈ cs) {x : ℝ} (hx : x ∈ c.carrier) :
    x ∈ Ioc a b ↔ a < c.right ∧ c.right ≤ b := by
  constructor
  · intro h
    refine ⟨h.1.trans_le (c.subset_closed hx).2, ?_⟩
    by_contra hn
    have hbx := hb c hc (lt_of_not_ge hn) hx
    exact (not_lt_of_ge h.2) hbx
  · intro h
    exact ⟨ha c hc h.1 hx, (c.subset_closed hx).2.trans h.2⟩

def intervalAtoms (a b : ℝ) (cs : List Component) : List Component :=
  cs.filter (fun c => decide (a < c.right ∧ c.right ≤ b))

def outsideAtoms (a b : ℝ) (cs : List Component) : List Component :=
  cs.filter (fun c => decide (¬(a < c.right ∧ c.right ≤ b)))

theorem domain_filter_carrier (cs : List Component) (keep : Component → Bool) (S : Set ℝ)
    (hkeep : ∀ c ∈ cs, ∀ x ∈ c.carrier, keep c = true ↔ x ∈ S) :
    domain (cs.filter keep) = domain cs ∩ S := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, hxc⟩ := mem_domain.mp hx
    obtain ⟨hmem, hkeepc⟩ := List.mem_filter.mp hc
    exact ⟨mem_domain.mpr ⟨c, hmem, hxc⟩, (hkeep c hmem x hxc).mp hkeepc⟩
  · rintro ⟨hx, hS⟩
    obtain ⟨c, hc, hxc⟩ := mem_domain.mp hx
    exact mem_domain.mpr ⟨c, List.mem_filter.mpr ⟨hc, (hkeep c hc x hxc).mpr hS⟩, hxc⟩

theorem intervalAtoms_domain (cs : List Component) (a b : ℝ)
    (ha : SeparatedAt a cs) (hb : SeparatedAt b cs) :
    domain (intervalAtoms a b cs) = domain cs ∩ Ioc a b := by
  apply domain_filter_carrier
  intro c hc x hx
  simpa using (separated_Ioc_iff cs a b ha hb c hc hx).symm

theorem outsideAtoms_domain (cs : List Component) (a b : ℝ)
    (ha : SeparatedAt a cs) (hb : SeparatedAt b cs) :
    domain (outsideAtoms a b cs) = domain cs \ Ioc a b := by
  apply domain_filter_carrier cs _ (Ioc a b)ᶜ
  intro c hc x hx
  simp only [decide_eq_true_eq, mem_compl_iff]
  exact not_congr (separated_Ioc_iff cs a b ha hb c hc hx).symm

/-- Whole-cell exclusions are exact because distinct original components
have disjoint literal carriers. -/
theorem whole_filter_domain (cs : List Component) (hdisjoint : DisjointComponents cs)
    (remove : Component → Bool) :
    domain (cs.filter (fun c => !remove c)) = domain cs \ domain (cs.filter remove) := by
  let : Std.Symm (fun c d : Component => Disjoint c.carrier d.carrier) :=
    ⟨fun _ _ h => h.symm⟩
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, hxc⟩ := mem_domain.mp hx
    have hmem := (List.mem_filter.mp hc).1
    have hremove : remove c = false := by simpa using (List.mem_filter.mp hc).2
    refine ⟨mem_domain.mpr ⟨c, hmem, hxc⟩, ?_⟩
    intro hy
    obtain ⟨d, hd, hxd⟩ := mem_domain.mp hy
    have hmemd := (List.mem_filter.mp hd).1
    have hremoved : remove d = true := (List.mem_filter.mp hd).2
    have hne : c ≠ d := by intro h; subst d; simp [hremove] at hremoved
    exact Set.disjoint_left.mp (hdisjoint.forall hmem hmemd hne) hxc hxd
  · rintro ⟨hx, hnot⟩
    obtain ⟨c, hc, hxc⟩ := mem_domain.mp hx
    have hremove : remove c = false := by
      by_contra hn
      have ht : remove c = true := by cases h : remove c <;> simp_all
      exact hnot (mem_domain.mpr ⟨c, List.mem_filter.mpr ⟨hc, ht⟩, hxc⟩)
    exact mem_domain.mpr ⟨c, List.mem_filter.mpr ⟨hc, by simp [hremove]⟩, hxc⟩

/-- Actual arithmetic/list implementation of removing a two-endpoint
physical circular piece. It never replaces a carrier by an a.e. equivalent
half-open interval. -/
def removeCorrection (cs : List Component) (amount : I) (start : UpperCircular.Circle)
    (first last : ℝ) : List Component :=
  if amount = 0 then cs else if amount = 1 then [] else
    let refined := refineAt last (refineAt first cs)
    if value start < value (start + project amount) then outsideAtoms first last refined
    else intervalAtoms last first refined

theorem removeCorrection_domain (cs : List Component) (amount : I) (start : UpperCircular.Circle)
    (first last : ℝ) :
    domain (removeCorrection cs amount start first last) =
      domain cs \ physicalPiece (domain cs) amount start first last := by
  have hfirst := refineAt_preserves_separated last first (refineAt first cs)
    (refineAt_separated first cs)
  have hlast := refineAt_separated last (refineAt first cs)
  unfold removeCorrection physicalPiece
  dsimp only
  split_ifs with hzero hone hwrap
  · simp
  · simp [domain]
  · rw [outsideAtoms_domain _ _ _ hfirst hlast, refineAt_domain, refineAt_domain]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  · rw [intervalAtoms_domain _ _ _ hlast hfirst, refineAt_domain, refineAt_domain]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto

theorem removeCorrection_ordered (cs : List Component) (hcs : Ordered cs)
    (amount : I) (start : UpperCircular.Circle) (first last : ℝ) :
    Ordered (removeCorrection cs amount start first last) := by
  have hr := refineAt_ordered last _ (refineAt_ordered first cs hcs)
  unfold removeCorrection
  split_ifs
  · exact hcs
  · simp [Ordered]
  · exact hr.filter _
  · exact hr.filter _

theorem removeCorrection_disjoint (cs : List Component) (hcs : DisjointComponents cs)
    (amount : I) (start : UpperCircular.Circle) (first last : ℝ) :
    DisjointComponents (removeCorrection cs amount start first last) := by
  have hr := refineAt_disjoint last _ (refineAt_disjoint first cs hcs)
  unfold removeCorrection
  split_ifs
  · exact hcs
  · simp [DisjointComponents]
  · exact hr.filter _
  · exact hr.filter _

theorem filter_recorded (cs : List Component) (keep : Component → Bool) {p : ℝ}
    (hp : Recorded (cs.filter keep) p) : Recorded cs p := by
  obtain ⟨c, hc, hp⟩ := hp
  exact ⟨c, (List.mem_filter.mp hc).1, hp⟩

theorem removeCorrection_recorded (cs : List Component) (amount : I) (start : UpperCircular.Circle)
    (first last : ℝ) {p : ℝ} (hp : Recorded (removeCorrection cs amount start first last) p) :
    p = first ∨ p = last ∨ Recorded cs p := by
  have hreduce (hp : Recorded (refineAt last (refineAt first cs)) p) :
      p = first ∨ p = last ∨ Recorded cs p := by
    rcases refineAt_recorded last _ hp with h | h
    · exact Or.inr (Or.inl h)
    · rcases refineAt_recorded first cs h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  unfold removeCorrection at hp
  split_ifs at hp
  · exact Or.inr (Or.inr hp)
  · obtain ⟨c, hc, _⟩ := hp
    simp at hc
  · exact hreduce (filter_recorded _ _ hp)
  · exact hreduce (filter_recorded _ _ hp)

end EnvyFreeResearch.Full.UpperDomainDifference
