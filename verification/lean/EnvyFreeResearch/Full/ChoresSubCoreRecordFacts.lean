import EnvyFreeResearch.Full.ChoresSubCorePhysicalStore

/-!
# Exact order reflection inside a permanent physical parent table

Any observer's formal row determines the order of two records from the same
parent table. This certifies a returned formal trim lies below its offered
whole record, even when both records have the same physical coordinate.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCorePhysical

open Persistent

theorem pairwise_members_trichotomy {α : Type*} {R : α → α → Prop} {xs : List α}
    (h : xs.Pairwise R) {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) : a = b ∨ R a b ∨ R b a := by
  induction xs with
  | nil => simp at ha
  | cons c xs ih =>
    obtain ⟨hc, htail⟩ := List.pairwise_cons.mp h
    by_cases hac : a = c
    · subst a
      by_cases hbc : b = c
      · exact Or.inl hbc.symm
      · exact Or.inr (Or.inl (hc b ((List.mem_cons.mp hb).resolve_left hbc)))
    · have ha' : a ∈ xs := (List.mem_cons.mp ha).resolve_left hac
      by_cases hbc : b = c
      · subst b
        exact Or.inr (Or.inr (hc a ha'))
      · exact ih htail ha' ((List.mem_cons.mp hb).resolve_left hbc)

theorem ordered_le_iff_formal_le {n : ℕ} (records : List (Record n)) (horder : records.Pairwise Before)
    (i : Fin n) {r s : Record n} (hr : r ∈ records) (hs : s ∈ records) :
    orderedRecord r ≤ orderedRecord s ↔ formalValue i (orderedRecord r) ≤ formalValue i (orderedRecord s) := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  rcases pairwise_members_trichotomy horder hr hs with rfl | h | h
  · exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  · exact ⟨fun _ => (formalValue_strict h i).le, fun _ => (before_ordered_lt hn h).le⟩
  · exact ⟨fun hbad => ((not_le_of_gt (before_ordered_lt hn h)) hbad).elim,
      fun hbad => ((not_le_of_gt (formalValue_strict h i)) hbad).elim⟩

theorem same_formal_record {n : ℕ} (records : List (Record n)) (horder : records.Pairwise Before)
    (i : Fin n) {r s : Record n} (hr : r ∈ records) (hs : s ∈ records)
    (heq : r.formal i = s.formal i) : r = s := by
  have hforward : orderedRecord r ≤ orderedRecord s := (ordered_le_iff_formal_le records horder i hr hs).mpr
    (congrArg toLex heq).le
  have hback : orderedRecord s ≤ orderedRecord r := (ordered_le_iff_formal_le records horder i hs hr).mpr
    (congrArg toLex heq.symm).le
  exact orderedRecord_injective (le_antisymm hforward hback)

theorem stored_formal_le_coord {n : ℕ} {GlobalParent Payload : Type*}
    (view : Payload → Record n) (store : Store GlobalParent Payload) (p : GlobalParent)
    (horder : (store p).Pairwise (fun r s => Before (view r) (view s)))
    (i : Fin n) (r s : OrderedRecord n) (hr : Stored view store p r) (hs : Stored view store p s)
    (hle : formalValue i r ≤ formalValue i s) : r ≤ s := by
  obtain ⟨rr, hrr, hr⟩ := hr
  obtain ⟨ss, hss, hs⟩ := hs
  have ho : ((store p).map view).Pairwise Before := by simpa only [List.pairwise_map] using horder
  have hr' : r.record ∈ (store p).map view := List.mem_map.mpr ⟨rr, hrr, hr⟩
  have hs' : s.record ∈ (store p).map view := List.mem_map.mpr ⟨ss, hss, hs⟩
  exact (ordered_le_iff_formal_le _ ho i hr' hs').mpr hle

theorem Extends.refl {GlobalParent Payload : Type*} (store : Store GlobalParent Payload) : Extends store store :=
  fun _ => List.Sublist.refl _

theorem Extends.trans {GlobalParent Payload : Type*} {first second third : Store GlobalParent Payload}
    (hfirst : Extends first second) (hsecond : Extends second third) : Extends first third :=
  fun p => (hfirst p).trans (hsecond p)

theorem Stored.mono {n : ℕ} {GlobalParent Payload : Type*} (view : Payload → Record n)
    {before after : Store GlobalParent Payload} (h : Extends before after)
    {p : GlobalParent} {r : OrderedRecord n} (hr : Stored view before p r) : Stored view after p r := by
  obtain ⟨payload, hpayload, heq⟩ := hr
  exact ⟨payload, (h p).subset hpayload, heq⟩

end EnvyFreeResearch.Full.Chores.SubCorePhysical
