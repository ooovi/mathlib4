import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Pairwise

/-!
# Independent Sets in Graphs

This file defines independent sets (aka cocliques) in simple graphs.
A clique is a set of vertices that are pairwise nonadjacent.

-/

open Finset Fintype Function SimpleGraph.Walk

namespace SimpleGraph

variable {α β : Type*} (G H : SimpleGraph α)

/-! ### Independent Sets -/

section IndependentSet

variable {s t : Set α}

/-- An independent set in a graph is a set of vertices that are pairwise not adjacent. -/
abbrev IsIndependentSet (s : Set α) : Prop :=
  s.Pairwise (fun v w ↦ ¬G.Adj v w)

theorem isIndependentSet_iff : G.IsIndependentSet s ↔ s.Pairwise (fun v w ↦ ¬G.Adj v w) :=
  Iff.rfl

/-- An independent set is a clique in the complement graph and vice versa. -/
theorem isIndependentSet_iff_isClique_of_complement : G.IsIndependentSet s ↔ Gᶜ.IsClique s := by
  rw [isIndependentSet_iff, isClique_iff]; repeat rw [Set.Pairwise]
  simp_all only [compl_adj, ne_eq, not_false_eq_true, true_and]

/-- An independent set is a set of vertices whose induced graph is empty. -/
theorem isIndependentSet_iff_induce_eq : G.IsIndependentSet s ↔ G.induce s = ⊥ := by
  have cc : Gᶜ.induce s = (G.induce s)ᶜ := by aesop
  have : Gᶜ.IsClique s ↔ Gᶜ.induce s = ⊤ := isClique_iff_induce_eq Gᶜ
  rw [cc] at this
  rw [isIndependentSet_iff_isClique_of_complement]
  aesop

instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsClique s) :=
  decidable_of_iff' _ G.isClique_iff

instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsIndependentSet s) :=
  decidable_of_iff' _ G.isIndependentSet_iff

variable {G H} {a b : α}

lemma isIndependentSet_empty : G.IsIndependentSet ∅ := by simp

lemma isIndependentSet_singleton (a : α) : G.IsIndependentSet {a} := by simp

theorem IsIndependentSet.of_subsingleton {G : SimpleGraph α} (hs : s.Subsingleton) :
    G.IsIndependentSet s :=
  hs.pairwise (fun v w => ¬ G.Adj v w)

lemma isIndependentSet_pair : G.IsIndependentSet {a, b} ↔ ¬ G.Adj a b := by
  rw [isIndependentSet_iff_isClique_of_complement]
  have cp : Gᶜ.IsClique {a, b} ↔ a ≠ b → Gᶜ.Adj a b := isClique_pair
  have neq_ad_iff_nadj : (a ≠ b → Gᶜ.Adj a b) ↔ ¬ G.Adj a b := by
    simp_all only [ne_eq, compl_adj, not_false_eq_true, true_and, Classical.imp_iff_right_iff]
    rw [←not_and_or];
    aesop;
  rw [neq_ad_iff_nadj] at cp
  exact cp

@[simp]
lemma isIndependentSet_insert :
    G.IsIndependentSet (insert a s) ↔ G.IsIndependentSet s ∧ ∀ b ∈ s, ¬ G.Adj a b := by
  repeat rw [isIndependentSet_iff_isClique_of_complement]
  have cin : Gᶜ.IsClique (insert a s) ↔ Gᶜ.IsClique s ∧ ∀ b ∈ s, a ≠ b → Gᶜ.Adj a b
    := isClique_insert
  -- TODO this is almost neq_ad_iff_nadj from the lemma above. make it a lemma if you can manage?!
  have hu : (∀ b ∈ s, (a ≠ b → Gᶜ.Adj a b)) ↔ ∀ b ∈ s, ¬ G.Adj a b := by aesop
  rw [hu] at cin
  exact cin

-- TODO this is implied in the normal insert one
--lemma isIndependentSet_insert_of_not_mem (ha : a ∉ s) :
--    G.IsIndependentSet (insert a s) ↔ G.IsIndependentSet s ∧ ∀ b ∈ s, ¬ G.Adj a b :=

-- TODO why do we have this?
lemma IsIndependentSet.insert (hs : G.IsIndependentSet s) (h : ∀ b ∈ s, ¬ G.Adj a b) :
    G.IsIndependentSet (insert a s) := isIndependentSet_insert.mpr ⟨hs ,h⟩

theorem IsIndependentSet.mono (h : G ≤ H) : H.IsIndependentSet s → G.IsIndependentSet s := by
  repeat rw [isIndependentSet_iff_isClique_of_complement]
  apply IsClique.mono (compl_le_compl_iff_le.mpr h)


@[simp]
theorem isIndependentSet_top_iff :
    (⊤ : SimpleGraph α).IsIndependentSet s ↔ (s : Set α).Subsingleton := by
  rw [isIndependentSet_iff_isClique_of_complement]
  simp only [compl_top, isClique_bot_iff]

alias ⟨IsIndependentSet.subsingleton, _⟩ := isIndependentSet_top_iff

@[simp]
lemma isClique_compl_map_iff_isClique_map_compl {f : α ↪ β} {s : Set α} :
   (SimpleGraph.map f G)ᶜ.IsClique (f '' s) ↔ (SimpleGraph.map f Gᶜ).IsClique (f '' s) := by
  repeat rw [isClique_iff];
  repeat rw [Set.Pairwise];
  aesop

protected theorem IsIndependentSet.map (h : G.IsIndependentSet s) {f : α ↪ β} :
    (G.map f).IsIndependentSet (f '' s) := by
  rw [isIndependentSet_iff_isClique_of_complement] at *
  simp_all [isClique_map_image_iff]

theorem isIndependentSet_map_iff_of_nontrivial {f : α ↪ β} {t : Set β} (ht : t.Nontrivial) :
    (G.map f).IsIndependentSet t ↔ ∃ (s : Set α), G.IsIndependentSet s ∧ f '' s = t := by
  repeat rw [isIndependentSet_iff_isClique_of_complement]
  sorry

-- TODO some more tricky map stuff here

end IndependentSet

-- TODO this is mostly just copy paste. ok?
section NIndependentSet

variable {n : ℕ} {s : Finset α}

/-- An `n`-IndependentSet in a graph is a set of `n` vertices which are pairwise nonadjacent. -/
structure IsNIndependentSet (n : ℕ) (s : Finset α) : Prop where
  IndependentSet : G.IsIndependentSet s
  card_eq : s.card = n

theorem isNIndependentSet_iff : G.IsNIndependentSet n s ↔ G.IsIndependentSet s ∧ s.card = n :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- An independent n-set is an n-clique in the complement graph and vice versa. -/
theorem isNIndependentSet_iff_isNClique_of_complement :
    G.IsNIndependentSet n s ↔ Gᶜ.IsNClique n s := by
  rw [isNIndependentSet_iff]; rw [isIndependentSet_iff_isClique_of_complement]
  simp [isNClique_iff]

instance [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α} :
    Decidable (G.IsNIndependentSet n s) :=
  decidable_of_iff' _ G.isNIndependentSet_iff

variable {G H} {a b c : α}

@[simp] lemma isNIndependentSet_empty : G.IsNIndependentSet n ∅ ↔ n = 0 :=
  by simp [isNIndependentSet_iff, eq_comm]

@[simp]
lemma isNIndependentSet_singleton : G.IsNIndependentSet n {a} ↔ n = 1 :=
  by simp [isNIndependentSet_iff, eq_comm]

theorem IsNIndependentSet.mono (h : G ≤ H) : H.IsNIndependentSet n s → G.IsNIndependentSet n s := by
  simp_rw [isNIndependentSet_iff]
  exact And.imp_left (IsIndependentSet.mono h)


@[simp]
theorem isNIndependentSet_top_iff :
    (⊤ : SimpleGraph α).IsNIndependentSet n s ↔ n ≤ 1 ∧ s.card = n := by
  rw [isNIndependentSet_iff, isIndependentSet_top_iff]
  refine and_congr_left ?_
  rintro rfl
  exact card_le_one.symm

@[simp]
theorem isNIndependentSet_zero : G.IsNIndependentSet 0 s ↔ s = ∅ := by
  simp only [isNIndependentSet_iff, Finset.card_eq_zero, and_iff_right_iff_imp]; rintro rfl; simp

@[simp]
theorem isNIndependentSet_one : G.IsNIndependentSet 1 s ↔ ∃ a, s = {a} := by
  simp only [isNIndependentSet_iff, card_eq_one, and_iff_right_iff_imp]; rintro ⟨a, rfl⟩; simp

section DecidableEq

variable [DecidableEq α]

theorem IsNIndependentSet.insert (hs : G.IsNIndependentSet n s) (h : ∀ b ∈ s, ¬ G.Adj a b) :
    a ∉ s → G.IsNIndependentSet (n + 1) (insert a s) := by
  intro ans
  constructor
  · push_cast
    exact hs.1.insert fun b hb hab => h b hb hab
  · rw [card_insert_of_not_mem ans, hs.2]

theorem is3IndependentSet_triple_iff :
    G.IsNIndependentSet 3 {a, b, c} ↔
    (a ≠ b ∧ ¬ G.Adj a b) ∧ (a ≠ c ∧ ¬ G.Adj a c) ∧ (b ≠ c ∧ ¬ G.Adj b c) := by
  rw [isNIndependentSet_iff_isNClique_of_complement]
  repeat rw [←compl_adj]
  simp [is3Clique_triple_iff]

theorem is3IndependentSet_iff :
    G.IsNIndependentSet 3 s ↔
    ∃ a b c, (a ≠ b ∧ ¬ G.Adj a b) ∧ (a ≠ c ∧ ¬ G.Adj a c) ∧ (b ≠ c ∧ ¬ G.Adj b c) ∧
    s = {a, b, c} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨a, b, c, -, -, -, hs⟩ := card_eq_three.1 h.card_eq
    refine ⟨a, b, c, ?_⟩
    rwa [hs, eq_self_iff_true, and_true, is3IndependentSet_triple_iff.symm, ← hs]
  · rintro ⟨a, b, c, hab, hbc, hca, rfl⟩
    exact is3IndependentSet_triple_iff.2 ⟨hab, hbc, hca⟩

-- theorem is3IndependentSet_iff_exists_cycle_length_three :
-- (∃ s : Finset α, G.IsNIndependentSet 3 s) ↔ ∃ (u : α) (w : G.Walk u u), w.IsCycle ∧ w.length
-- TODO is there a dual to this one? if not, do we even need the other thrms about 3-sets?

end DecidableEq

end NIndependentSet

end SimpleGraph
