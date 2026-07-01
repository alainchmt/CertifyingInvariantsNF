import IdealArithmetic.Galois.Parity

/-!
# Degree-3 milestone — the Galois group of an irreducible cubic

The first end-to-end certified Galois group: for an irreducible cubic over `ℚ`, the Galois group is
cyclic of order 3 (`A₃`) exactly when the discriminant is a square, and `S₃` (order 6) otherwise.
Combines Core Theorem 2 (`range_galActionHom_le_alternatingGroup_iff`) with the fact that the image
of `Gal` is a transitive subgroup of `S₃`.

See `.mathlib-quality/tickets.md`, T007.
-/

namespace IdealArithmetic.Galois

open Polynomial Finset Polynomial.Gal

/-- **T007 / Milestone M1.** For a monic irreducible cubic over `ℚ`, the Galois group has order 3
when the discriminant is a square (the group is `A₃`), and order 6 otherwise (the group is `S₃`). -/
theorem galoisGroup_cubic (p : ℚ[X]) (hp : Irreducible p) (hmonic : p.Monic)
    (h3 : p.natDegree = 3) :
    (IsSquare p.discr → Nat.card p.Gal = 3) ∧ (¬ IsSquare p.discr → Nat.card p.Gal = 6) := by
  classical
  have hsep : p.Separable := hp.separable
  have hcardGal : Nat.card p.Gal = Nat.card (galActionHom p p.SplittingField).range :=
    Nat.card_congr (MonoidHom.ofInjective (galActionHom_injective p p.SplittingField)).toEquiv
  have hcardRoot : Fintype.card {x // x ∈ p.rootSet p.SplittingField} = 3 := by
    rw [card_rootSet_eq_natDegree hsep (IsSplittingField.splits p.SplittingField p), h3]
  have hcardRootN : Nat.card {x // x ∈ p.rootSet p.SplittingField} = 3 :=
    Nat.card_eq_fintype_card.trans hcardRoot
  have h3dvd : 3 ∣ Nat.card (galActionHom p p.SplittingField).range := by
    rw [← hcardGal]
    have hpt : MulAction.IsPretransitive p.Gal (p.rootSet p.SplittingField) :=
      galAction_isPretransitive p p.SplittingField hp
    obtain ⟨x⟩ : Nonempty (p.rootSet p.SplittingField) := by
      rw [← Fintype.card_pos_iff, hcardRoot]
      norm_num
    -- Pin `galAction` explicitly: `galActionAux` also provides `MulAction p.Gal (rootSet p SF)`,
    -- so bare instance synthesis picks the wrong `MulAction` and `hpt` fails to match.
    have hidx := @MulAction.index_stabilizer_of_transitive p.Gal _ _
      (Polynomial.Gal.galAction p p.SplittingField) x hpt
    have hdvd := Subgroup.index_dvd_card
      (@MulAction.stabilizer p.Gal _ _ (Polynomial.Gal.galAction p p.SplittingField) x)
    rwa [hidx, hcardRootN] at hdvd
  have hdvd6 : Nat.card (galActionHom p p.SplittingField).range ∣ 6 := by
    have h := Subgroup.card_subgroup_dvd_card (galActionHom p p.SplittingField).range
    rwa [Nat.card_perm, hcardRootN] at h
  have hR2 : (galActionHom p p.SplittingField).range ≤ alternatingGroup _ ↔ IsSquare p.discr :=
    range_galActionHom_le_alternatingGroup_iff p hmonic hsep
  have hcardA3 : Nat.card (alternatingGroup {x // x ∈ p.rootSet p.SplittingField}) = 3 := by
    have : Nontrivial {x // x ∈ p.rootSet p.SplittingField} :=
      Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    rw [nat_card_alternatingGroup, hcardRootN]
    decide
  have horder3_le : Nat.card (galActionHom p p.SplittingField).range = 3 →
      (galActionHom p p.SplittingField).range ≤ alternatingGroup _ := by
    intro hcard3 x hx
    rw [Equiv.Perm.mem_alternatingGroup]
    set G := (galActionHom p p.SplittingField).range
    have hxpow : x ^ orderOf (⟨x, hx⟩ : G) = 1 := by
      have h := congrArg G.subtype (pow_orderOf_eq_one (⟨x, hx⟩ : G))
      rwa [map_pow, map_one] at h
    have hdvd : orderOf (⟨x, hx⟩ : G) ∣ 3 := hcard3 ▸ orderOf_dvd_natCard (⟨x, hx⟩ : G)
    have hsign : Equiv.Perm.sign x ^ orderOf (⟨x, hx⟩ : G) = 1 := by
      have h := congrArg Equiv.Perm.sign hxpow
      rwa [map_pow, map_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign x) with h1 | hm1
    · exact h1
    · exfalso
      rw [hm1] at hsign
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h <;>
        rw [h] at hsign <;> revert hsign <;> decide
  refine ⟨fun hsq => ?_, fun hnsq => ?_⟩
  · exact hcardGal.trans (Nat.dvd_antisymm (hcardA3 ▸ Subgroup.card_dvd_of_le (hR2.mpr hsq)) h3dvd)
  · have hn3 : Nat.card (galActionHom p p.SplittingField).range ≠ 3 :=
      fun h => hnsq (hR2.mp (horder3_le h))
    have hle6 : Nat.card (galActionHom p p.SplittingField).range ≤ 6 :=
      Nat.le_of_dvd (by norm_num) hdvd6
    rw [hcardGal]
    interval_cases (Nat.card (galActionHom p p.SplittingField).range) <;> omega

end IdealArithmetic.Galois
