/- Authors: Alain Chavarri Villarello -/

import IdealArithmetic.MordellThueProject.ElementarySkolem

/-!
# Checking a Skolem certificate on a times table

## AI use
This file was partially generated using Claude Code with Opus 5. The main definitions
were human-written, as well as the statement of `coordMod_mul`. A natural-language
description of the rest of the main results and the proof strategy was specified by me, while
the proofs were mostly AI-generated. We also carried out some polishing afterwards.

## Main definitions
- `muOfBasis`: the `ℤ`-linear functional `O →ₗ[ℤ] ℤ` given by a fixed integer combination
  of the coordinates with respect to `b`.
- `coordMod`: the coordinate vector of an element, reduced modulo `m`.

## Main results
- `coordMod_mul`, `coordMod_pow_succ`: coordinate vectors multiply through the reduced times
  table.
- `not_dvd_muOfBasis_iff`: decided by one entry of the reduced vector.
- `exists_delta_of_coordMod`, `exists_delta_not_dvd_mu`: read off from the
  coordinate vector of `ε ^ f` modulo `p ^ 2`.  -/

open Finset Module

section MuTimesTables

variable {n : ℕ} {O : Type*} [CommRing O] {b : Basis (Fin n) ℤ O}


noncomputable def muOfBasis (b : Basis (Fin n) ℤ O) (k : Fin n → ℤ) : O →ₗ[ℤ] ℤ :=
  ∑ i, k i • b.coord i

lemma muOfBasis_apply (k : Fin n → ℤ) (x : O) :
    muOfBasis b k x = ∑ i, k i * b.equivFun x i := by
  simp [muOfBasis, Basis.coord_apply, Basis.equivFun_apply]

/-- The coordinate vector of `x` with respect to `b`, reduced modulo `m`.  Reducible, so a
hypothesis stated with `algebraMap ℤ (ZMod m) ∘ (b.equivFun x)` matches it definitionally.
Like `muOfBasis`, this needs only the basis, never the multiplication table. -/
noncomputable abbrev coordMod (b : Basis (Fin n) ℤ O) (m : ℕ) (x : O) : Fin n → ZMod m :=
  algebraMap ℤ (ZMod m) ∘ (b.equivFun x)

/-- `mu` of an element given by its coordinate vector. -/
lemma muOfBasis_symm (k v : Fin n → ℤ) :
    muOfBasis b k (b.equivFun.symm v) = ∑ i, k i * v i := by
  rw [muOfBasis_apply, LinearEquiv.apply_symm_apply]

/-- On a basis vector, `mu` is the corresponding weight. -/
lemma muOfBasis_basis (k : Fin n → ℤ) (i : Fin n) :
    muOfBasis b k (b i) = k i := by
  rw [muOfBasis_apply]
  simp [Basis.equivFun_self, Finset.sum_ite_eq]

lemma coordMod_one {m : ℕ} {i₀ : Fin n} (hB0 : b i₀ = 1) :
    coordMod b m 1 = fun i => if i = i₀ then 1 else 0 := by
  funext i
  simp only [coordMod, Function.comp_apply, Basis.equivFun_apply, ← hB0, Basis.repr_self,
    Finsupp.single_apply]
  rcases eq_or_ne i i₀ with rfl | h
  · simp
  · simp [h, h.symm]

/-- **Multiplication on coordinate vectors modulo `m`.**  If `a`, `b` are the coordinate
vectors of `x`, `y` reduced mod `m`, and `c` is their product with respect to the reduced
times table `TMod`, then `c` is the reduced coordinate vector of `x * y`. -/
lemma coordMod_mul {TT : TimesTable (Fin n) ℤ O} {m : ℕ} {T : Fin n → Fin n → List ℤ}
    (heq : ∀ i j, T i j = List.ofFn (TT.table i j))
    {TMod : Fin n → Fin n → List (ZMod m)}
    (hTMod : ∀ i j, List.map (algebraMap ℤ (ZMod m)) (T i j) = TMod i j)
    {x y : O} {a b c : Fin n → ZMod m}
    (ha : coordMod TT.basis m x = a) (hb : coordMod TT.basis m y = b)
    (hc : List.ofFn c = table_mul_list TMod (List.ofFn a) (List.ofFn b)) :
    coordMod TT.basis m (x * y) = c := by
  set TMod' : Fin n → Fin n → Fin n → ZMod m :=
    fun i j k => algebraMap ℤ (ZMod m) (TT.table i j k) with hTMod'
  have hlist : ∀ i j, TMod i j = List.ofFn (TMod' i j) := fun i j => by
    rw [← hTMod i j, heq i j, hTMod', List.map_ofFn]
    rfl
  rw [table_mul_eq_table_mul' TMod' TMod hlist] at hc
  have hsum := FnOfList_table_mul_list_eq_sum_sum TMod' a b c hc
  funext k
  rw [hsum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [coordMod, Function.comp_apply, Basis.equivFun_apply]
  rw [TimesTable.unfold_mul' TT]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← ha, ← hb, hTMod']
  simp [Basis.equivFun_apply]

/-- **Powers, one step at a time.**  If `a` is the coordinate vector of `x` modulo `m` and
`cr` that of `x ^ r`, then their table product is the coordinate vector of `x ^ (r + 1)`.
Chaining this lemma computes `x, x ^ 2, …, x ^ f` with one `table_mul_list` per step. -/
lemma coordMod_pow_succ {TT : TimesTable (Fin n) ℤ O} {m : ℕ} {T : Fin n → Fin n → List ℤ}
    (heq : ∀ i j, T i j = List.ofFn (TT.table i j))
    {TMod : Fin n → Fin n → List (ZMod m)}
    (hTMod : ∀ i j, List.map (algebraMap ℤ (ZMod m)) (T i j) = TMod i j)
    {x : O} {a cr cs : Fin n → ZMod m} {r : ℕ}
    (ha : coordMod TT.basis m x = a) (hr : coordMod TT.basis m (x ^ r) = cr)
    (hc : List.ofFn cs = table_mul_list TMod (List.ofFn cr) (List.ofFn a)) :
    coordMod TT.basis m (x ^ (r + 1)) = cs := by
  rw [pow_succ]
  exact coordMod_mul heq hTMod hr ha hc

/-- `mu x` mod `m` is the `k`-th entry of the reduced coordinate vector. -/
lemma muOfBasis_cast {m : ℕ} {x : O} {a : Fin n → ZMod m} (ha : coordMod b m x = a)
    (k : Fin n → ℤ) : ((muOfBasis b k x : ℤ) : ZMod m) = ∑ i, (k i : ZMod m) * a i := by
  rw [muOfBasis_apply, ← ha]
  push_cast
  rfl

/-- **The `(S2)`/`(S3)` test.**  With `p ∣ m`, `p ∤ mu x` is decided by the `k`-th entry of
the coordinate vector of `x` mod `m`, pushed down to `ZMod p`. -/
lemma not_dvd_muOfBasis_iff {p m : ℕ} (hpm : p ∣ m) {x : O} {a : Fin n → ZMod m}
    (ha : coordMod b m x = a) (k : Fin n → ℤ) :
    ¬ ((p : ℤ) ∣ muOfBasis b k x) ↔
      ZMod.castHom hpm (ZMod p) (∑ i, (k i : ZMod m) * a i) ≠ 0 := by
  rw [← muOfBasis_cast ha k, map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]


/-- Reducing the modulus: the coordinate vector mod `p` is the coordinate vector mod `m`
pushed down, whenever `p ∣ m`.  Lets one chain of multiplications mod `p ^ 2` serve both the
sieve and the re-centering test. -/
lemma coordMod_castHom {p m : ℕ} (hpm : p ∣ m) (x : O) :
    coordMod b p x = fun i => ZMod.castHom hpm (ZMod p) (coordMod b m x i) :=
  funext fun _ => (map_intCast (ZMod.castHom hpm (ZMod p)) _).symm

lemma coordMod_sub {m : ℕ} (x y : O) :
    coordMod b m (x - y) = coordMod b m x - coordMod b m y := by
  funext i
  simp only [coordMod, Function.comp_apply, Basis.equivFun_apply, map_sub, Pi.sub_apply]

/-- **Reading off `δ` from `u` mod `p ^ 2`.**  Suppose the coordinate vector of `u` mod `p ^ 2`
is `a`, and that `a` minus the coordinate vector of `1` is `p` times the lift of
`e : Fin n → ZMod p`.  Then `u = 1 + p δ` for an explicit `δ`, whose coordinates mod `p` are
exactly `e`.  Combined with `muOfBasis_cast` this computes `mu δ` mod `p`, i.e. `(S2)`. -/
theorem exists_delta_of_coordMod {p : ℕ} (hp : 0 < p) {i₀ : Fin n} (hB0 : b i₀ = 1)
    {u : O} {a : Fin n → ZMod (p ^ 2)} (ha : coordMod b (p ^ 2) u = a)
    (e : Fin n → ZMod p)
    (hae : ∀ i, a i - (if i = i₀ then 1 else 0)
      = (p : ZMod (p ^ 2)) * ((e i).val : ZMod (p ^ 2))) :
    ∃ δ : O, u = p * δ + 1 ∧ coordMod b p δ = e := by
  haveI : NeZero p := ⟨hp.ne'⟩
  set w : Fin n → ℤ := b.equivFun (u - 1) with hw
  have hwmod : ∀ i, w i = (p : ZMod (p ^ 2)) * ((e i).val : ZMod (p ^ 2)) := by
    intro i
    have h := congrFun (coordMod_sub (b := b) (m := p ^ 2) u 1) i
    rw [ha, coordMod_one hB0] at h
    have hrfl : (b.equivFun (u - 1) i : ZMod (p ^ 2)) = coordMod b (p ^ 2) (u - 1) i := rfl
    rw [hw, hrfl, h, Pi.sub_apply, hae i]
  have hsq : ∀ i, ((p ^ 2 : ℕ) : ℤ) ∣ w i - p * (e i).val := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hwmod i]
    ring
  have hdvd : ∀ i, (p : ℤ) ∣ w i := by
    intro i
    have hpp : (p : ℤ) ∣ ((p ^ 2 : ℕ) : ℤ) := by
      push_cast
      exact dvd_pow_self _ two_ne_zero
    have h2 : (p : ℤ) ∣ p * (e i).val := Dvd.intro _ rfl
    simpa using (hpp.trans (hsq i)).add h2
  set d : Fin n → ℤ := fun i => w i / p
  have hpd : ∀ i, p * d i = w i := fun i => Int.mul_ediv_cancel' (hdvd i)
  refine ⟨b.equivFun.symm d, ?_, funext fun k => ?_⟩
  · have hcast : (p : O) * b.equivFun.symm d = (p : ℤ) • b.equivFun.symm d := by
      rw [zsmul_eq_mul]
      push_cast
      ring
    have hsmul : (p : ℤ) • d = w := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, hpd]
    have key : (p : O) * b.equivFun.symm d = u - 1 := by
      rw [hcast, ← LinearEquiv.map_smul, hsmul, hw, LinearEquiv.symm_apply_apply]
    rw [key]
    ring
  · show b.equivFun (b.equivFun.symm d) k = e k
    rw [LinearEquiv.apply_symm_apply]
    have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
    have h := hsq k
    push_cast at h
    rw [← hpd k, ← mul_sub, pow_two] at h
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (d k - (e k).val) p).mpr
      ((mul_dvd_mul_iff_left hp0).mp h)
    push_cast at h2
    rw [sub_eq_zero.mp h2]
    simp

/-- **Packaged `(S1)` and `(S2)`.**  Exactly the data `skolem_zpow_eq_zero_iff` consumes,
read off from the coordinates of `u` modulo `p ^ 2`. -/
theorem exists_delta_not_dvd_mu {p : ℕ} (hp : 0 < p) {i₀ : Fin n} (hB0 : b i₀ = 1)
    (k : Fin n → ℤ)
    {u : O} {a : Fin n → ZMod (p ^ 2)} (ha : coordMod b (p ^ 2) u = a)
    (e : Fin n → ZMod p)
    (hae : ∀ i, a i - (if i = i₀ then 1 else 0)
      = (p : ZMod (p ^ 2)) * ((e i).val : ZMod (p ^ 2)))
    (hek : ∑ i, (k i : ZMod p) * e i ≠ 0) :
    ∃ δ : O, u = p * δ + 1 ∧ ¬ ((p : ℤ) ∣ muOfBasis b k δ) := by
  obtain ⟨δ, hδ, hcoord⟩ := exists_delta_of_coordMod hp hB0 ha e hae
  refine ⟨δ, hδ, fun hdvd => hek ?_⟩
  rw [← muOfBasis_cast hcoord k, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd]

end MuTimesTables
