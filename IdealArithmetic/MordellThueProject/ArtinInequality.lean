import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact
import IdealArithmetic.Saturation.PrincipalityCertificate


/- # Artin inequality

We prove Artin inequality for units in orders of cubic number fields with signature `(1,1)` .

## AI use
The specifications of lemmas and theorems were mostly human-written
(with small later modifications by the model) while the proofs were done
mainly with Sonnet 5, and later Opus 5 for refinements, with the strategy specified by me.
We also carried out some polishing afterwards.

## Main Definition:
- `artin_inequality_order`: a strict lower bound for the absolute discriminant in terms of the value of
a unit under the real embedding.
- `artin_inequality_bound_index'` : proves that a unit that is `p`-saturated for all primes
below certain bound is fundamental.
- `units_pow_of_pMaximalUnitsCertificateNDvdT`: proves a generator for the unit group
 modulo `p`-th powers from a certificate pMaximalUnitsCertificateNDvdT (applies to odd `p`).
- `units_pow_of_pMaximalUnitsCertificateDvdT`: proves a ± generator for the unit group
 modulo `p`-th powers from a certificate pMaximalUnitsCertificateDvdT (applied to `p = 2`).


-/

open NumberField.ComplexEmbedding IntermediateField Module

lemma mem_Ioo_of_quadratic_neg {R : Type*} [CommRing R]
    {a b c x₁ x₂ y : R} [LinearOrder R] [IsStrictOrderedRing R] (ha : 0 < a)
    (h₁ : a * x₁ ^ 2 + b * x₁ + c = 0) (h₂ : a * x₂ ^ 2 + b * x₂ + c = 0)
    (hlt : x₁ < x₂) (hy : a * y ^ 2 + b * y + c < 0) : x₁ < y ∧ y < x₂ := by
  have hb : (x₁ - x₂) * (a * (x₁ + x₂) + b) = 0 := by linear_combination h₁ - h₂
  have aux : a * y ^ 2 + b * y + c = a * ((y - x₁) * (y - x₂)) := by
    linear_combination (y - x₁) * ((mul_eq_zero.mp hb).resolve_left (sub_ne_zero_of_ne hlt.ne)) + h₁
  exact (sub_mul_sub_neg_iff y hlt.le).1 ((pos_iff_neg_of_mul_neg (aux ▸ hy)).mp ha)

open Complex

lemma sq_prod_sub_exp_eq_neg_cos_sq {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    ((x⁻¹ * exp (I * t) - x ^ 2) * (x⁻¹ * exp (- I * t) - x ^ 2) *
      (x⁻¹ * exp (I * t) - x ⁻¹ * exp (-I * t))) ^ 2 =
    - 16 * (1 - (Real.cos t) ^ 2 ) * (((x ^ 3 + (x⁻¹) ^ 3) / 2) - Real.cos t) ^ 2  := by
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
  have hexp1 : exp (I * t) * exp (-(I * t)) = 1 := by
    rw [← exp_add]
    norm_num
  have hp : exp (I * t) = Real.cos t + Real.sin t * I := by
    rw [mul_comm, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hm : exp (-(I * t)) = Real.cos t - Real.sin t * I := by
    rw [mul_comm, ← neg_mul, exp_mul_I, cos_neg, sin_neg,← ofReal_cos, ← ofReal_sin]
    ring
  rw [neg_mul]
  calc ((x⁻¹ * exp (I * t) - x ^ 2) * (x⁻¹ * exp (-(I * t)) - x ^ 2) *
        (x⁻¹ * exp (I * t) - x⁻¹ * exp (-(I * t)))) ^ 2
      = ((x ^ 4 + (x⁻¹) ^ 2 - x * (exp (I * t) + exp (-(I * t))))
          * (x⁻¹ * exp (I * t) - x⁻¹ * exp (-(I * t)))) ^ 2 := by
        congr
        push_cast
        grind
    _ = ((x ^ 3 + (x⁻¹) ^ 3 - (exp (I * t) + exp (-(I * t))))
          * (exp (I * t) - exp (-(I * t)))) ^ 2 := by
        push_cast
        grind
    _ = (-4 * (Real.sin t) ^ 2 * (x ^ 3 + (x⁻¹) ^ 3 - 2 * Real.cos t) ^ 2 : ℂ) := by
        rw [hp, hm]; push_cast; ring_nf; rw [I_sq]; ring
    _ = (- 16 * (1 - (Real.cos t) ^ 2) * (((x ^ 3 + (x⁻¹) ^ 3) / 2) - Real.cos t) ^ 2 : ℂ) := by
        have key : -4 * (Real.sin t) ^ 2 * (x ^ 3 + (x⁻¹) ^ 3 - 2 * Real.cos t) ^ 2 =
            - 16 * (1 - (Real.cos t) ^ 2) * (((x ^ 3 + (x⁻¹) ^ 3) / 2) - Real.cos t) ^ 2 := by
          rw [Real.sin_sq]; ring
        exact_mod_cast key


lemma mul_eq_two_mul_sq_sub_one_of_isMaxOn {y0 a : ℝ} (ha : 1 < a) (hy0 : y0 ∈ Set.Icc (-1) 1)
    (h : ∀ y ∈ Set.Icc (-1) 1 , 16 * (1 - y ^ 2) * (a - y) ^ 2 ≤ 16 * (1 - y0 ^ 2) * (a - y0) ^ 2) :
    a * y0 = 2 * y0 ^ 2 - 1 := by
  have h0 := h 0 (by norm_num)
  have hlt1 : y0 < 1 := lt_of_le_of_ne hy0.2 (by rintro rfl; nlinarith)
  have hlt2 : -1 < y0 := lt_of_le_of_ne hy0.1 (by rintro rfl; nlinarith)
  have hmax : IsLocalMax (fun y => 16 * (1 - y ^ 2) * (a - y) ^ 2) y0 :=
    (isMaxOn_iff.mpr h).isLocalMax (Icc_mem_nhds hlt2 hlt1)
  have hderiv : HasDerivAt (fun y => 16 * (1 - y ^ 2) * (a - y) ^ 2)
      (32 * (a - y0) * (2 * y0 ^ 2 - a * y0 - 1)) y0 := by
    have key : HasDerivAt (fun y => 16 * (1 - y ^ 2) * (a - y) ^ 2)
        (16 * -(2 * y0) * (a - y0) ^ 2 + 16 * (1 - y0 ^ 2) * (2 * (a - y0) ^ (2 - 1) * (-1))) y0 := by
      apply HasDerivAt.mul
      · apply HasDerivAt.const_mul
        simpa using (hasDerivAt_const y0 1).sub ((hasDerivAt_id y0).pow 2)
      · simpa using ((hasDerivAt_const y0 a).sub (hasDerivAt_id y0)).pow 2
    convert key using 1
    ring
  have h' : 2 * y0 ^ 2 - a * y0 - 1 = 0 :=
    (mul_eq_zero.mp (hmax.hasDerivAt_eq_zero hderiv)).resolve_left
      (mul_ne_zero (by norm_num) (by linarith))
  linarith

theorem embeddings_ne {K : Type*} [Field K] {σ φ : K →+* ℂ}
    (hφ : IsReal φ) (hσ : ¬ IsReal σ) : σ ≠ φ ∧ conjugate σ ≠ φ ∧ σ ≠ conjugate σ := by
  refine ⟨fun h => hσ (h ▸ hφ), fun h => hσ ?_, fun h => hσ ?_⟩
  · rw [← isReal_conjugate_iff, h]; exact hφ
  · rw [isReal_iff]; exact h.symm

variable {K : Type*} [Field K] [NumberField K]

lemma adjoin_eq_top_of_natDegree_minpoly_eq_three (hdeg : Module.finrank ℚ K = 3)
    {v : K} (hv3 : (minpoly ℚ v).natDegree = 3) : Algebra.adjoin ℚ {v} = ⊤ := by
  have h1 := congrArg IntermediateField.toSubalgebra <|
    (Field.primitive_element_iff_minpoly_natDegree_eq ℚ v).mpr (hv3.trans hdeg.symm)
  rwa [IntermediateField.top_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsAlgebraic.of_finite ℚ v)] at h1

lemma norm_eq_mul_normSq (hdeg : Module.finrank ℚ K = 3) (σ φ : K →+* ℂ)
    (hφ : IsReal φ) (hσ : ¬ IsReal σ) (a : K) :
    Algebra.norm ℚ a = φ a * normSq (σ a) := by
  classical
  obtain ⟨hne1, hne2, hne3⟩ := embeddings_ne hφ hσ
  have huniv : Finset.univ = {φ, σ, conjugate σ} := by
    refine (Finset.eq_univ_of_card _ ?_).symm
    rw [Finset.card_insert_of_notMem (by simp [hne1.symm, hne2.symm]),
        Finset.card_insert_of_notMem (by simp [hne3]), Finset.card_singleton,
        NumberField.Embeddings.card K ℂ, hdeg]
  have hprod : algebraMap ℚ ℂ (Algebra.norm ℚ a) = φ a * (σ a * conjugate σ a) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ a,
        ← Fintype.prod_equiv RingHom.equivRatAlgHom (fun f => f a) (fun τ => τ a)
          (fun _ => by simp [RingHom.equivRatAlgHom_apply]),
        huniv, Finset.prod_insert (by simp [hne1.symm, hne2.symm]),
        Finset.prod_insert (by simp [hne3]), Finset.prod_singleton]
  rw [conjugate_coe_eq, mul_conj] at hprod
  exact_mod_cast hprod

lemma exists_eq_inv_sqrt_mul_exp (hdeg : Module.finrank ℚ K = 3) (σ φ : K →+* ℂ)
    (hφ : IsReal φ) (hσ : ¬ IsReal σ) (a : K) (ha : |Algebra.norm ℚ a| = 1)
    (hpos : 0 < hφ.embedding a) :
    ∃ (t : ℝ), σ a = (Real.sqrt (hφ.embedding a))⁻¹ * exp (I * t) := by
  have hreal : (Algebra.norm ℚ a : ℝ) = hφ.embedding a * normSq (σ a) := by
    have h := norm_eq_mul_normSq hdeg σ φ hφ hσ a
    rw [← hφ.coe_embedding_apply a] at h
    exact_mod_cast h
  have hnorm1 : Algebra.norm ℚ a = 1 := by
    have h0 : 0 ≤ Algebra.norm ℚ a := by
      have hnn : 0 ≤ (Algebra.norm ℚ a : ℝ) := by
        rw [hreal]; exact mul_nonneg hpos.le (normSq_nonneg _)
      exact_mod_cast hnn
    rw [← abs_of_nonneg h0, ha]
  have hnormSq : normSq (σ a) = (hφ.embedding a)⁻¹ := by
    rw [hnorm1] at hreal
    push_cast at hreal
    field_simp
    linarith
  refine ⟨arg (σ a), ?_⟩
  conv_lhs => rw [← norm_mul_exp_arg_mul_I (σ a), norm_def, hnormSq, Real.sqrt_inv]
  congr 2
  ring


lemma algebraMap_discr_eq_sq_prod_sub (hdeg : Module.finrank ℚ K = 3) (σ φ : K →+* ℂ)
    (hφ : IsReal φ) (hσ : ¬ IsReal σ) (v : K)
    (hv3 : (minpoly ℚ v).natDegree = 3) :
    algebraMap ℚ ℂ (Algebra.discr ℚ fun i : Fin 3 => v ^ (i : ℕ)) =
      ((σ v - φ v) * (conjugate σ v - φ v) * (σ v - conjugate σ v)) ^ 2 := by
  classical
  have htop : Algebra.adjoin ℚ {v} = ⊤ := adjoin_eq_top_of_natDegree_minpoly_eq_three hdeg hv3
  let pb := PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite ℚ v) htop
  have hgen : pb.gen = v := PowerBasis.ofAdjoinEqTop_gen ..
  have hdim : pb.dim = 3 := (PowerBasis.ofAdjoinEqTop_dim ..).trans hv3
  obtain ⟨hne1, hne2, hne3⟩ := embeddings_ne hφ hσ
  have hcardK : Fintype.card (K →ₐ[ℚ] ℂ) = 3 := by rw [AlgHom.card, hdeg]
  set e0 : Fin 3 → (K →ₐ[ℚ] ℂ) :=
    ![RingHom.equivRatAlgHom φ, RingHom.equivRatAlgHom σ, RingHom.equivRatAlgHom (conjugate σ)]
    with he0
  have hinj : Function.Injective e0 := by
    intro i j hij
    apply_fun AlgHom.toRingHom at hij
    simp only [he0, RingHom.equivRatAlgHom_apply] at hij
    fin_cases i <;> fin_cases j <;> simp_all [RingHom.toRatAlgHom_toRingHom]
  set e3 := Equiv.ofBijective e0
    ((Fintype.bijective_iff_injective_and_card e0).mpr ⟨hinj, by simp [hcardK]⟩) with he3
  set e := (finCongr hdim).trans e3 with he
  have e0eq : ∀ i, e (finCongr hdim.symm i) = e0 i := fun i => by
    rw [he, Equiv.trans_apply]; congr 1
  have hdiscreq : Algebra.discr ℚ (fun i : Fin 3 => v ^ (i : ℕ)) = Algebra.discr ℚ (⇑pb.basis) := by
    rw [← Algebra.discr_reindex ℚ pb.basis (finCongr hdim)]
    congr 1; funext i; simp [hgen]
  have hcast : ∀ x : Fin 3, finCongr hdim.symm x = (finCongr hdim.symm).toEmbedding x := fun _ => rfl
  have hreindex : ∏ i : Fin 3, ∏ j ∈ Finset.Ioi i, (e (finCongr hdim.symm j) pb.gen -
        e (finCongr hdim.symm i) pb.gen) ^ 2 =
      ∏ i : Fin pb.dim, ∏ j ∈ Finset.Ioi i, (e j pb.gen - e i pb.gen) ^ 2 := by
    refine Fintype.prod_equiv (finCongr hdim.symm) _ _ fun i => ?_
    simp only [hcast]
    rw [← Finset.prod_map (Finset.Ioi i) (finCongr hdim.symm).toEmbedding
      (fun j => (e j pb.gen - e ((finCongr hdim.symm).toEmbedding i) pb.gen) ^ 2)]
    congr 1
    exact Fin.map_finCongr_Ioi hdim.symm i
  rw [hdiscreq, Algebra.discr_powerBasis_eq_prod ℚ ℂ pb e, ← hreindex]
  simp_rw [hgen, e0eq]
  have h0 : Finset.Ioi (0 : Fin 3) = {1, 2} := by decide
  have h1 : Finset.Ioi (1 : Fin 3) = {2} := by decide
  have h2 : Finset.Ioi (2 : Fin 3) = ∅ := by decide
  rw [Fin.prod_univ_three, h0, h1, h2]
  simp only [Finset.prod_insert (by decide : 1 ∉ ({2} : Finset (Fin 3))),
    Finset.prod_singleton, Finset.prod_empty, mul_one, he0]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, RingHom.equivRatAlgHom_apply, RingHom.toRatAlgHom_apply]
  ring

open NumberField


open scoped nonZeroDivisors in

lemma abs_discr_le_abs_discr_cubic_field_order (hdeg : Module.finrank ℚ K = 3) {O : Subalgebra ℤ K}
    (bO : Basis (Fin 3) ℤ O) {v : K} (hv : v ∈ O) (hv3 : (minpoly ℚ v).natDegree = 3) :
    |(Algebra.discr ℤ bO : ℚ)| ≤ |Algebra.discr ℚ fun i : Fin 3 => v ^ (i : ℕ)| := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O ℤ⁰) K :=
    isLocalization_fraction_ring_of_eq_rank hdeg O bO
  set w : O := ⟨v, hv⟩ with hw
  set bK := Basis.localizationLocalization ℚ ℤ⁰ K bO with hbK
  set P := bO.toMatrix (fun i : Fin 3 => w ^ (i : ℕ)) with hP
  have hPv : bK.toMatrix (fun i : Fin 3 => v ^ (i : ℕ)) = P.map (algebraMap ℤ ℚ) := by
    ext i j
    have hvw : v ^ (j : ℕ) = algebraMap O K (w ^ (j : ℕ)) := by simp [hw]
    simp only [Basis.toMatrix_apply, Matrix.map_apply, hbK, hP, hvw,
      Basis.localizationLocalization_repr_algebraMap]
  have hne : Algebra.discr ℚ (fun i : Fin 3 => v ^ (i : ℕ)) ≠ 0 := by
    have htop : Algebra.adjoin ℚ {v} = ⊤ :=
      adjoin_eq_top_of_natDegree_minpoly_eq_three hdeg hv3
    set pb := PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite ℚ v) htop with hpb
    have hgen : pb.gen = v := PowerBasis.ofAdjoinEqTop_gen ..
    have hdiscreq : Algebra.discr ℚ (⇑pb.basis) = Algebra.discr ℚ (fun i : Fin 3 => v ^ (i : ℕ)) := by
      have hdim : pb.dim = 3 := (PowerBasis.ofAdjoinEqTop_dim ..).trans hv3
      rw [← Algebra.discr_reindex ℚ pb.basis (finCongr hdim)]
      congr 1; funext i; simp [hgen]
    rw [← hdiscreq]
    exact Algebra.discr_not_zero_of_basis ℚ pb.basis
  have hdQ : ((Algebra.discr ℤ bO : ℤ) : ℚ) = Algebra.discr ℚ bK := by
    rw [show ((Algebra.discr ℤ bO : ℤ) : ℚ) = algebraMap ℤ ℚ (Algebra.discr ℤ bO) from rfl,
      discr_eq_discr_fraction_field hdeg O bO]
    congr 1
    funext i
    simp [hbK, Basis.localizationLocalization_apply]
  have heq : Algebra.discr ℚ (fun i : Fin 3 => v ^ (i : ℕ))
      = (P.det : ℚ) ^ 2 * ((Algebra.discr ℤ bO : ℤ) : ℚ) := by
    rw [← Basis.toMatrix_map_vecMul bK (fun i : Fin 3 => v ^ (i : ℕ)), hPv,
      Algebra.discr_of_matrix_vecMul, hdQ, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      eq_intCast]
  have hPdet : P.det ≠ 0 := by
    intro h0; rw [heq, h0] at hne; simp at hne
  have hd1 : 1 ≤ (P.det : ℚ) ^ 2 := by
    have h2 : 1 ≤ |(P.det : ℚ)| := by exact_mod_cast Int.one_le_abs hPdet
    nlinarith [sq_abs (P.det : ℚ), abs_nonneg (P.det : ℚ)]
  rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (P.det : ℚ) ^ 2)]
  nlinarith [abs_nonneg ((Algebra.discr ℤ bO : ℤ) : ℚ)]

lemma abs_discr_le_abs_algebraMap_discr_eq_sq_prod_sub (hdeg : Module.finrank ℚ K = 3) (v : K)
    (hv : IsIntegral ℤ v) (hv3 : (minpoly ℚ v).natDegree = 3) :
    |(NumberField.discr K : ℚ)| ≤ |Algebra.discr ℚ fun i : Fin 3 => v ^ (i : ℕ)| := by
  have hrank : Module.finrank ℤ (𝓞 K) = 3 := by rw [NumberField.RingOfIntegers.rank, hdeg]
  let bZ := Module.finBasisOfFinrankEq ℤ (𝓞 K) hrank
  rw [← NumberField.discr_eq_discr K bZ]
  exact abs_discr_le_abs_discr_cubic_field_order hdeg (O := integralClosure ℤ K) bZ hv hv3

open NumberField


lemma natDegree_minpoly_eq_three_of_norm_one (hdeg : Module.finrank ℚ K = 3) {φ : K →+* ℂ} (hφ : IsReal φ)
    {u : K} (hnorm : |Algebra.norm ℚ u| = 1) (hone : 1 < hφ.embedding u) :
    (minpoly ℚ u).natDegree = 3 := by
  have hdvd : (minpoly ℚ u).natDegree ∣ 3 :=
    hdeg ▸ minpoly.degree_dvd (IsIntegral.of_finite ℚ u)
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h1 | h3
  · exfalso
    obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp h1
    rw [← hq, Algebra.norm_algebraMap, hdeg] at hnorm
    have hembed : hφ.embedding u = (q : ℝ) := by rw [← hq, eq_ratCast, map_ratCast]
    rw [hembed] at hone
    have hq1 : 1 < q := by exact_mod_cast hone
    rw [abs_of_pos (by positivity : 0 < q ^ 3)] at hnorm
    nlinarith [mul_pos (sub_pos.mpr hq1) (sub_pos.mpr hq1)]
  · exact h3

lemma natDegree_minpoly_of_isUnit_of_embedding_gt_one {K : Type*} [Field K]
    [NumberField K] (hdeg : Module.finrank ℚ K = 3) {φ : K →+* ℂ} (hφ : IsReal φ)
    {v : 𝓞 K} (hv : IsUnit v) (hvone : 1 < hφ.embedding v) :
    (minpoly ℚ (v : K)).natDegree = 3 :=
  natDegree_minpoly_eq_three_of_norm_one hdeg hφ
    (by have h := NumberField.Units.norm K hv.unit; rwa [IsUnit.unit_spec] at h) hvone

lemma abs_discr_lt_of_one_lt {x t : ℝ} (hx1 : 1 < x) :
    |(-16 * (1 - Real.cos t ^ 2) * ((x ^ 3 + (x⁻¹) ^ 3) / 2 - Real.cos t) ^ 2)|
      < 4 * x ^ 6 + 24 := by
  have hxpos : 0 < x := by linarith
  set aparam := (x ^ 3 + (x⁻¹) ^ 3) / 2 with haparam
  have hcube : 1 < x ^ 3 := one_lt_pow₀ hx1 (by norm_num)
  have haparam1 : 1 < aparam := by
    rw [haparam]
    have hpos3 : 0 < x ^ 3 := by positivity
    have hkey : 0 < x ^ 3 + (x⁻¹) ^ 3 - 2 := by
      have heq : x ^ 3 + (x⁻¹) ^ 3 - 2 = (x ^ 3 - 1) ^ 2 / x ^ 3 := by field_simp; ring
      rw [heq]
      exact div_pos (pow_pos (by linarith) 2) hpos3
    linarith
  have hcontf : ContinuousOn (fun y => 16 * (1 - y ^ 2) * (aparam - y) ^ 2) (Set.Icc (-1:ℝ) 1) := by
    fun_prop
  obtain ⟨y0, hy0mem, hy0max⟩ := IsCompact.exists_isMaxOn isCompact_Icc
    (Set.nonempty_Icc.mpr (by norm_num)) hcontf
  have hy0max' : ∀ y ∈ Set.Icc (-1:ℝ) 1, 16 * (1 - y ^ 2) * (aparam - y) ^ 2 ≤
      16 * (1 - y0 ^ 2) * (aparam - y0) ^ 2 := fun y hy => hy0max hy
  have hkey0 : aparam * y0 = 2 * y0 ^ 2 - 1 := mul_eq_two_mul_sq_sub_one_of_isMaxOn haparam1 hy0mem hy0max'
  have hy0lt1 : y0 < 1 := hy0mem.2.lt_of_ne (by
    rintro rfl
    have h0 := hy0max' 0 (by norm_num)
    nlinarith)
  have hy0lt0 : y0 < 0 := by
    nlinarith [mul_pos (sub_pos.mpr hy0lt1) (sub_pos.mpr hy0lt1)]
  have hy0ne : y0 ≠ 0 := hy0lt0.ne
  have h1 : 2 * y0 ^ 2 + (-aparam) * y0 + (-1) = 0 := by linear_combination -hkey0
  have h2 : 2 * (-1 / (2 * y0)) ^ 2 + (-aparam) * (-1 / (2 * y0)) + (-1) = 0 := by
    field_simp; linear_combination hkey0
  have hlt : y0 < -1 / (2 * y0) := by
    rw [lt_div_iff_of_neg (by linarith : 2 * y0 < 0)]
    nlinarith [sq_nonneg y0]
  have hxinv1 : (x⁻¹) ^ 6 < 1 :=
    calc (x⁻¹) ^ 6 < 1 ^ 6 := by gcongr; exact (inv_lt_one_iff₀).mpr (Or.inr hx1)
      _ = 1 := one_pow 6
  have hy : 2 * (-1 / (2 * x ^ 3)) ^ 2 + (-aparam) * (-1 / (2 * x ^ 3)) + (-1) < 0 := by
    have hx3 : 0 < x ^ 3 := by positivity
    rw [haparam,
      show 2 * (-1 / (2 * x ^ 3)) ^ 2 + -((x ^ 3 + x⁻¹ ^ 3) / 2) * (-1 / (2 * x ^ 3)) + -1 =
        (3 / 4) * (x⁻¹ ^ 6 - 1) by field_simp; ring]
    linarith
  have hmemIoo := mem_Ioo_of_quadratic_neg (a := 2) (x₁ := y0) (x₂ := -1 / (2 * y0))
    (by norm_num) h1 h2 hlt hy
  have hx3 : 0 < x ^ 3 := by positivity
  have hxinvlt : (x⁻¹) ^ 6 < 4 * y0 ^ 2 := by
    have hlt2 := hmemIoo.1
    rw [lt_div_iff₀ (by linarith : 0 < 2 * x ^ 3)] at hlt2
    rw [inv_pow, inv_lt_iff_one_lt_mul₀ (by positivity : 0 < x ^ 6)]
    have hz : 1 < -(y0 * (2 * x ^ 3)) := by linarith
    calc 1 < (-(y0 * (2 * x ^ 3))) ^ 2 := one_lt_pow₀ hz (by norm_num)
      _ = _ := by ring
  have hexpand : 16 * (1 - y0 ^ 2) * (aparam - y0) ^ 2 = 16 * (aparam ^ 2 + 1 - y0 ^ 4 - y0 ^ 2) := by
    linear_combination (-16 * (aparam * y0 + 1)) * hkey0
  have hsubst : 16 * (aparam ^ 2 + 1 - y0 ^ 4 - y0 ^ 2) =
      4 * x ^ 6 + 24 + 4 * ((x⁻¹) ^ 6 - 4 * y0 ^ 4 - 4 * y0 ^ 2) := by
    rw [haparam]; field_simp; ring
  have hcosmem : Real.cos t ∈ Set.Icc (-1:ℝ) 1 := ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
  have hy04 : 0 ≤ y0 ^ 4 := by positivity
  have hcossq : 0 ≤ 1 - Real.cos t ^ 2 := by linarith [Real.cos_sq_le_one t]
  have habs_nonpos : -16 * (1 - Real.cos t ^ 2) * (aparam - Real.cos t) ^ 2 ≤ 0 := by
    have h3 : 0 ≤ 16 * (1 - Real.cos t ^ 2) * (aparam - Real.cos t) ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hcossq) (sq_nonneg _)
    linarith
  rw [abs_of_nonpos habs_nonpos]
  calc -(-16 * (1 - Real.cos t ^ 2) * ((x ^ 3 + x⁻¹ ^ 3) / 2 - Real.cos t) ^ 2)
      = 16 * (1 - Real.cos t ^ 2) * (aparam - Real.cos t) ^ 2 := by rw [haparam]; ring
    _ ≤ 16 * (1 - y0 ^ 2) * (aparam - y0) ^ 2 := hy0max' (Real.cos t) hcosmem
    _ = 16 * (aparam ^ 2 + 1 - y0 ^ 4 - y0 ^ 2) := hexpand
    _ = 4 * x ^ 6 + 24 + 4 * ((x⁻¹) ^ 6 - 4 * y0 ^ 4 - 4 * y0 ^ 2) := hsubst
    _ < 4 * x ^ 6 + 24 := by linarith [hxinvlt, hy04]


lemma abs_norm_units_order {O : Subalgebra ℤ K}
    {ι : Type*} [Fintype ι] (bO : Basis ι ℤ O) (u : Oˣ) :
    |Algebra.norm ℚ ((u : O) : K)| = 1 :=
  NumberField.Units.norm K
    (Units.map (Subalgebra.inclusion (le_integralClosure_of_basis O bO)).toMonoidHom u)

lemma natDegree_minpoly_of_units_order (hdeg : Module.finrank ℚ K = 3) {φ : K →+* ℂ} (hφ : IsReal φ)
    {O : Subalgebra ℤ K} (bO : Basis (Fin 3) ℤ O) (v : Oˣ)
    (hvone : 1 < hφ.embedding v) :
    (minpoly ℚ (v  : K)).natDegree = 3 :=
  natDegree_minpoly_eq_three_of_norm_one hdeg hφ (abs_norm_units_order bO v) hvone


theorem artin_inequality_order (hdeg : Module.finrank ℚ K = 3) {σ φ : K →+* ℂ}
    (hφ : IsReal φ) (hσ : ¬ IsReal σ) {O : Subalgebra ℤ K} (bO : Basis (Fin 3) ℤ O)
    (v : Oˣ) (hvone : 1 < hφ.embedding v) :
    |Algebra.discr ℤ bO| < 4 * (hφ.embedding v) ^ 3 + 24 := by
  set u : K := ↑v with hu
  have hv3 := natDegree_minpoly_of_units_order hdeg hφ bO v hvone
  have hdisc1 := abs_discr_le_abs_discr_cubic_field_order hdeg bO (v : O).2 hv3
  have hnormu : |Algebra.norm ℚ u| = 1 := abs_norm_units_order bO v
  obtain ⟨t, hpol⟩ := exists_eq_inv_sqrt_mul_exp hdeg σ φ hφ hσ u hnormu (by linarith : 0 < hφ.embedding u)
  push_cast at hpol
  set x := Real.sqrt (hφ.embedding u) with hxdef
  have hxpos : 0 < x := Real.sqrt_pos.mpr (by linarith)
  have hxsq : x ^ 2 = hφ.embedding u := Real.sq_sqrt (by linarith)
  have hx1 : 1 < x := by nlinarith [hxsq]
  have hxne : x ≠ 0 := hxpos.ne'
  have hdc := algebraMap_discr_eq_sq_prod_sub hdeg σ φ hφ hσ u hv3
  have hφa : φ u = (x : ℂ) ^ 2 := by
    rw [← hφ.coe_embedding_apply u, ← hxsq]; push_cast; ring
  have hconjσ : conjugate σ u = (x : ℂ)⁻¹ * exp (-I * t) := by
    rw [conjugate_coe_eq, hpol, map_mul, map_inv₀, conj_ofReal, ← exp_conj,
      map_mul, conj_I, conj_ofReal, neg_mul]
  have hDeq : algebraMap ℚ ℂ (Algebra.discr ℚ fun i : Fin 3 => u ^ (i : ℕ)) =
      ((x⁻¹ * exp (I * t) - x ^ 2) *
          (x⁻¹ * exp (-I * t) - x ^ 2) *
        (x⁻¹ * exp (I * t) - x⁻¹ * exp (-I * t))) ^ 2 := by
    rw [hdc, hpol, hφa, hconjσ]; push_cast; ring
  have hDreal : (Algebra.discr ℚ fun i : Fin 3 => u ^ (i : ℕ) : ℝ) =
      -16 * (1 - Real.cos t ^ 2) * ((x ^ 3 + (x⁻¹) ^ 3) / 2 - Real.cos t) ^ 2 := by
    have hcast := hDeq.trans (sq_prod_sub_exp_eq_neg_cos_sq hxne t)
    rw [eq_ratCast] at hcast
    exact_mod_cast hcast
  calc ((|Algebra.discr ℤ bO| : ℤ) : ℝ)
      ≤ |(Algebra.discr ℚ fun i : Fin 3 => u ^ (i : ℕ) : ℝ)| := by exact_mod_cast hdisc1
    _ < 4 * x ^ 6 + 24 := by rw [hDreal]; exact abs_discr_lt_of_one_lt hx1
    _ = 4 * (hφ.embedding u) ^ 3 + 24 := by rw [← hxsq]; ring


theorem artin_inequality (hdeg : Module.finrank ℚ K = 3) (σ φ : K →+* ℂ)
    (hφ : IsReal φ) (hσ : ¬ IsReal σ) (v : (𝓞 K)ˣ)
    (hvone : 1 < hφ.embedding v) :
    |NumberField.discr K| < 4 * (hφ.embedding v) ^ 3 + 24 := by
  have hrank : Module.finrank ℤ (𝓞 K) = 3 := by rw [RingOfIntegers.rank, hdeg]
  let bZ := Module.finBasisOfFinrankEq ℤ (𝓞 K) hrank
  rw [← NumberField.discr_eq_discr K bZ]
  exact artin_inequality_order hdeg hφ hσ (O := integralClosure ℤ K) bZ v hvone

theorem artin_inequality'_order (hdeg : Module.finrank ℚ K = 3) (σ φ : K →+* ℂ)
    (hφ : IsReal φ) (hσ : ¬ IsReal σ) {O : Subalgebra ℤ K} (bO : Basis (Fin 3) ℤ O)
    (v : Oˣ) (hvone : 1 < hφ.embedding v) (B : ℚ)
    (hB : B ^ 3 ≤ ((|Algebra.discr ℤ bO| : ℚ) - 24) / 4) :
    B < hφ.embedding v := by
  have h := artin_inequality_order hdeg hφ hσ bO v hvone
  have hvpos : 0 ≤ hφ.embedding v := by linarith
  have hB' : (B : ℝ) ^ 3 < (hφ.embedding v) ^ 3 := by
    have hBr : (B : ℝ) ^ 3 ≤ (((|Algebra.discr ℤ bO| : ℤ) : ℝ) - 24) / 4 := by
      exact_mod_cast hB
    linarith
  exact lt_of_pow_lt_pow_left₀ 3 hvpos hB'

theorem artin_inequality' (hdeg : Module.finrank ℚ K = 3) (σ φ : K →+* ℂ)
    (hφ : IsReal φ) (hσ : ¬ IsReal σ) (v : (𝓞 K)ˣ)
    (hvone : 1 < hφ.embedding v) (B : ℚ)
    (hB : B ^ 3 ≤ (|(NumberField.discr K : ℚ)| - 24) / 4) :
    B < hφ.embedding v := by
  have hrank : Module.finrank ℤ (𝓞 K) = 3 := by rw [RingOfIntegers.rank, hdeg]
  let bZ := Module.finBasisOfFinrankEq ℤ (𝓞 K) hrank
  rw [← NumberField.discr_eq_discr K bZ] at hB
  exact artin_inequality'_order hdeg σ φ hφ hσ (O := integralClosure ℤ K) bZ v hvone B hB

theorem artin_inequality_bound_index_order (hdeg : Module.finrank ℚ K = 3) (σ φ : K →+* ℂ)
    (hφ : IsReal φ) (hσ : ¬ IsReal σ) {O : Subalgebra ℤ K} (bO : Basis (Fin 3) ℤ O)
    (v w : Oˣ) (hvone : 1 < hφ.embedding v) (a b c d : ℕ)
    (ha : 0 < a) (hd : 0 < d)
    (hdisc : 24 ≤ |Algebra.discr ℤ bO|)
    (hB : 8 ^ a ≤ (((↑|Algebra.discr ℤ bO| : ℚ) - 24) / 4) ^ b)
    (hw : |hφ.embedding w| ^ d ≤ 2 ^ c) {k : ℕ}
    (hvw : w = v ^ k ∨ w = -v ^ k) :
    0 ≤ k ∧ k ≤ (c * b) / (a * d) := by
  refine ⟨Nat.zero_le k, ?_⟩
  set V := hφ.embedding v with hVdef
  have hVpos : 0 ≤ V := by linarith
  have hstep1 : 2 ^ (3 * a) ≤ V ^ (3 * b) := by
    have hnonneg : 0 ≤ (((|Algebra.discr ℤ bO| : ℤ) : ℝ) - 24) / 4 := by
      have : 24 ≤ ((|Algebra.discr ℤ bO| : ℤ) : ℝ) := by exact_mod_cast hdisc
      linarith
    have hle3 : (((|Algebra.discr ℤ bO| : ℤ) : ℝ) - 24) / 4 ≤ V ^ 3 := by
      linarith [artin_inequality_order hdeg hφ hσ bO v hvone]
    calc 2 ^ (3 * a) = 8 ^ a := by rw [pow_mul]; norm_num
      _ ≤ ((((|Algebra.discr ℤ bO| : ℤ) : ℝ) - 24) / 4) ^ b := by exact_mod_cast hB
      _ ≤ (V ^ 3) ^ b := by gcongr
      _ = V ^ (3 * b) := by rw [← pow_mul]
  have hstep2 : V ^ (k * d) ≤ 2 ^ c := by
    -- `|φ w| = V ^ k` in both branches of `hvw`; no sign hypothesis on `w` is needed
    have hWeq : |hφ.embedding ((w : O) : K)| = V ^ k := by
      rcases hvw with h | h <;>
        simp [h, Units.val_pow_eq_pow_val, map_pow, ← hVdef, abs_of_nonneg (pow_nonneg hVpos k)]
    rw [pow_mul, ← hWeq]
    exact hw
  have hfinal1 : 2 ^ (3 * a * (d * k)) ≤ V ^ (3 * b * (d * k)) := by
    simpa [← pow_mul] using pow_le_pow_left₀ (by positivity) hstep1 (d * k)
  have hfinal2 : V ^ (3 * b * (d * k)) ≤ 2 ^ (3 * b * c) := by
    simpa [← pow_mul, mul_comm, mul_assoc, mul_left_comm] using
      pow_le_pow_left₀ (by positivity) hstep2 (3 * b)
  have hchain := hfinal1.trans hfinal2
  have hexp : 3 * a * (d * k) ≤ 3 * b * c := by
    rwa [pow_le_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)] at hchain
  exact (Nat.le_div_iff_mul_le (mul_pos ha hd)).mpr (by nlinarith [hexp])

theorem artin_inequality_bound_index (hdeg : Module.finrank ℚ K = 3) (σ φ : K →+* ℂ)
    (hφ : IsReal φ) (hσ : ¬ IsReal σ) (v w : (𝓞 K)ˣ)
    (hvone : 1 < hφ.embedding v) (a b c d : ℕ)
    (ha : 0 < a) (hd : 0 < d)
    (hdisc : 24 ≤ |NumberField.discr K|)
    (hB : 8 ^ a ≤ (((↑|NumberField.discr K| : ℚ) - 24) / 4) ^ b )
    (hw : |hφ.embedding w| ^ d ≤ 2 ^ c) {k : ℕ}
    (hvw : w = v ^ k ∨ w = - v ^ k) :
    0 ≤ k ∧ k ≤ (c * b) / (a * d) := by
  have hrank : Module.finrank ℤ (𝓞 K) = 3 := by rw [RingOfIntegers.rank, hdeg]
  let bZ := Module.finBasisOfFinrankEq ℤ (𝓞 K) hrank
  rw [← NumberField.discr_eq_discr K bZ] at hdisc hB
  exact artin_inequality_bound_index_order hdeg σ φ hφ hσ (O := integralClosure ℤ K) bZ
    v w hvone a b c d ha hd hdisc hB hw (k := k) hvw

open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace in

lemma exists_fundamental_unit (hdeg : Module.finrank ℚ K = 3) (σ φ : K →+* ℂ)
    (hφ : IsReal φ) (hσ : ¬ IsReal σ) :
    ∃ v : (𝓞 K)ˣ, 1 < hφ.embedding v ∧
      ∀ w : (𝓞 K)ˣ, ∃ k : ℤ, w = v ^ k ∨ w = -v ^ k := by
  classical
  have hrank1 : rank K = 1 := by
    have h1 : 0 < Fintype.card {ψ : K →+* ℂ // ¬ NumberField.ComplexEmbedding.IsReal ψ} :=
      Fintype.card_pos_iff.mpr ⟨⟨σ, hσ⟩⟩
    have h2 := card_complex_embeddings K
    have h3 := card_add_two_mul_card_eq_rank K
    have h4 := card_eq_nrRealPlaces_add_nrComplexPlaces K
    simp only [rank, hdeg] at *
    omega
  letI : Unique (Fin (rank K)) :=
    ⟨⟨⟨0, hrank1 ▸ Nat.one_pos⟩⟩, fun i => Fin.ext (by have := i.isLt; omega)⟩
  set ε₀ := fundSystem K default with hε₀
  have hgen : ∀ w : (𝓞 K)ˣ, ∃ (ζ : (𝓞 K)ˣ) (e : ℤ),
      ζ * ζ = 1 ∧ w = ζ * ε₀ ^ e := by
    intro w
    obtain ⟨⟨⟨ζ, hζ⟩, e⟩, heq, -⟩ := exist_unique_eq_mul_prod K w
    rw [Fintype.prod_unique] at heq
    refine ⟨ζ, e default, ?_, heq⟩
    rcases torsion_eq_one_or_neg_one_of_odd_finrank (hdeg ▸ (by decide : Odd 3)) ⟨ζ, hζ⟩ with h | h
    · have h' : ζ = 1 := h; rw [h', one_mul]
    · have h' : ζ = -1 := h; rw [h']; norm_num
  -- any power of a "sign" is again a "sign"
  have hsq_zpow : ∀ (c : (𝓞 K)ˣ), c * c = 1 → ∀ n : ℤ, c ^ n * c ^ n = 1 := by
    intro c hc n
    rw [← zpow_two, ← zpow_mul, mul_comm, zpow_mul, zpow_two, hc, one_zpow]
  -- convert generation by `ε₀` into generation by any `v` with `ε₀ = c * v ^ s`, `c * c = 1`
  have hconv : ∀ (v c : (𝓞 K)ˣ) (s : ℤ), c * c = 1 → ε₀ = c * v ^ s →
      ∀ w : (𝓞 K)ˣ, ∃ k : ℤ, w = v ^ k ∨ w = -v ^ k := by
    intro v c s hc hcs w
    obtain ⟨ζ, e, hζ, hw⟩ := hgen w
    have h1u : (ζ * c ^ e) * (ζ * c ^ e) = 1 := by
      rw [mul_mul_mul_comm, hζ, hsq_zpow c hc e, one_mul]
    have h1 : ((ζ * c ^ e : (𝓞 K)ˣ) : 𝓞 K) *
        ((ζ * c ^ e : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
      rw [← Units.val_mul, h1u, Units.val_one]
    rcases mul_self_eq_one_iff.mp h1 with h | h
    · have hu : ζ * c ^ e = 1 := Units.ext h
      exact ⟨s * e, Or.inl (by rw [hw, hcs, mul_zpow, ← zpow_mul, ← mul_assoc, hu, one_mul])⟩
    · have hu : ζ * c ^ e = -1 := Units.ext (by simpa using h)
      exact ⟨s * e, Or.inr (by rw [hw, hcs, mul_zpow, ← zpow_mul, ← mul_assoc, hu, neg_one_mul])⟩
  -- pick the branch (`ε₀`, `ε₀⁻¹`, `-ε₀` or `-ε₀⁻¹`) whose embedding exceeds `1`
  set x := hφ.embedding (ε₀ : K) with hxdef
  have hxne : x ≠ 0 := by
    rw [hxdef]
    exact fun h => (RingOfIntegers.coe_ne_zero_iff.mpr ε₀.ne_zero)
      ((map_eq_zero_iff hφ.embedding hφ.embedding.injective).mp h)
  set ε₀i : (𝓞 K)ˣ := ε₀⁻¹ with hε₀idef
  have hinv : hφ.embedding (ε₀i : K) = x⁻¹ := by
    have h1 : hφ.embedding (ε₀i : K) * x = 1 := by
      rw [hxdef, ← map_mul]
      have hc : (ε₀i : K) * (ε₀ : K) = 1 := by rw [hε₀idef]; exact_mod_cast Units.inv_mul ε₀
      rw [hc, map_one]
    exact eq_inv_of_mul_eq_one_left h1
  have hnegcoe : ∀ u : (𝓞 K)ˣ, ((-u : (𝓞 K)ˣ) : K) = -(u : K) := by
    intro u; push_cast; ring
  have hε0_not_torsion : ε₀ ∉ torsion K := by
    rw [← logEmbedding_eq_zero_iff, hε₀, logEmbedding_fundSystem]
    simpa using (basisUnitLattice K).ne_zero default
  have hcompinj : Function.Injective (fun r : 𝓞 K => hφ.embedding (r : K)) :=
    hφ.embedding.injective.comp RingOfIntegers.coe_injective
  have hx1 : x ≠ 1 := by
    intro h
    apply hε0_not_torsion
    have h2 : ε₀ = 1 := Units.ext (hcompinj (by rw [hxdef] at h; simpa using h))
    rw [h2]; exact one_mem _
  have hxm1 : x ≠ -1 := by
    intro h
    apply hε0_not_torsion
    have h2 : ε₀ = -1 := Units.ext (hcompinj (by rw [hxdef] at h; simpa using h))
    rw [h2]; exact neg_one_mem_torsion
  rcases lt_or_ge x 0 with hxneg | hxpos
  · rcases lt_or_ge x (-1) with hlt | hge
    · refine ⟨-ε₀, ?_, hconv (-ε₀) (-1) 1 (by norm_num) (by rw [zpow_one]; simp)⟩
      have he : hφ.embedding ((-ε₀ : (𝓞 K)ˣ) : K) = -x := by
        simp only [hnegcoe, map_neg, ← hxdef]
      rw [he]; linarith
    · have hgt : -1 < x := lt_of_le_of_ne hge (Ne.symm hxm1)
      refine ⟨-ε₀i, ?_, hconv (-ε₀i) (-1) (-1) (by norm_num) (by
        rw [hε₀idef, zpow_neg_one, inv_neg, inv_inv]; simp)⟩
      have he : hφ.embedding ((-ε₀i : (𝓞 K)ˣ) : K) = -x⁻¹ := by
        simp only [hnegcoe, map_neg, hinv]
      rw [he, lt_neg, inv_eq_one_div, div_lt_iff_of_neg hxneg]
      linarith
  · rcases lt_or_ge x 1 with hlt | hge
    · refine ⟨ε₀i, ?_, hconv ε₀i 1 (-1) (by norm_num) (by rw [hε₀idef, zpow_neg_one, inv_inv, one_mul])⟩
      have hxpos' : 0 < x := lt_of_le_of_ne hxpos (Ne.symm hxne)
      rw [hinv, inv_eq_one_div, lt_div_iff₀ hxpos']
      linarith
    · have hgt : 1 < x := lt_of_le_of_ne hge (Ne.symm hx1)
      exact ⟨ε₀, by rw [← hxdef]; linarith, hconv ε₀ 1 1 (by norm_num) (by rw [zpow_one, one_mul])⟩

lemma units_pow_of_pMaximalUnitsCertificateNDvdT {O : Subalgebra ℤ K} (heqO : O = integralClosure ℤ K)
    (w : Oˣ) {p : ℕ}
    (A : pMaximalUnitsCertificateNDvdT O p) (hAr : A.r = 1) (hAu : ∀ i, A.u i = (w : O)) :
    ∀ u : Oˣ, ∃ (e : ℤ) (t : Oˣ), u = w ^ e * t ^ p := by
  subst heqO
  haveI : Module.Finite ℤ (Additive ((integralClosure ℤ K)ˣ ⧸ CommGroup.torsion (integralClosure ℤ K)ˣ)) :=
    NumberField.Units.instFiniteIntAdditiveQuotientUnitsRingOfIntegersSubgroupTorsion K
  haveI : Module.Free ℤ (Additive ((integralClosure ℤ K)ˣ ⧸ CommGroup.torsion (integralClosure ℤ K)ˣ)) :=
    NumberField.Units.instFreeIntAdditiveQuotientUnitsRingOfIntegersSubgroupTorsion K
  haveI hUniq : Unique (Fin A.r) := by rw [hAr]; infer_instance
  intro u
  obtain ⟨e, t, hx⟩ := units_of_pMaximalUnitsCertificateNDvdT A u
  rw [Fintype.prod_unique] at hx
  have hueq : (A.hu (default : Fin A.r)).unit = w := Units.ext (by rw [IsUnit.unit_spec, hAu])
  rw [hueq] at hx
  exact ⟨e default, t, hx⟩

open NumberField.Units in

lemma units_pow_of_pMaximalUnitsCertificateDvdT (hdeg : Module.finrank ℚ K = 3)
    {O : Subalgebra ℤ K} (heqO : O = integralClosure ℤ K)
    (w : Oˣ) {p : ℕ}
    (A : pMaximalUnitsCertificateDvdT O p) (hAr : A.r = 1) (hAu : ∀ i, A.u i = (w : O)) :
    ∀ u : Oˣ, ∃ (e : ℤ) (t : Oˣ), u = w ^ e * t ^ p ∨ u = -w ^ e * t ^ p := by
  subst heqO
  haveI : Module.Finite ℤ (Additive ((integralClosure ℤ K)ˣ ⧸ CommGroup.torsion (integralClosure ℤ K)ˣ)) :=
    NumberField.Units.instFiniteIntAdditiveQuotientUnitsRingOfIntegersSubgroupTorsion K
  haveI : Module.Free ℤ (Additive ((integralClosure ℤ K)ˣ ⧸ CommGroup.torsion (integralClosure ℤ K)ˣ)) :=
    NumberField.Units.instFreeIntAdditiveQuotientUnitsRingOfIntegersSubgroupTorsion K
  haveI : IsCyclic ↥(CommGroup.torsion (integralClosure ℤ K)ˣ) :=
    NumberField.Units.instIsCyclicSubtypeUnitsRingOfIntegersMemSubgroupTorsion K
  haveI hUniq : Unique (Fin A.r) := by rw [hAr]; infer_instance
  intro u
  obtain ⟨e, t, hx⟩ := units_of_pMaximalUnitsCertificateDvdT A u
  rw [Fintype.prod_sum_type] at hx
  simp only [Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique] at hx
  have hueq : (A.hu (default : Fin A.r)).unit = w := Units.ext (by rw [IsUnit.unit_spec, hAu])
  set τ := (IsUnit.of_pow_eq_one A.hmv A.hm).unit
  have hτmem : τ ∈ CommGroup.torsion (integralClosure ℤ K)ˣ := by
    rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    refine ⟨A.m, Nat.pos_of_ne_zero A.hm, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, A.hmv, Units.val_one]
  rw [hueq] at hx
  rcases torsion_eq_one_or_neg_one_of_odd_finrank (hdeg ▸ (by decide : Odd 3))
    (⟨(τ : (𝓞 K)ˣ), hτmem⟩ : CommGroup.torsion (𝓞 K)ˣ) with h | h
  · have hτ1 : τ = 1 := h
    rw [hτ1, one_zpow, mul_one] at hx
    exact ⟨e (Sum.inl default), t, Or.inl hx⟩
  · have hτ1 : τ = -1 := h
    rw [hτ1, neg_one_zpow_eq_ite] at hx
    by_cases he2 : Even (e (Sum.inr default))
    · rw [if_pos he2, mul_one] at hx
      exact ⟨e (Sum.inl default), t, Or.inl hx⟩
    · rw [if_neg he2, mul_neg_one] at hx
      exact ⟨e (Sum.inl default), t, Or.inr hx⟩

theorem artin_inequality_bound_index_aux (hdeg : Module.finrank ℚ K = 3) (σ φ : K →+* ℂ)
    (hφ : IsReal φ) (hσ : ¬ IsReal σ) (w : (𝓞 K)ˣ) (a b c d : ℕ)
    (ha : 0 < a) (hd : 0 < d)
    (hdisc : 24 ≤ |NumberField.discr K|)
    (hB : 8 ^ a ≤ (((↑|NumberField.discr K| : ℚ) - 24) / 4) ^ b )
    (hwone : 1 < hφ.embedding w)
    (hw : (hφ.embedding w) ^ d ≤ 2 ^ c)
    (hp : ∀ p, Nat.Prime p → p ≤ (c * b) / (a * d) →
      ∀ u : (𝓞 K)ˣ, ∃ (e : ℤ) (t : (𝓞 K)ˣ),
        u = w ^ e * t ^ p ∨ u = -w ^ e * t ^ p) :
    ∀ u : (𝓞 K)ˣ, ∃ n : ℤ, u = w ^ n ∨ u = -w ^ n := by
  have hemb_zpow : ∀ (u : (𝓞 K)ˣ) (n : ℤ),
      hφ.embedding ((u ^ n : (𝓞 K)ˣ) : K) = (hφ.embedding (u : K)) ^ n := by
    intro u n
    rcases n with n | n
    · simp [zpow_natCast, map_pow]
    · simp [zpow_negSucc, map_inv₀, map_pow]
  obtain ⟨v, hvone, hvgen⟩ := exists_fundamental_unit hdeg σ φ hφ hσ
  have hVpos : 0 < hφ.embedding v := by linarith
  -- `w = v ^ k'` for some `k' : ℤ` (the `-v ^ k'` branch is impossible since `φ(w) > 0`)
  obtain ⟨k', hk'⟩ := hvgen w
  have hwv_zpow : w = v ^ k' := by
    rcases hk' with h | h
    · exact h
    · exfalso
      rw [h] at hwone
      simp only [Units.val_neg, map_neg, hemb_zpow] at hwone
      nlinarith [zpow_pos hVpos k']
  have hwv : hφ.embedding (w : K) = (hφ.embedding (v : K)) ^ k' := by rw [hwv_zpow, hemb_zpow]
  -- `k' > 0`
  have hk'pos : 0 < k' := by
    by_contra hle
    have := zpow_le_one_of_nonpos₀ hvone.le (not_lt.mp hle)
    linarith [hwv ▸ hwone]
  -- write `k' = (k : ℤ)` for a natural `k`, so `w = v ^ k` (natural power of units)
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hk'pos.le
  have hwv_units : w = v ^ k := by rw [hwv_zpow, hk, zpow_natCast]
  -- bound `k` using `artin_inequality_bound_index`
  -- `hwone` gives `φ w > 0`, so `|φ w| = φ w` and the general form above applies
  have hwabs : |hφ.embedding (w : K)| ^ d ≤ 2 ^ c := by
    rwa [abs_of_pos (by linarith : 0 < hφ.embedding (w : K))]
  have hkbound : k ≤ (c * b) / (a * d) :=
    (artin_inequality_bound_index hdeg σ φ hφ hσ v w hvone a b c d ha hd hdisc hB hwabs
      (k := k) (Or.inl hwv_units)).2
  -- the meat: if `k > 1` it has a prime factor `p`, giving `1 = p * (m + r)` -- absurd
  have hk1 : k = 1 := by
    by_contra hne
    have hkpos : 0 < k := by omega
    obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hple : p ≤ (c * b) / (a * d) := (Nat.le_of_dvd hkpos hpdvd).trans hkbound
    obtain ⟨m, hm⟩ := hpdvd
    set V := hφ.embedding (v : K) with hVdef
    have hWreal : hφ.embedding (w : K) = V ^ ((p : ℤ) * (m : ℤ)) := by
      rw [hwv, hk]; congr 1; exact_mod_cast hm
    obtain ⟨e, t, ht⟩ := hp p hpprime hple v
    obtain ⟨r, htr⟩ := hvgen t
    have hVt : |hφ.embedding (t : K)| = V ^ r := by
      rcases htr with h | h <;> simp [h, map_neg, hemb_zpow, ← hVdef, abs_of_pos hVpos]
    have hWabs : |hφ.embedding (w : K)| = V ^ ((p : ℤ) * (m : ℤ)) := by
      rw [hWreal]; exact abs_of_pos (zpow_pos hVpos _)
    have habsv : |hφ.embedding (v : K)| =
        |hφ.embedding (w : K)| ^ e * |hφ.embedding (t : K)| ^ p := by
      rcases ht with h | h <;>
        simp [h, map_mul, map_pow, map_neg, abs_mul, abs_neg, hemb_zpow, abs_zpow]
    rw [abs_of_pos hVpos, hWabs, hVt, ← zpow_natCast (V ^ r) p, ← zpow_mul, ← zpow_mul,
      ← zpow_add₀ hVpos.ne'] at habsv
    have hVeq : V ^ (1 : ℤ) = V ^ ((p : ℤ) * (m : ℤ) * e + r * (p : ℤ)) := by
      rw [zpow_one]; exact habsv
    have h1 : 1 = (p : ℤ) * (m : ℤ) * e + r * (p : ℤ) :=
      (zpow_right_inj₀ hVpos (by linarith [hvone])).mp hVeq
    have : (p : ℤ) ∣ 1 := ⟨m * e + r, by linarith⟩
    have := Int.isUnit_iff.mp (isUnit_of_dvd_one this)
    have := hpprime.two_le
    omega
  rw [hk1, pow_one] at hwv_units
  rw [hwv_units]
  exact hvgen

theorem artin_inequality_bound_index' (hdeg : Module.finrank ℚ K = 3) (σ φ : K →+* ℂ)
    (hφ : IsReal φ) (hσ : ¬ IsReal σ)
    {O : Subalgebra ℤ K} (heqO : O = integralClosure ℤ K)
    (w : Oˣ) (a b c d : ℕ)
    (ha : 0 < a) (hd : 0 < d)
    (hdisc : 24 ≤ |NumberField.discr K|)
    (hB : 8 ^ a ≤ (((↑|NumberField.discr K| : ℚ) - 24) / 4) ^ b )
    (hwone : 1 < hφ.embedding w)
    (hw : (hφ.embedding w) ^ d ≤ 2 ^ c)
    (hp : ∀ p, Nat.Prime p → p ≤ (c * b) / (a * d) →
      ∀ u : Oˣ, ∃ (e : ℤ) (t : Oˣ), u = w ^ e * t ^ p ∨ u = -w ^ e * t ^ p) :
    ∀ u : Oˣ, ∃ n : ℤ, u = w ^ n ∨ u = -w ^ n := by
  subst heqO
  exact artin_inequality_bound_index_aux hdeg σ φ hφ hσ w a b c d ha hd hdisc hB hwone hw hp

theorem artin_inequality_bound_index'' (hdeg : Module.finrank ℚ K = 3) (σ φ : K →+* ℂ)
    (hφ : IsReal φ) (hσ : ¬ IsReal σ)
    {O : Subalgebra ℤ K} (heqO : O = integralClosure ℤ K)
    (w : Oˣ) (W : (𝓞 K)ˣ) (hWw : (W : K) = (w : K)) (a b c d : ℕ)
    (ha : 0 < a) (hd : 0 < d)
    (hdisc : 24 ≤ |NumberField.discr K|)
    (hB : 8 ^ a ≤ (((↑|NumberField.discr K| : ℚ) - 24) / 4) ^ b )
    (hwone : 1 < hφ.embedding w)
    (hw : (hφ.embedding w) ^ d ≤ 2 ^ c)
    (hp : ∀ p, Nat.Prime p → p ≤ (c * b) / (a * d) →
      ∀ u : Oˣ, ∃ (e : ℤ) (t : Oˣ), u = w ^ e * t ^ p ∨ u = -w ^ e * t ^ p) :
    ∀ u : (𝓞 K)ˣ, ∃ n : ℤ, u = W ^ n ∨ u = -W ^ n := by
  subst heqO
  have hWeq : W = w := Units.ext (Subtype.ext hWw)
  subst hWeq
  exact artin_inequality_bound_index_aux hdeg σ φ hφ hσ W a b c d ha hd hdisc hB hwone hw hp
