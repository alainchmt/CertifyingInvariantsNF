import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

open Finset Polynomial

/- # Image under a real embedding of cubic fields

This files contains results for approximating the image under a real embedding
of an element in a cubic number field. This is done by approximating a real root of
the defining polynomial using the intermediate value theorem.

## AI use
The specifications of lemmas and theorems were mostly human-written
(with small later modifications by the model) while the proofs were done
mainly with Sonnet 5, and later Opus 5 for refinements, with the strategy specified by me.
We also carried out some polishing afterwards.

## Main Definitions:
- `realEmbeddingOfRealRootCubic` : a real embedding coming from the application of the
intermediate value theorem around a root of a defining polynomial.

## Main Results
- `Polynomial.abs_eval_sub_le`: bound the difference of polynomial evaluation.
- `realEmbeddingOfRealRootCubic_bound_le` : an upper bound for the value under a real embedding.
- `realEmbeddingOfRealRootCubic_bound_ge` : a lower bound for the value under a real embedding.

-/

theorem AbsoluteValue.pow_sub_pow_le {R S : Type*} [CommRing R] [Nontrivial R] [CommSemiring S]
    [PartialOrder S] [IsOrderedRing S] [IsDomain S] (v : AbsoluteValue R S) {x r : R} {B : S}
    (hx : v x ≤ B) (hr : v r ≤ B) (n : ℕ) :
    v (x ^ n - r ^ n) ≤ n * B ^ (n - 1) * v (x - r) := by
  rw [← geom_sum₂_mul x r n, map_mul]
  refine mul_le_mul_of_nonneg_right ?_ (v.nonneg _)
  calc v (∑ i ∈ range n, x ^ i * r ^ (n - 1 - i))
      ≤ ∑ i ∈ range n, v (x ^ i * r ^ (n - 1 - i)) := v.sum_le _ _
    _ = ∑ i ∈ range n, v x ^ i * v r ^ (n - 1 - i) := by
        refine sum_congr rfl fun i _ => ?_
        rw [map_mul, v.map_pow, v.map_pow]
    _ ≤ ∑ i ∈ range n, B ^ i * B ^ (n - 1 - i) := by
        refine sum_le_sum fun i _ => ?_
        exact mul_le_mul (pow_le_pow_left₀ (v.nonneg x) hx i) (pow_le_pow_left₀ (v.nonneg r) hr _)
          (pow_nonneg (v.nonneg r) _) (pow_nonneg ((v.nonneg x).trans hx) i)
    _ = ∑ i ∈ range n, B ^ (n - 1) := by
        refine sum_congr rfl fun i hi => ?_
        rw [← pow_add]
        congr 1
        simp only [mem_range] at hi
        omega
    _ = n * B ^ (n - 1) := by rw [sum_const, card_range, nsmul_eq_mul]

theorem Polynomial.abs_eval_sub_le {R S : Type*} [CommRing R] [Nontrivial R] [CommSemiring S]
    [PartialOrder S] [IsOrderedRing S] [IsDomain S] (v : AbsoluteValue R S) (f : R[X])
    {x r : R} {B : S} (hx : v x ≤ B) (hr : v r ≤ B) :
    v (f.eval x - f.eval r) ≤
      (∑ i ∈ range (f.natDegree + 1), (i : S) * v (f.coeff i) * B ^ (i - 1)) * v (x - r) := by
  have heval : f.eval x - f.eval r =
      ∑ i ∈ range (f.natDegree + 1), f.coeff i * (x ^ i - r ^ i) := by
    rw [eval_eq_sum_range, eval_eq_sum_range, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [heval]
  calc v (∑ i ∈ range (f.natDegree + 1), f.coeff i * (x ^ i - r ^ i))
      ≤ ∑ i ∈ range (f.natDegree + 1), v (f.coeff i * (x ^ i - r ^ i)) := v.sum_le _ _
    _ = ∑ i ∈ range (f.natDegree + 1), v (f.coeff i) * v (x ^ i - r ^ i) :=
        sum_congr rfl fun i _ => map_mul v _ _
    _ ≤ ∑ i ∈ range (f.natDegree + 1), v (f.coeff i) * ((i : S) * B ^ (i - 1) * v (x - r)) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (v.pow_sub_pow_le hx hr i) (v.nonneg _)
    _ = (∑ i ∈ range (f.natDegree + 1), (i : S) * v (f.coeff i) * B ^ (i - 1)) * v (x - r) := by
        rw [sum_mul]
        exact sum_congr rfl fun i _ => by ring

theorem Polynomial.abs_eval_sub_le_of_sub_lt {R S : Type*} [CommRing R] [Nontrivial R] [CommSemiring S]
    [PartialOrder S] [IsOrderedRing S] [IsDomain S] (v : AbsoluteValue R S) (f : R[X])
    {x r : R} {B ε : S} (hx : v x ≤ B) (hr : v r ≤ B) (he : v (x - r) < ε) :
    v (f.eval x - f.eval r) ≤
        ε * ∑ i ∈ range (f.natDegree + 1), (i : S) * v (f.coeff i) * B ^ (i - 1) := by
  refine (f.abs_eval_sub_le v hx hr).trans ?_
  have hB : 0 ≤ B := (v.nonneg x).trans hx
  have hnonneg : 0 ≤ ∑ i ∈ range (f.natDegree + 1), (i : S) * v (f.coeff i) * B ^ (i - 1) :=
    sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg i) (v.nonneg _)) (pow_nonneg hB _)
  calc (∑ i ∈ range (f.natDegree + 1), (i : S) * v (f.coeff i) * B ^ (i - 1)) * v (x - r)
      ≤ (∑ i ∈ range (f.natDegree + 1), (i : S) * v (f.coeff i) * B ^ (i - 1)) * ε :=
        mul_le_mul_of_nonneg_left he.le hnonneg
    _ = ε * ∑ i ∈ range (f.natDegree + 1), (i : S) * v (f.coeff i) * B ^ (i - 1) := by ring

theorem AbsoluteValue.quadratic_sub_le_of_sub_lt {R S : Type*} [CommRing R] [Nontrivial R] [CommSemiring S]
    [PartialOrder S] [IsOrderedRing S] [IsDomain S] (v : AbsoluteValue R S)
    (a₀ a₁ a₂ : R) (ha₂ : a₂ ≠ 0) {x r : R} {B ε : S} (hx : v x ≤ B) (hr : v r ≤ B)
    (he : v (x - r) < ε) :
    v ((a₂ * x ^ 2 + a₁ * x + a₀) - (a₂ * r ^ 2 + a₁ * r + a₀)) ≤
      ε * (v a₁ + 2 * v a₂ * B) := by
  set f : R[X] := C a₂ * X ^ 2 + C a₁ * X + C a₀ with hf
  have hdeg : f.natDegree = 2 := natDegree_quadratic ha₂
  have heval : ∀ y : R, f.eval y = a₂ * y ^ 2 + a₁ * y + a₀ := by
    intro y; simp [hf]
  have hc0 : f.coeff 0 = a₀ := by simp [hf]
  have hc1 : f.coeff 1 = a₁ := by simp [hf]
  have hc2 : f.coeff 2 = a₂ := by simp [hf]
  have key := f.abs_eval_sub_le_of_sub_lt v hx hr he
  rw [heval, heval, hdeg] at key
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc0, hc1, hc2] at key
  refine key.trans_eq ?_
  push_cast
  ring

theorem abs_quadratic_sub_le_of_sub_lt (a₀ a₁ a₂ : ℝ) (ha₂ : a₂ ≠ 0) {x r B ε : ℝ}
    (hx : |x| ≤ B) (hr : |r| ≤ B) (he : |x - r| < ε) :
    |(a₂ * x ^ 2 + a₁ * x + a₀) - (a₂ * r ^ 2 + a₁ * r + a₀)| ≤
      ε * (|a₁| + 2 * |a₂| * B) := by
  simpa using AbsoluteValue.quadratic_sub_le_of_sub_lt AbsoluteValue.abs a₀ a₁ a₂ ha₂ hx hr he


theorem abs_quadratic_sub_le_of_abs_sub_lt (a₀ a₁ a₂ : ℝ) (ha₂ : a₂ ≠ 0) {x r ε : ℝ}
    (he : |x - r| < ε) :
    |(a₂ * x ^ 2 + a₁ * x + a₀) - (a₂ * r ^ 2 + a₁ * r + a₀)| ≤
      ε * (|a₁| + 2 * |a₂| * (|r| + ε)) := by
  have hεpos : 0 < ε := (abs_nonneg _).trans_lt he
  have hx : |x| ≤ |r| + ε := by
    calc |x| = |r + (x - r)| := by ring_nf
      _ ≤ |r| + |x - r| := abs_add_le _ _
      _ ≤ |r| + ε := by linarith [he.le]
  have hr : |r| ≤ |r| + ε := by linarith
  exact abs_quadratic_sub_le_of_sub_lt a₀ a₁ a₂ ha₂ hx hr he

theorem exists_root_mem_Ioo_of_mul_neg  {b₀ b₁ b₂ b₃ : ℝ}
    {r ε : ℝ} (hε : 0 < ε)
    (h1 : (b₃ * (r + ε) ^ 3 + b₂ * (r + ε) ^ 2 + b₁ * (r + ε) + b₀) *
          (b₃ * (r - ε) ^ 3 + b₂ * (r - ε) ^ 2 + b₁ * (r - ε) + b₀) < 0) :
    ∃ x ∈ Set.Ioo (r - ε) (r + ε), (b₃ * x ^ 3 + b₂ * x ^ 2 + b₁ * x + b₀ = 0) := by
  have hab : r - ε ≤ r + ε := by linarith
  have hcont : ContinuousOn (fun y => b₃ * y ^ 3 + b₂ * y ^ 2 + b₁ * y + b₀)
      (Set.Icc (r - ε) (r + ε)) := by fun_prop
  rcases mul_neg_iff.mp h1 with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · exact intermediate_value_Ioo hab hcont ⟨h2', h1'⟩
  · exact intermediate_value_Ioo' hab hcont ⟨h1', h2'⟩


theorem abs_eval_root_sub_le (a₀ a₁ a₂ b₀ b₁ b₂ b₃ : ℝ) (ha₂ : a₂ ≠ 0)
    {r ε : ℝ} (hε : 0 < ε)
    (h1 : (b₃ * (r + ε) ^ 3 + b₂ * (r + ε) ^ 2 + b₁ * (r + ε) + b₀) *
          (b₃ * (r - ε) ^ 3 + b₂ * (r - ε) ^ 2 + b₁ * (r - ε) + b₀) < 0) :
    |(a₂ * (exists_root_mem_Ioo_of_mul_neg hε h1).choose ^ 2 + a₁ * (exists_root_mem_Ioo_of_mul_neg hε h1).choose + a₀)
        - (a₂ * r ^ 2 + a₁ * r + a₀)| ≤ ε * (|a₁| + 2 * |a₂| * (|r| + ε)) := by
  obtain ⟨⟨hlt1, hlt2⟩, -⟩ := (exists_root_mem_Ioo_of_mul_neg hε h1).choose_spec
  exact abs_quadratic_sub_le_of_abs_sub_lt a₀ a₁ a₂ ha₂ (by rw [abs_lt]; constructor <;> linarith)

theorem eval_root_le (a₀ a₁ a₂ b₀ b₁ b₂ b₃ : ℝ) (ha₂ : a₂ ≠ 0)
    {r ε : ℝ} (hε : 0 < ε)
    (h1 : (b₃ * (r + ε) ^ 3 + b₂ * (r + ε) ^ 2 + b₁ * (r + ε) + b₀) *
          (b₃ * (r - ε) ^ 3 + b₂ * (r - ε) ^ 2 + b₁ * (r - ε) + b₀) < 0) :
      a₂ * (exists_root_mem_Ioo_of_mul_neg hε h1).choose ^ 2 + a₁ * (exists_root_mem_Ioo_of_mul_neg hε h1).choose + a₀ ≤
        (a₂ * r ^ 2 + a₁ * r + a₀) +
          ε * (|a₁| + 2 * |a₂| * (|r| + ε)) := by
  linarith [(abs_le.mp (abs_eval_root_sub_le a₀ a₁ a₂ b₀ b₁ b₂ b₃ ha₂ hε h1)).2]

theorem le_eval_root (a₀ a₁ a₂ b₀ b₁ b₂ b₃ : ℝ) (ha₂ : a₂ ≠ 0)
    {r ε : ℝ} (hε : 0 < ε)
    (h1 : (b₃ * (r + ε) ^ 3 + b₂ * (r + ε) ^ 2 + b₁ * (r + ε) + b₀) *
          (b₃ * (r - ε) ^ 3 + b₂ * (r - ε) ^ 2 + b₁ * (r - ε) + b₀) < 0) :
      (a₂ * r ^ 2 + a₁ * r + a₀) - ε * (|a₁| + 2 * |a₂| * (|r| + ε)) ≤
        a₂ * (exists_root_mem_Ioo_of_mul_neg hε h1).choose ^ 2 + a₁ * (exists_root_mem_Ioo_of_mul_neg hε h1).choose + a₀ := by
  linarith [(abs_le.mp (abs_eval_root_sub_le a₀ a₁ a₂ b₀ b₁ b₂ b₃ ha₂ hε h1)).1]

open NumberField.ComplexEmbedding

noncomputable def realEmbeddingOfRealRoot {K : Type*} [Field K] [NumberField K] {f : ℚ[X]}
    (hf : IsAdjoinRoot K f) {x : ℝ} (hz : f.aeval x = 0) : K →+* ℂ := by
  refine IsAdjoinRoot.lift hf (algebraMap ℚ ℂ) x ?_
  rw [Polynomial.aeval_def] at hz
  show eval₂ ((algebraMap ℝ ℂ).comp (algebraMap ℚ ℝ)) ((algebraMap ℝ ℂ) x) f = 0
  rw [← Polynomial.hom_eval₂, hz, map_zero]


lemma realEmbeddingOfRealRoot_isReal  {K : Type*} [Field K] [NumberField K] {f : ℚ[X]}
    (hf : IsAdjoinRoot K f) {x : ℝ} (hz : f.aeval x = 0) :
    IsReal (realEmbeddingOfRealRoot hf hz) := by
  rw [isReal_iff]
  unfold realEmbeddingOfRealRoot
  refine hf.eq_lift _ _ (fun a => ?_) ?_
  · rw [conjugate_coe_eq, IsAdjoinRoot.lift_algebraMap, IsScalarTower.algebraMap_apply ℚ ℝ ℂ]
    exact Complex.conj_ofReal _
  · rw [conjugate_coe_eq, IsAdjoinRoot.lift_root]
    exact Complex.conj_ofReal _


lemma realEmbeddingOfRealRoot_eval {K : Type*} [Field K] [NumberField K]
    {f g : ℚ[X]} (hf : IsAdjoinRoot K f) {x : ℝ} (hz : f.aeval x = 0) :
    (realEmbeddingOfRealRoot_isReal hf hz).embedding (hf.map g) = g.aeval x := by
  have h1 : ((realEmbeddingOfRealRoot_isReal hf hz).embedding (hf.map g) : ℂ) =
      (g.aeval x : ℂ) := by
    rw [(realEmbeddingOfRealRoot_isReal hf hz).coe_embedding_apply]
    unfold realEmbeddingOfRealRoot
    rw [IsAdjoinRoot.lift_map]
    have heq2 : (algebraMap ℚ ℂ) = (algebraMap ℝ ℂ).comp (algebraMap ℚ ℝ) := rfl
    show eval₂ (algebraMap ℚ ℂ) (x : ℂ) g = ((g.aeval x : ℝ) : ℂ)
    rw [heq2]
    show eval₂ ((algebraMap ℝ ℂ).comp (algebraMap ℚ ℝ)) ((algebraMap ℝ ℂ) x) g =
      (algebraMap ℝ ℂ) (g.aeval x)
    rw [← Polynomial.hom_eval₂, ← Polynomial.aeval_def]
  exact_mod_cast h1

noncomputable def realRootCubic
  {b₀ b₁ b₂ b₃ ε : ℚ}  (hε : 0 < ε) {r : ℝ}
  (h1 : (b₃ * (r + ε) ^ 3 + b₂ * (r + ε) ^ 2 + b₁ * (r + ε) + b₀) *
          (b₃ * (r - ε) ^ 3 + b₂ * (r - ε) ^ 2 + b₁ * (r - ε) + b₀) < 0) : ℝ :=
  (exists_root_mem_Ioo_of_mul_neg (algebraMap_pos ℝ hε) h1).choose

lemma realRootCubic_eval_eq_zero {b₀ b₁ b₂ b₃ ε : ℚ} (hε : 0 < ε) {r : ℝ}
    (h1 : (b₃ * (r + ε) ^ 3 + b₂ * (r + ε) ^ 2 + b₁ * (r + ε) + b₀) *
          (b₃ * (r - ε) ^ 3 + b₂ * (r - ε) ^ 2 + b₁ * (r - ε) + b₀) < 0) :
    b₃ * realRootCubic hε h1 ^ 3 + b₂ * realRootCubic hε h1 ^ 2 +
      b₁ * realRootCubic hε h1 + b₀ = 0 :=
  (exists_root_mem_Ioo_of_mul_neg (algebraMap_pos ℝ hε) h1).choose_spec.2

noncomputable def realEmbeddingOfRealRootCubic {K : Type*} [Field K] [NumberField K]
  {b₀ b₁ b₂ b₃ ε : ℚ}  (hε : 0 < ε) {f : ℚ[X]}
  (heq : f = C b₃ * X ^ 3 + C b₂ * X ^ 2 + C b₁ * X + C b₀)
  (hf : IsAdjoinRoot K f) {r : ℝ}
  (h1 : (b₃ * (r + ε) ^ 3 + b₂ * (r + ε) ^ 2 + b₁ * (r + ε) + b₀) *
          (b₃ * (r - ε) ^ 3 + b₂ * (r - ε) ^ 2 + b₁ * (r - ε) + b₀) < 0) : K →+* ℂ := by
    apply realEmbeddingOfRealRoot hf (x := realRootCubic hε h1)
    rw [heq]
    have := realRootCubic_eval_eq_zero hε h1
    simp only [map_add, map_mul, aeval_C, eq_ratCast, map_pow, aeval_X]
    exact this

lemma realEmbeddingOfRealRootCubic_isReal {K : Type*} [Field K] [NumberField K]
    {b₀ b₁ b₂ b₃ ε : ℚ}  (hε : 0 < ε){f : ℚ[X]}
    (heq : f = C b₃ * X ^ 3 + C b₂ * X ^ 2 + C b₁ * X + C b₀)
    (hf : IsAdjoinRoot K f) {r : ℝ}
    (h1 : (b₃ * (r + ε) ^ 3 + b₂ * (r + ε) ^ 2 + b₁ * (r + ε) + b₀) *
            (b₃ * (r - ε) ^ 3 + b₂ * (r - ε) ^ 2 + b₁ * (r - ε) + b₀) < 0) :
  IsReal (realEmbeddingOfRealRootCubic hε heq hf h1) :=
  realEmbeddingOfRealRoot_isReal hf _

lemma realEmbeddingOfRealRootCubic_embedding {K : Type*} [Field K] [NumberField K]
    {a₀ a₁ a₂ b₀ b₁ b₂ b₃ ε : ℚ} (hε : 0 < ε) {f : ℚ[X]}
    (heq : f = C b₃ * X ^ 3 + C b₂ * X ^ 2 + C b₁ * X + C b₀)
    (hf : IsAdjoinRoot K f) {r : ℝ}
    (h1 : (b₃ * (r + ε) ^ 3 + b₂ * (r + ε) ^ 2 + b₁ * (r + ε) + b₀) *
            (b₃ * (r - ε) ^ 3 + b₂ * (r - ε) ^ 2 + b₁ * (r - ε) + b₀) < 0) :
    (realEmbeddingOfRealRootCubic_isReal hε heq hf h1).embedding
      (a₂ * hf.root ^ 2 + a₁ * hf.root + a₀) =
      a₂ * (realRootCubic hε h1) ^ 2 + a₁ * (realRootCubic hε h1) + a₀ := by
  have h2 := realEmbeddingOfRealRoot_eval hf (g := C a₂ * X ^ 2 + C a₁ * X + C a₀)
    (x := realRootCubic hε h1) (by
      rw [heq]
      simp only [map_add, map_mul, aeval_C, eq_ratCast, map_pow, aeval_X]
      exact realRootCubic_eval_eq_zero hε h1)
  simpa [map_add, map_mul, map_pow, ← hf.algebraMap_apply,
    IsReal.coe_embedding_apply, realEmbeddingOfRealRootCubic] using h2

lemma realEmbeddingOfRealRootCubic_bound_ge {K : Type*} [Field K] [NumberField K]
    {a₀ a₁ a₂ b₀ b₁ b₂ b₃ ε : ℚ} (ha₂ : a₂ ≠ 0) (hε : 0 < ε) {f : ℚ[X]}
    (heq : f = C b₃ * X ^ 3 + C b₂ * X ^ 2 + C b₁ * X + C b₀)
    (hf : IsAdjoinRoot K f) {r : ℝ}
    (h1 : (b₃ * (r + ε) ^ 3 + b₂ * (r + ε) ^ 2 + b₁ * (r + ε) + b₀) *
            (b₃ * (r - ε) ^ 3 + b₂ * (r - ε) ^ 2 + b₁ * (r - ε) + b₀) < 0) :
    (realEmbeddingOfRealRootCubic_isReal hε heq hf h1).embedding
      (a₂ * hf.root ^ 2 + a₁ * hf.root + a₀) ≥ (a₂ * r ^ 2 + a₁ * r + a₀) -
        ε * (|a₁| + 2 * |a₂| * (|r| + ε)) := by
  rw [realEmbeddingOfRealRootCubic_embedding hε heq hf h1]
  exact_mod_cast le_eval_root a₀ a₁ a₂ b₀ b₁ b₂ b₃
    (by exact_mod_cast ha₂) (algebraMap_pos ℝ hε) h1

lemma realEmbeddingOfRealRootCubic_bound_le {K : Type*} [Field K] [NumberField K]
    {a₀ a₁ a₂ b₀ b₁ b₂ b₃ ε : ℚ} (ha₂ : a₂ ≠ 0) (hε : 0 < ε) {f : ℚ[X]}
    (heq : f = C b₃ * X ^ 3 + C b₂ * X ^ 2 + C b₁ * X + C b₀)
    (hf : IsAdjoinRoot K f) {r : ℝ}
    (h1 : (b₃ * (r + ε) ^ 3 + b₂ * (r + ε) ^ 2 + b₁ * (r + ε) + b₀) *
          (b₃ * (r - ε) ^ 3 + b₂ * (r - ε) ^ 2 + b₁ * (r - ε) + b₀) < 0) :
    (realEmbeddingOfRealRootCubic_isReal hε heq hf h1).embedding
      (a₂ * hf.root ^ 2 + a₁ * hf.root + a₀) ≤ (a₂ * r ^ 2 + a₁ * r + a₀) +
          ε * (|a₁| + 2 * |a₂| * (|r| + ε))  := by
  rw [realEmbeddingOfRealRootCubic_embedding hε heq hf h1]
  exact_mod_cast eval_root_le a₀ a₁ a₂ b₀ b₁ b₂ b₃
    (by exact_mod_cast ha₂) (algebraMap_pos ℝ hε) h1
