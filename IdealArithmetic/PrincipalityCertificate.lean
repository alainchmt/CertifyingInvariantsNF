import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Sturm
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/- Here we specialized `LogFiniteRing` , `MatrixLogProd`
  and the releated theorems to prove nonprincipality to the case
  where the reduction homomorphisms `φ` are reduction modulo primes of degree 1.

Note that for number fields, we can always assume this case.   --/

/-- Given an ideal `I` of norm a prime integer `q`, this is the 'discrete logarithm' map that
sends `x` in `O` to `n % p` in `ZMod p`, where `ζ ^ n = x mod I` and `ζ` is a generator of
`(ZMod q)ˣ`. -/
noncomputable def LogFiniteZMod {O : Type*} [CommRing O] {q : ℕ}
  [hq : Fact $ Nat.Prime q] {I : Ideal O} (hcard : Nat.card (O ⧸ I) = q)
  {ζ : ℕ} (hr : IsPrimitiveRoot (ζ : ZMod q) (q - 1)) (p : ℕ) : O → ZMod p := by
  intro x
  let φ := ((modIdealToZMod (hq).out (I) (hcard)).comp (Ideal.Quotient.mk (I)))
  refine LogFiniteRing (ζ := (ζ : ZMod q)) ?_ p (φ x)
  convert hr
  simp only [ZMod.card_units_eq_totient, Nat.totient_prime hq.out]


attribute [-instance]  Lean.Omega.IntList.instAdd


structure DiscreteLogCertificate {O : Type*} [CommRing O] {q : ℕ}
  [hq : Fact $ Nat.Prime q] {I : Ideal O} (hcard : Nat.card (O ⧸ I) = q)
  {ζ : ℕ} (hr : IsPrimitiveRoot (ζ : ZMod q) (q - 1)) (p : ℕ) (x : O) (l : ZMod p) where
    r : ℕ
    hN : NeZero r
    hpdvd : p ∣ q - 1
    B : Basis (Fin r) ℤ O
    hone : B 0 = 1
    xcoord : Fin r → ℤ
    hxeq : x =  B.equivFun.symm xcoord
    m : ℤ
    C : Fin r → ℤ
    hCeq : List.ofFn C = List.ofFn xcoord + List.ofFn (fun (i : Fin r) => if i = 0 then (- m : ℤ) else 0)
    hmem :  B.equivFun.symm C ∈ I
    k : ℕ
    hpow : (ζ : ZMod q) ^ k = m
    heql : l = k

lemma apply_map_ZMod {O : Type*} [CommRing O] {q : ℕ}
    [hq : Fact $ Nat.Prime q] {I : Ideal O} {hcard : Nat.card (O ⧸ I) = q}
    {ζ : ℕ} {hr : IsPrimitiveRoot (ζ : ZMod q) (q - 1)} {p : ℕ} {x : O} {l : ZMod p}
    (A : DiscreteLogCertificate hcard hr p x l) :
      (modIdealToZMod (hq).out I hcard) ((Ideal.Quotient.mk I) x) = A.m := by
  haveI : NeZero A.r := A.hN
  have hmem : x - A.m ∈ I := by
    convert A.hmem
    rw [← table_add_list_eq_add A.B A.xcoord
      (fun (i : Fin A.r) => if i = 0 then (- A.m : ℤ) else 0) A.C A.hCeq, ← A.hxeq]
    simp [A.hone]
    exact  sub_eq_add_neg _ _
  rw [Ideal.Quotient.eq.2 hmem, map_intCast, map_intCast]


lemma eq_of_DiscreteLogCertificate {O : Type*} [CommRing O] {q : ℕ}
    [hq : Fact $ Nat.Prime q] {I : Ideal O} {hcard : Nat.card (O ⧸ I) = q}
    {ζ : ℕ} {hr : IsPrimitiveRoot (ζ : ZMod q) (q - 1)} {p : ℕ} {x : O} {l : ZMod p}
    (A : DiscreteLogCertificate hcard hr p x l) : LogFiniteZMod hcard hr p x = l := by
  simp only [LogFiniteZMod]
  dsimp
  rw [apply_map_ZMod A, ← A.hpow]
  convert LogFiniteRing_of_pow ?_ ?_ A.k
  · exact A.heql
  · rw [ZMod.card_units_eq_totient, Nat.totient_prime hq.out]
    exact A.hpdvd

section

variable {O : Type*} [CommRing O] [Fintype ι] [Fintype τ]
  (p : ℕ) {q : τ → ℕ} [hF : ∀ i, Fact $ Nat.Prime (q i)]
  {I : τ → Ideal O} (hcard : ∀ j, Nat.card (O ⧸ (I j)) = q j)
  (x : ι → O) {ζ : τ → ℕ} (hr : ∀ i, IsPrimitiveRoot (ζ i : ZMod (q i)) (q i - 1))


def F (q : τ → ℕ) : τ → Type _ := fun i => (ZMod (q i))

instance F_CommRing : ∀ i, CommRing (F q i) := fun i => ZMod.commRing (q i)

instance F_Fintype : ∀ i, Fintype (F q i) := by
  intro i
  exact ZMod.fintype (q i)

open Classical

noncomputable instance F_unit_Fintype :  ∀ i, Fintype (F q i)ˣ := by
  intro i
  refine instFintypeUnitsOfDecidableEq

/- Given a collection of ideals of norm a prime, this is the reduction map O → ZMod _ -/
noncomputable def φ : Π i : τ, O →+* (ZMod (q i)) := by
  intro i
  exact ((modIdealToZMod (hF i).out (I i) (hcard i)).comp (Ideal.Quotient.mk (I i)))

def hr_aux : ∀ i , IsPrimitiveRoot (ζ i : ZMod (q i)) (Fintype.card (F q i)ˣ) := by
  intro i
  convert hr i
  unfold F
  simp only [ZMod.card_units_eq_totient, Nat.totient_prime (hF i).out]


noncomputable def MatrixLogZMod : Matrix τ ι (ZMod p) := by
  intro i j
  exact LogFiniteZMod (hcard i) (hr i) p (x j)


lemma MatrixLog_eq :
  MatrixLogZMod p hcard x hr = MatrixLogProd p (F q) (φ hcard) x _ (hr_aux hr) := by rfl


lemma not_principal_of_full_rank_matrixLogZMod {p n : ℕ} [hp : Fact $ Nat.Prime p]
  [IsDomain O] (u : ι → O) (hu : ∀ i, IsUnit (u i))
  (hugen : ∀ (w : Oˣ), (∃ (e : ι → ℕ) , (∃ (t : Oˣ) , w = (∏ (i : ι), (u i) ^ (e i)) * t ^ p)))
  (hdvd : ∀ i, p ∣ q i - 1) (J : Ideal O) (a : O)
  (hua : ∀ i, (modIdealToZMod (hF i).out (I i) (hcard i)) ((Ideal.Quotient.mk (I i)) a) ≠ 0)
  (hdvdp : p ∣ n) (h : J ^ n = Ideal.span {a})
  (hrank : (MatrixLogZMod p hcard (Sum.elim (fun i => u i) (fun (_ : Fin 1) => a)) hr).rank = Fintype.card ι + 1) :
    ¬ ∃ b, J = Ideal.span {b} := by
  refine not_principal_of_full_rank_matrix (F q) u hu hugen (φ hcard) (fun i => ↑(ζ i)) (hr_aux hr) ?_ J a ?_ hdvdp h ?_
  · intro i
    unfold F
    simp only [ZMod.card_units_eq_totient, Nat.totient_prime (hF i).out]
    exact hdvd i
  · intro i
    apply (isUnit_iff_ne_zero (a := (φ hcard i) a)).2
    exact hua i
  · rw [← MatrixLog_eq p hcard _ hr]
    exact hrank

lemma units_linear_independent_not_dvd_torsion_of_full_rank {p : ℕ} [hp : Fact $ Nat.Prime p]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  (u : ι → O) (hu : ∀ i, IsUnit (u i)) (hdvd : ∀ i, p ∣ q i - 1)
  (hpndvdt : ¬ p ∣ Nat.card (CommGroup.torsion Oˣ))
  (hrank : (MatrixLogZMod p hcard u hr).rank = Fintype.card ι) :
  LinearIndependent ℤ (fun i => Additive.ofMul (QuotientGroup.mk (s := (CommGroup.torsion Oˣ)) (hu i).unit)) := by
  refine units_linear_independent_of_full_rank_matrix_of_p_not_dvd_torsion (F q) u hu (φ hcard)
    (fun i => ↑(ζ i)) (hr_aux hr) ?_ hpndvdt ?_
  · intro i
    unfold F
    simp only [ZMod.card_units_eq_totient, Nat.totient_prime (hF i).out]
    exact hdvd i
  · rw [← MatrixLog_eq p hcard _ hr]
    exact hrank


lemma units_up_to_p_power_not_dvd_torsion_of_full_rank {p : ℕ} [hp : Fact $ Nat.Prime p]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  (u : ι → O) (hu : ∀ i, IsUnit (u i)) (hdvd : ∀ i, p ∣ q i - 1)
  (hpndvdt : ¬ p ∣ Nat.card (CommGroup.torsion Oˣ))
  (hrank : (MatrixLogZMod p hcard u hr).rank = Fintype.card ι)
  (huc : Module.finrank ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ))) ≤ Fintype.card ι) (w : Oˣ) :
  ∃ (e' : ι → ℤ), (∃ (t : Oˣ) , w = (∏ (i : ι), ((hu i).unit) ^ (e' i)) * t ^ p) := by
  refine units_up_to_p_power_of_full_rank_matrix_of_p_not_dvd_torsion (F q) u hu (φ hcard)
    (fun i => ↑(ζ i)) (hr_aux hr) ?_ hpndvdt ?_ huc w
  · intro i
    unfold F
    simp only [ZMod.card_units_eq_totient, Nat.totient_prime (hF i).out]
    exact hdvd i
  · rw [← MatrixLog_eq p hcard _ hr]
    exact hrank

lemma units_up_to_p_power_dvd_torsion_of_full_rank [Fintype κ] {p : ℕ} [hp : Fact $ Nat.Prime p]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  (u : ι → O) (hu : ∀ i, IsUnit (u i)) (hdvd : ∀ i, p ∣ q i - 1)
  (v : κ → O) (hv : ∀ i, IsUnit (v i))
  (hvt : ∀ w ∈ CommGroup.torsion Oˣ, (∃ (a : κ → ℤ) , (∃ t ∈ CommGroup.torsion Oˣ ,
    w = (∏ i, (hv i).unit ^ (a i)) * t ^ p)))
  (hrank : (MatrixLogZMod p hcard ((Sum.elim u v)) hr).rank = Fintype.card ι + Fintype.card κ)
  (huc : Module.finrank ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ))) ≤ Fintype.card ι) (w : Oˣ) :
   ∃ (e' : ι ⊕ κ → ℤ), (∃ (t : Oˣ) , w = (∏ (i : ι ⊕ κ), (Sum.elim (fun i => (hu i).unit)
    (fun i => (hv i).unit) i) ^ (e' i)) * t ^ p) := by
  refine units_up_to_p_power_of_full_rank_matrix_of_p_dvd_torsion (F q) u hu (φ hcard)
    (fun i => ↑(ζ i)) (hr_aux hr) ?_ v hv hvt ?_ huc w
  · intro i
    unfold F
    simp only [ZMod.card_units_eq_totient, Nat.totient_prime (hF i).out]
    exact hdvd i
  · rw [← MatrixLog_eq p hcard _ hr]
    exact hrank


lemma units_linear_independent_dvd_torsion_of_full_rank [Fintype κ] {p : ℕ} [hp : Fact $ Nat.Prime p]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  (u : ι → O) (hu : ∀ i, IsUnit (u i)) (hdvd : ∀ i, p ∣ q i - 1)
  (v : κ → O) (hv : ∀ i, IsUnit (v i))
  (hvt : ∀ w ∈ CommGroup.torsion Oˣ, (∃ (a : κ → ℤ) , (∃ t ∈ CommGroup.torsion Oˣ , w = (∏ i, (hv i).unit ^ (a i)) * t ^ p)))
  (hrank : (MatrixLogZMod p hcard ((Sum.elim u v)) hr).rank = Fintype.card ι + Fintype.card κ) :
  LinearIndependent ℤ (fun i => Additive.ofMul (QuotientGroup.mk (s := (CommGroup.torsion Oˣ)) (hu i).unit)) := by
  refine units_linear_independent_of_full_rank_matrix_of_p_dvd_torsion (F q) u hu v hv hvt (φ hcard) (fun i => ↑(ζ i)) (hr_aux hr) ?_ ?_
  · intro i
    unfold F
    simp only [ZMod.card_units_eq_totient, Nat.totient_prime (hF i).out]
    exact hdvd i
  · rw [← MatrixLog_eq p hcard _ hr]
    exact hrank


end


-- Dirichlet Unit theorem applies to orders of K, so we make this
-- certificate more general.
structure NonPrincipalCertificateNDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] (J : Ideal O) where
 p : ℕ
 hp : Nat.Prime p
 r : ℕ -- rank of the unit group
 huc : Module.finrank ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ))) ≤ r
 u : Fin r → O
 hu : ∀ (i : Fin r), IsUnit (u i)
 q : Fin (r + 1) → ℕ -- List of prime norms
 hqP : ∀ i, Fact (Nat.Prime (q i))
 I : Fin (r + 1) → Ideal O -- Corresponding list of ideals (advantage of degree 1: we dont have to prove they are prime)
 hcard : ∀ j, Nat.card (O ⧸ I j) = q j
 ζ : Fin (r + 1) → ℕ
 hr : ∀ i, IsPrimitiveRoot (ζ i : ZMod (q i)) (q i - 1)
 hdvd : ∀ i, p ∣ q i - 1
 a : O
 n : ℕ -- Power to raise the ideal (usually prime)
 hpdvd : p ∣ n
 hJ : J ^ n = Ideal.span {a}
 hpndvdt : ¬p ∣ Nat.card (CommGroup.torsion Oˣ)
 M : Matrix (Fin (r + 1)) (Fin (r + 1)) (ZMod p)
 hM1 : ∀ i, ∀ hj : j < r , M i j = LogFiniteZMod (hcard i) (hr i) p (u ⟨j, hj⟩) -- First columns of the matrix
 hM2 : ∀ i , DiscreteLogCertificate (hcard i) (hr i) p a (M i r) -- Last column of the matrix. The certificate contains discrete log info.
 hDl : ∀ i, ((hM2 i).m : ZMod (q i)) ≠ 0
 Minv : Matrix (Fin (r + 1)) (Fin (r + 1)) (ZMod p)
 hInv : M * Minv = 1
 N : Matrix (Fin r) (Fin r) (ZMod p)
 hNiv : (M.submatrix (Fin.castSucc) (Fin.castSucc)) * N = 1
 -- Order the prime ideals q i in such a way that removing the last row and column induce an
 -- invertible matrix.


lemma matrix_of_NonPrincipalCertificateNDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] {J : Ideal O}
  (C : NonPrincipalCertificateNDvdT J) :
    Matrix.reindex (Equiv.refl _) (finSumFinEquiv).symm C.M  =
      (MatrixLogZMod C.p (hF := C.hqP) C.hcard
      (Sum.elim (fun i => C.u i) (fun (_ : Fin 1) => C.a)) C.hr) := by
    ext i j
    rcases j with j | k
    · simp [MatrixLog_eq, MatrixLogZMod]
      convert C.hM1 i j.2
      rw [Fin.coe_eq_castSucc]
      rfl
    · simp [MatrixLog_eq, MatrixLogZMod]
      haveI : Fact $ Nat.Prime (C.q i) := C.hqP i
      rw [eq_of_DiscreteLogCertificate (C.hM2 i)]
      simp only [Fin.natAdd, Fin.val_eq_zero, add_zero, Fin.natCast_eq_last]
      rfl

lemma submatrix_of_NonPrincipalCertificateNDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] {J : Ideal O}
  (C : NonPrincipalCertificateNDvdT J) :
    C.M.submatrix (Fin.castSucc) (Fin.castSucc)  =
      (MatrixLogZMod C.p (hF := fun i : Fin C.r => C.hqP i)
        (fun i => C.hcard i) C.u (fun i => C.hr i)) := by
    ext i j
    simp [MatrixLog_eq, MatrixLogZMod]
    convert C.hM1 i j.2
    repeat {simp}

lemma units_linear_independent_of_NonPrincipalCertificateNDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] {J : Ideal O}
  (C : NonPrincipalCertificateNDvdT J) :
LinearIndependent ℤ (fun i => Additive.ofMul (QuotientGroup.mk (s := (CommGroup.torsion Oˣ)) (C.hu i).unit)) := by
  haveI : Fact $ Nat.Prime C.p := {out := C.hp}
  refine units_linear_independent_not_dvd_torsion_of_full_rank (hF := fun i : Fin C.r => C.hqP i)  (fun i => C.hcard i)
    (fun i => C.hr i) C.u C.hu (fun i => C.hdvd i) C.hpndvdt ?_
  rw [← submatrix_of_NonPrincipalCertificateNDvdT C]
  refine le_antisymm ?_ ?_
  · convert (Matrix.rank_le_card_width) _
    exact strongRankCondition_of_orzechProperty (ZMod C.p)
  · refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.N)
    rw [C.hNiv]
    simp only [Fintype.card_fin, Matrix.rank_one]


lemma units_of_NonPrincipalCertificateNDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] {J : Ideal O}
  (C : NonPrincipalCertificateNDvdT J) (w : Oˣ) :
  ∃ (e' : Fin C.r → ℤ), (∃ (t : Oˣ) , w = (∏ i, ((C.hu i).unit) ^ (e' i)) * t ^ C.p) := by
  haveI : Fact $ Nat.Prime C.p := {out := C.hp}
  refine units_up_to_p_power_not_dvd_torsion_of_full_rank (hF := fun i : Fin C.r => C.hqP i)
    (fun i => C.hcard i)
    (fun i => C.hr i) C.u C.hu (fun i => C.hdvd i) C.hpndvdt ?_ ?_ w
  rw [← submatrix_of_NonPrincipalCertificateNDvdT C]
  refine le_antisymm ?_ ?_
  · convert (Matrix.rank_le_card_width) _
    exact strongRankCondition_of_orzechProperty (ZMod C.p)
  · refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.N)
    rw [C.hNiv]
    simp only [Fintype.card_fin, Matrix.rank_one]
  simp
  exact C.huc

lemma not_principal_of_NonPrincipalCertificateNDvdT  {O : Type*} [CommRing O]
    [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] {J : Ideal O}
    (C : NonPrincipalCertificateNDvdT J) : ¬ ∃ b, J = Ideal.span {b} := by
  haveI : Fact $ Nat.Prime C.p := {out := C.hp}
  refine not_principal_of_full_rank_matrixLogZMod (hF := C.hqP) C.hcard C.hr C.u C.hu
    ?_ C.hdvd J C.a ?_ C.hpdvd C.hJ ?_
  · intro w
    obtain ⟨e, t, h1⟩ := units_of_NonPrincipalCertificateNDvdT C w
    obtain ⟨e',h1, t', h2 ⟩ := (nat_up_to_power_of_int_up_to_power C.hu (Ne.symm (NeZero.ne' C.p)) e t h1)
    use e' , t'
  · intro i
    rw [apply_map_ZMod (hq := C.hqP i) (C.hM2 i)]
    exact C.hDl i
  · rw [← matrix_of_NonPrincipalCertificateNDvdT C]
    refine le_antisymm ?_ ?_
    · convert (Matrix.rank_le_card_width) _
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unique]
      exact strongRankCondition_of_orzechProperty (ZMod C.p)
    · rw [Matrix.rank, Matrix.mulVecLin_reindex, LinearMap.range_comp, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq, ← Matrix.rank]
      refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.Minv)
      rw [C.hInv]
      simp only [Fintype.card_fin, Matrix.rank_one]

-- Why include elements of O instead of coordinates for this elements?
-- Because I want to reuse my units, so i want to define them beforehand. Proofs would be
-- repetitive if I do all computations within the structure.

structure NonPrincipalCertificateDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [IsCyclic (CommGroup.torsion Oˣ)] (J : Ideal O) where
p : ℕ
hp : Nat.Prime p
r : ℕ -- rank of the unit group
huc : Module.finrank ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ))) ≤ r
u : Fin r → O -- generators of the unit group mod torsion (mod p-powers)
hu : ∀ (i : Fin r), IsUnit (u i)
v : O -- Generator of the torsion group (mod p-powers)
m : ℕ
hm : m ≠ 0
hmv : v ^ m = 1 -- v is a torsion unit. Insetad of proving this directly,
  --you could, for each prime power dividing m, give elements that order and consider the product. Or just use square and multiply.
q : Fin (r + 1 + 1) → ℕ -- List of prime norms
hqP : ∀ i, Fact (Nat.Prime (q i))
I : Fin (r + 1 + 1) → Ideal O -- Corresponding list of prime ideals
hcard : ∀ j, Nat.card (O ⧸ I j) = q j
ζ : Fin (r + 1 + 1) → ℕ
hr : ∀ i, IsPrimitiveRoot (ζ i : ZMod (q i)) (q i - 1)
hdvd : ∀ i, p ∣ q i - 1
a : O
n : ℕ -- Power to raise the ideal (usually prime)
hpdvd : p ∣ n
hJ : J ^ n = Ideal.span {a}
M : Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) (ZMod p)
hM1 : ∀ i, ∀ hj : j < r , M i j = LogFiniteZMod (hcard i) (hr i) p (u ⟨j, hj⟩) -- First columns of the matrix
hM2 : ∀ i, M i r = LogFiniteZMod (hcard i) (hr i) p v
hM3 : ∀ i , DiscreteLogCertificate (hcard i) (hr i) p a (M i (r + 1)) -- Last column of the matrix. The certificate contains discrete log info.
hDl : ∀ i, ((hM3 i).m : ZMod (q i)) ≠ 0
Minv : Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) (ZMod p)
hInv : M * Minv = 1
N : Matrix (Fin (r + 1)) (Fin (r + 1)) (ZMod p)
hNiv : (M.submatrix (Fin.castSucc) (Fin.castSucc)) * N = 1


lemma torsion_of_NonPrincipalCertificateDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [IsCyclic (CommGroup.torsion Oˣ)] {J : Ideal O} (C : NonPrincipalCertificateDvdT J) :
  ∀ w ∈ CommGroup.torsion Oˣ, (∃ (a : ℤ) , (∃ t ∈ CommGroup.torsion Oˣ ,
    w = ((IsUnit.of_pow_eq_one C.hmv C.hm).unit ^ a * t ^ C.p))) := by
  haveI : Fact $ Nat.Prime C.p := {out := C.hp }
  have hvmem : (IsUnit.of_pow_eq_one C.hmv C.hm).unit ∈ CommGroup.torsion Oˣ := by
    rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    use C.m
    constructor
    · exact Nat.pos_of_ne_zero C.hm
    · rw [Units.ext_iff]
      simp [C.hmv]
  intro w hwmem
  obtain ⟨⟨g, hgmem⟩ , hg ⟩ := exists_zpow_surjective (CommGroup.torsion Oˣ)
  obtain ⟨r, hr⟩ := hg ⟨w, hwmem⟩
  obtain ⟨t, ht⟩ := hg ⟨_, hvmem⟩
  rw [← Subtype.val_inj] at hr ht
  simp at hr ht
  haveI := C.hqP
  have hnz : ∃ i, LogFiniteZMod (C.hcard i) (C.hr i) C.p C.v ≠ 0 := by
    by_contra! h
    simp_rw [← C.hM2] at h
    have : (C.Minv *C.M) C.r C.r = 1 := by
      rw [Matrix.mul_eq_one_comm.1 C.hInv]
      simp only [Matrix.one_apply_eq]
    rw [Matrix.mul_apply] at this
    simp [h] at this
  have hC : IsCoprime ↑C.p t := by
    rw [Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp C.hp)]
    rintro ⟨k, hk⟩
    obtain ⟨i, hi⟩ := hnz
    rw [hk, mul_comm, zpow_mul, zpow_natCast, Units.ext_iff] at ht
    simp at ht
    rw [← ht] at hi
    simp [LogFiniteZMod] at hi
    rw [LogFiniteRing_p_power_eq_zero] at hi
    exact hi rfl
    simp only [ZMod.card_units_eq_totient, Nat.totient_prime (C.hqP i).out]
    exact C.hdvd i
  obtain ⟨b, a, hab⟩ := hC
  use r * a , g ^ (r * b)
  constructor
  · exact Subgroup.zpow_mem (CommGroup.torsion Oˣ) hgmem _
  · rw [← ht, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
      ← zpow_add, add_comm, mul_comm t _, ← hr]
    nth_rw 1 [← mul_one r, ← hab]
    congr
    ring

lemma matrix_of_NonPrincipalCertificateDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [IsCyclic (CommGroup.torsion Oˣ)] {J : Ideal O}
  (C : NonPrincipalCertificateDvdT J) :
    Matrix.reindex (Equiv.refl _) (Equiv.trans (finSumFinEquiv.symm)
      (Equiv.sumCongr (finSumFinEquiv.symm) (Equiv.refl _))) C.M  =
      (MatrixLogZMod C.p (hF := C.hqP) C.hcard
      (Sum.elim (Sum.elim (C.u) (fun (_ : Fin 1) => C.v)) (fun (_ : Fin 1) => C.a)) C.hr) := by
    ext i j
    rcases j with (j | j') | k
    · simp [MatrixLog_eq, MatrixLogZMod]
      convert C.hM1 i j.2
      rw [← Fin.val_inj]
      simp only [Fin.coe_castAdd, Fin.val_cast_of_lt (show (j < C.r + 1 + 1) by omega) ]
    · simp [MatrixLog_eq, MatrixLogZMod]
      convert C.hM2 i
      rw [← Fin.val_inj]
      simp only [Fin.coe_castAdd, Fin.coe_natAdd, Fin.val_eq_zero, add_zero,
        Fin.val_cast_of_lt (show (C.r < C.r + 1 + 1) by omega) ]
    · simp [MatrixLog_eq, MatrixLogZMod]
      haveI : Fact $ Nat.Prime (C.q i) := C.hqP i
      rw [eq_of_DiscreteLogCertificate (C.hM3 i)]
      congr 1
      rw [← Fin.val_inj]
      have : (↑C.r : Fin (C.r + 1 + 1)) + 1 = ↑(C.r + 1) := by
        exact Eq.symm (Mathlib.Tactic.Ring.inv_add rfl rfl)
      rw [this]
      rw [Fin.val_cast_of_lt (show (C.r + 1 < C.r + 1 + 1) by omega)]
      simp only [Fin.coe_natAdd, Fin.val_eq_zero, add_zero]


lemma submatrix_of_NonPrincipalCertificateDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [IsCyclic (CommGroup.torsion Oˣ)] {J : Ideal O}
  (C : NonPrincipalCertificateDvdT J) :
    C.M.submatrix (Fin.castSucc) ((Fin.castSucc) ∘ (finSumFinEquiv).toFun)  =
      (MatrixLogZMod C.p (hF := fun i : Fin (C.r + 1) => C.hqP i)
        (fun i => C.hcard i) (Sum.elim C.u (fun (_ : Fin 1) => C.v)) (fun i => C.hr i)) := by
    ext i j
    rcases j with j | r
    · simp [MatrixLog_eq, MatrixLogZMod]
      convert C.hM1 i j.2 using 2
      simp only [Fin.coe_eq_castSucc]
      rw [← Fin.coe_eq_castSucc]
      repeat {simp}
    · simp [MatrixLog_eq, MatrixLogZMod]
      convert C.hM2 i
      simp only [Fin.coe_eq_castSucc]
      rw [← Fin.coe_eq_castSucc]
      repeat {simp}


lemma units_linear_independent_of_NonPrincipalCertificateDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [IsCyclic (CommGroup.torsion Oˣ)] {J : Ideal O}
  (C : NonPrincipalCertificateDvdT J) :
  LinearIndependent ℤ (fun i => Additive.ofMul (QuotientGroup.mk (s := (CommGroup.torsion Oˣ)) (C.hu i).unit)) := by
  haveI : Fact $ Nat.Prime C.p := {out := C.hp}
  refine units_linear_independent_dvd_torsion_of_full_rank (hF := fun i : Fin (C.r + 1) => C.hqP i) (fun i => C.hcard i) (fun i => C.hr i) C.u C.hu (fun i => C.hdvd i) (fun (i : Fin 1) => C.v) ?_ ?_ ?_
  · intro i
    exact (IsUnit.of_pow_eq_one C.hmv C.hm)
  · intro w' hwmem'
    obtain ⟨a, t, htmem, hat⟩ := torsion_of_NonPrincipalCertificateDvdT C w' hwmem'
    use a, t, htmem
    rw [hat]
    simp
  rw [← submatrix_of_NonPrincipalCertificateDvdT C]
  refine le_antisymm ?_ ?_
  · convert (Matrix.rank_le_card_width) _
    simp only [Fintype.card_fin, Fintype.card_unique, Fintype.card_sum]
    exact strongRankCondition_of_orzechProperty (ZMod C.p)
  · erw [← Matrix.submatrix_submatrix C.M (Fin.castSucc )
      (Fin.castSucc ) (Equiv.refl _).toFun (finSumFinEquiv.toFun)]
    erw [← Matrix.reindex_apply (Equiv.refl _).symm (finSumFinEquiv).symm]
    rw [Matrix.rank, Matrix.mulVecLin_reindex, LinearMap.range_comp, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq, ← Matrix.rank]
    refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.N)
    rw [C.hNiv]
    simp only [Fintype.card_fin, Matrix.rank_one]


lemma units_of_NonPrincipalCertificateDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [IsCyclic (CommGroup.torsion Oˣ)] {J : Ideal O}
  (C : NonPrincipalCertificateDvdT J) (w : Oˣ) :
  ∃ (e' : (Fin C.r) ⊕ (Fin 1) → ℤ), (∃ (t : Oˣ) , w = (∏ (i : (Fin C.r) ⊕ (Fin 1)),
    (Sum.elim (fun i => (C.hu i).unit)
    (fun _ => (IsUnit.of_pow_eq_one C.hmv C.hm).unit) i) ^ (e' i)) * t ^ C.p) := by
  haveI : Fact $ Nat.Prime C.p := {out := C.hp}
  refine units_up_to_p_power_dvd_torsion_of_full_rank (hF := fun i : Fin (C.r + 1) => C.hqP i)
    (fun i => C.hcard i) (fun i => C.hr i) C.u C.hu (fun i => C.hdvd i)
      (fun (i : Fin 1) => C.v) _ ?_ ?_ ?_ w
  · intro w' hwmem'
    obtain ⟨a, t, htmem, hat⟩ := torsion_of_NonPrincipalCertificateDvdT C w' hwmem'
    use a, t, htmem
    rw [hat]
    simp
  rw [← submatrix_of_NonPrincipalCertificateDvdT C]
  refine le_antisymm ?_ ?_
  · convert (Matrix.rank_le_card_width) _
    simp only [Fintype.card_fin, Fintype.card_unique, Fintype.card_sum]
    exact strongRankCondition_of_orzechProperty (ZMod C.p)
  · erw [← Matrix.submatrix_submatrix C.M (Fin.castSucc )
      (Fin.castSucc ) (Equiv.refl _).toFun (finSumFinEquiv.toFun)]
    erw [← Matrix.reindex_apply (Equiv.refl _).symm (finSumFinEquiv).symm]
    rw [Matrix.rank, Matrix.mulVecLin_reindex, LinearMap.range_comp, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq, ← Matrix.rank]
    refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.N)
    rw [C.hNiv]
    simp only [Fintype.card_fin, Matrix.rank_one]
  · simp [C.huc]


lemma not_principal_of_NonPrincipalCertificateDvdT  {O : Type*} [CommRing O]
    [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [IsCyclic (CommGroup.torsion Oˣ)] {J : Ideal O}
    (C : NonPrincipalCertificateDvdT J) : ¬ ∃ b, J = Ideal.span {b} := by
  have aux : ∀ (i : Fin C.r ⊕ Fin 1), IsUnit (Sum.elim C.u (fun x ↦ C.v) i) := by
    intro i
    rcases i with i | j
    · simp [C.hu]
    · exact IsUnit.of_pow_eq_one C.hmv C.hm
  haveI : Fact $ Nat.Prime C.p := {out := C.hp}
  refine not_principal_of_full_rank_matrixLogZMod (hF := C.hqP) C.hcard C.hr
    (Sum.elim C.u (fun (_ : Fin 1) => C.v)) ?_
    ?_ C.hdvd J C.a ?_ C.hpdvd C.hJ ?_
  · exact aux
  · intro w
    obtain ⟨e, t, h1⟩ := units_of_NonPrincipalCertificateDvdT C w
    obtain ⟨e',h1, t', h2 ⟩ := (nat_up_to_power_of_int_up_to_power (w := w) aux
      (Ne.symm (NeZero.ne' C.p)) e t (by rw [h1]; simp))
    use e' , t'
  · intro i
    rw [apply_map_ZMod (hq := C.hqP i) (C.hM3 i)]
    exact C.hDl i
  · rw [← matrix_of_NonPrincipalCertificateDvdT C]
    refine le_antisymm ?_ ?_
    · convert (Matrix.rank_le_card_width) _
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unique]
      exact strongRankCondition_of_orzechProperty (ZMod C.p)
    · rw [Matrix.rank, Matrix.mulVecLin_reindex, LinearMap.range_comp, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq, ← Matrix.rank]
      refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.Minv)
      rw [C.hInv]
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unique, Matrix.rank_one]

open Polynomial

structure RankUnitsCertificate {K : Type*} [Field K] [NumberField K]
  (O : Subalgebra ℤ K) where
  f : ℤ[X]
  l : List ℤ
  hl : ofList l = f
  hlz : l = l.dropTrailingZeros'
  hz : l ≠ []
  hAdj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) f)
  heq : O = integralClosure ℤ K
  P : List (List ℤ)
  SB : SturmBuilderOfList P l (List.derivative l).dropTrailingZeros
  k : ℕ
  r : ℕ
  hr : signChangesNInftyOfList P - signChangesInftyOfList P = k
  hreq : (k + (l.length - 1)) / 2 = r

open NumberField

lemma card_infinitePlace_of_RankUnitsCertificate {K : Type*} [Field K] [NumberField K]
  {O : Subalgebra ℤ K} (C : RankUnitsCertificate O) : Fintype.card (InfinitePlace K) = C.r := by
  rw [card_infinite_place_adjoin_root K _ ?_ C.hAdj, ← C.hl, Polynomial.map_map]
  erw [sturm_theorem_total_map_ofList ℝ (Real.IsRealClosed) (algebraMap ℤ ℝ) (Int.cast_strictMono) C.SB]
  rw [C.hr, Polynomial.natDegree_map_eq_of_injective]
  convert C.hreq
  rw [← natDegree_ofList C.l (C.hz), add_tsub_cancel_right]
  · rw [dropTrailingZeros_eq_dropTrailingZeros']
    exact C.hlz
  · exact RingHom.injective_int (algebraMap ℤ ℚ)
  · rw [Polynomial.map_ne_zero_iff (RingHom.injective_int (algebraMap ℤ ℚ)), ← C.hl ]
    intro hc
    exact (C.hz) (nil_of_ofList_eq_zero C.l ((dropTrailingZeros_eq_dropTrailingZeros' C.l ).symm ▸ C.hlz) hc)

lemma units_finrank_of_RankUnitsCertificate {K : Type*} [Field K] [NumberField K]
  {O : Subalgebra ℤ K} (C : RankUnitsCertificate O) :
  Module.finrank ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ))) = C.r - 1  := by
  conv =>
    left
    erw [C.heq, NumberField.Units.rank_modTorsion]
  unfold NumberField.Units.rank
  rw [card_infinitePlace_of_RankUnitsCertificate C]
