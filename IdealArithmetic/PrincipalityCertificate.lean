import IdealArithmetic.IdealArithmetic

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

/-- I include r as parameter because I want NeZero to be automatically inferred. -/
structure DiscreteLogCertificate {O : Type*} [CommRing O] {q : ℕ} (r : ℕ)
  [NeZero r] [hq : Fact $ Nat.Prime q] {I : Ideal O} (hcard : Nat.card (O ⧸ I) = q)
  {ζ : ℕ} (hr : IsPrimitiveRoot (ζ : ZMod q) (q - 1)) (p : ℕ) (x : O) (l : ZMod p) where
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

lemma apply_map_ZMod {O : Type*} [CommRing O] {q : ℕ} {r : ℕ}
    [NeZero r] [hq : Fact $ Nat.Prime q] {I : Ideal O} {hcard : Nat.card (O ⧸ I) = q}
    {ζ : ℕ} {hr : IsPrimitiveRoot (ζ : ZMod q) (q - 1)} {p : ℕ} {x : O} {l : ZMod p}
    (A : DiscreteLogCertificate r hcard hr p x l) :
      (modIdealToZMod (hq).out I hcard) ((Ideal.Quotient.mk I) x) = A.m := by
  have hmem : x - A.m ∈ I := by
    convert A.hmem
    rw [← table_add_list_eq_add A.B A.xcoord
      (fun (i : Fin r) => if i = 0 then (- A.m : ℤ) else 0) A.C A.hCeq, ← A.hxeq]
    simp [A.hone]
    exact  sub_eq_add_neg _ _
  rw [Ideal.Quotient.eq.2 hmem, map_intCast, map_intCast]


lemma eq_of_DiscreteLogCertificate {O : Type*} [CommRing O] {q : ℕ} {r : ℕ}
    [NeZero r] [hq : Fact $ Nat.Prime q] {I : Ideal O} {hcard : Nat.card (O ⧸ I) = q}
    {ζ : ℕ} {hr : IsPrimitiveRoot (ζ : ZMod q) (q - 1)} {p : ℕ} {x : O} {l : ZMod p}
    (A : DiscreteLogCertificate r hcard hr p x l) : LogFiniteZMod hcard hr p x = l := by
  simp only [LogFiniteZMod]
  dsimp
  rw [apply_map_ZMod A, ← A.hpow]
  convert LogFiniteRing_of_pow ?_ ?_ A.k
  · exact A.heql
  · rw [ZMod.card_units_eq_totient, Nat.totient_prime hq.out]
    exact A.hpdvd



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






  --MatrixLogZMod p hcard x hr i j = MatrixLogProd p (F q) (φ hcard) x _ (hr_aux hr) i j := by rfl
