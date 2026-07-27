import IdealArithmetic.Examples.NF5_1_6250000_1.RI5_1_6250000_1
import IdealArithmetic.IdealArithmetic

/-- The number field has defining polynomial `X^5 + 10*X^3 - 10*X^2 - 15*X - 18`
with integral basis `[1, a, a^2, 1/2*a^3 - 1/2*a, 1/24*a^4 - 1/8*a^3 - 5/24*a^2 + 5/24*a - 1/4]`. -/


/- We define an ideal. -/
noncomputable def I : Ideal O :=
  Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![2, 3, -3, -1, -5]] i)))


/- Certify a `ℤ`-basis. -/
def A: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![2, 3, -3, -1, -5]]
    ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![2, 2, 1, 0, 0], ![1, 1, 0, 1, 0], ![0, 1, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0],
    ![0, 0, 0, 0, 3]], ![![2, 3, -3, -1, -5], ![-3, 0, 1, 1, 3], ![3, -3, 2, -1, 3],
    ![0, 3, -3, -3, -12], ![-2, -1, 1, 2, 4]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 0, 0, 1, 1], ![0, 3, 0, 0, -3]],
    ![![1, -2, 2, 1, 3], ![2, 3, 0, 0, -2]], ![![0, -1, 1, 1, 2], ![1, 1, 0, 0, -1]],
    ![![-1, -2, 2, 1, 4], ![2, 1, 0, 0, -1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-2, -2, 3, 0, 0], ![-1, -1, 0, 3, 0],
    ![0, -1, 0, 0, 3]], ![![3, 5, -3, -1, -5], ![-2, -2, 1, 1, 3], ![0, -3, 2, -1, 3],
    ![3, 8, -3, -3, -12], ![-2, -3, 1, 2, 4]]]
  hle1 := by decide
  hle2 := by decide

/- By multiplying the elements in the diagonal, we find the norm of this ideal. -/
lemma NI3N1 : Nat.card (O ⧸ I) = 9 :=
  ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide)
    (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A)

/- Proof that the polynomial `X ^ 2 + 1` is irreducible mod 3.  -/
def P3P1 : CertificateIrreducibleZModOfList' 3 2 2 1 [1, 0, 1] where
  m := 1
  P := ![2]
  exp := ![1]
  hneq := by decide
  hP := by decide
  hlen := by decide
  htr := by decide
  bit := ![1, 1]
  hbits := by decide
  h := ![[0, 1], [0, 2], [0, 1]]
  g := ![![[0, 1]], ![[0, 2]]]
  h' := ![![[0, 2], [0, 1]], ![[0, 1], [0, 2]]]
  hs := by decide
  hz := by decide
  hmul := by decide
  a := ![[], [1]]
  b := ![[], [0, 2]]
  hhz := by decide
  hhn := by decide
  hgcd := by decide

/- A certificate of primality-/
def CP : CertifiedPrimeIdeal' A 3 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P3P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1598, -1642, 1331, 3328, 9954]
  a := ![-11, 1, -10, -16, -45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1464, -5862, 1331, 3328, 9954]
  hcmem := by decide
  hpmem := by decide

/- The ideal `I` is prime.  -/
lemma isPrimeI3N1 : Ideal.IsPrime I :=
  CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl CP B_one_repr
