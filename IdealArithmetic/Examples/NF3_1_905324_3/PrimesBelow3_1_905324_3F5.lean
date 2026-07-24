
import IdealArithmetic.Examples.NF3_1_905324_3.RI3_1_905324_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![16, 110, 1]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![16, 110, 1]] 
 ![![263, 0, 0], ![0, 263, 0], ![16, 110, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![16, 110, 1], ![182, 2, 110], ![20020, -1358, 2]]]
  hmulB := by decide  
  f := ![![![-15, -110, -1], ![263, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -110, 263]], ![![0, 0, 1], ![-6, -46, 110], ![76, -6, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [90, 123, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [140, 262], [0, 1]]
 g := ![![[203, 83], [232, 129], [235, 133], [88], [11], [157], [138], [1]], ![[251, 180], [145, 134], [182, 130], [88], [11], [157], [138], [1]]]
 h' := ![![[140, 262], [160, 95], [153, 38], [66, 50], [126, 183], [255, 167], [151, 169], [173, 140], [0, 1]], ![[0, 1], [47, 168], [213, 225], [228, 213], [235, 80], [228, 96], [141, 94], [48, 123], [140, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [218]]
 b := ![[], [260, 109]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [90, 123, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![454, 31, -136]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, 57, -136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-110, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-110, 1, 0]] 
 ![![263, 0, 0], ![153, 1, 0], ![261, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-110, 1, 0], ![0, -110, 1], ![182, -14, -110]]]
  hmulB := by decide  
  f := ![![![9571, -87, 0], ![22881, 0, 0]], ![![5721, -52, 0], ![13677, 0, 0]], ![![9397, -85, 0], ![22465, 1, 0]]]
  g := ![![![1, 0, 0], ![-153, 263, 0], ![-261, 0, 263]], ![![-1, 1, 0], ![63, -110, 1], ![118, -14, -110]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![16, 110, 1]] ![![263, 0, 0], ![-110, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![-28930, 263, 0]], ![![4208, 28930, 263], ![-1578, -12098, 0]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![-110, 1, 0]]], ![![![16, 110, 1]], ![![-6, -46, 0]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![61, 100, 1]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0], ![61, 100, 1]] 
 ![![269, 0, 0], ![0, 269, 0], ![61, 100, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![61, 100, 1], ![182, 47, 100], ![18200, -1218, 47]]]
  hmulB := by decide  
  f := ![![![-60, -100, -1], ![269, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-61, -100, 269]], ![![0, 0, 1], ![-22, -37, 100], ![57, -22, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 2 2 8 [150, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [242, 268], [0, 1]]
 g := ![![[210, 217], [136], [167, 260], [121, 173], [138], [256], [191], [1]], ![[0, 52], [136], [141, 9], [23, 96], [138], [256], [191], [1]]]
 h' := ![![[242, 268], [57, 32], [236, 58], [142, 246], [224, 150], [91, 243], [37, 253], [119, 242], [0, 1]], ![[0, 1], [0, 237], [15, 211], [225, 23], [209, 119], [255, 26], [200, 16], [41, 27], [242, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [225, 196]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 2
  hpos := by decide
  P := [150, 27, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2060, 1756, -47]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, 24, -47]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![-100, 1, 0]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![269, 0, 0], ![-100, 1, 0]] 
 ![![269, 0, 0], ![169, 1, 0], ![222, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![-100, 1, 0], ![0, -100, 1], ![182, -14, -100]]]
  hmulB := by decide  
  f := ![![![22901, -229, 0], ![61601, 0, 0]], ![![14401, -144, 0], ![38737, 0, 0]], ![![18838, -188, 0], ![50672, 1, 0]]]
  g := ![![![1, 0, 0], ![-169, 269, 0], ![-222, 0, 269]], ![![-1, 1, 0], ![62, -100, 1], ![92, -14, -100]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![269, 0, 0], ![61, 100, 1]] ![![269, 0, 0], ![-100, 1, 0]]
  ![![269, 0, 0]] where
 M := ![![![72361, 0, 0], ![-26900, 269, 0]], ![![16409, 26900, 269], ![-5918, -9953, 0]]]
 hmul := by decide  
 g := ![![![![269, 0, 0]], ![![-100, 1, 0]]], ![![![61, 100, 1]], ![![-22, -37, 0]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0)


lemma PB270I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 269 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 269 (by omega)

def PB270I5 : PrimesBelowBoundCertificateInterval O 257 269 270 where
  m := 2
  g := ![2, 2]
  P := ![263, 269]
  hP := PB270I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC263
    · exact PBC269
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![69169, 263]
    · exact ![72361, 269]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
  β := ![I263N1, I269N1]
  Il := ![[I263N1], [I269N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
