
import IdealArithmetic.Examples.NF3_1_112887_1.RI3_1_112887_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-21, 37, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-21, 37, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![62, 37, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-21, 37, 1], ![53, -42, 37], ![1961, -724, -42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-62, -37, 83]], ![![-1, 0, 1], ![-27, -17, 37], ![55, 10, -42]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [35, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 82], [0, 1]]
 g := ![![[44, 81], [60, 4], [27], [61], [6, 41], [1]], ![[53, 2], [42, 79], [27], [61], [29, 42], [1]]]
 h' := ![![[37, 82], [58, 74], [61, 2], [50, 39], [39, 12], [48, 37], [0, 1]], ![[0, 1], [57, 9], [52, 81], [82, 44], [68, 71], [6, 46], [37, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [34, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [35, 46, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![141, -35, -66]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![51, 29, -66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-37, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-37, 1, 0]] 
 ![![83, 0, 0], ![46, 1, 0], ![42, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-37, 1, 0], ![0, -37, 1], ![53, -21, -37]]]
  hmulB := by decide  
  f := ![![![556, -15, 0], ![1245, 0, 0]], ![![334, -9, 0], ![748, 0, 0]], ![![350, -9, 0], ![784, 1, 0]]]
  g := ![![![1, 0, 0], ![-46, 83, 0], ![-42, 0, 83]], ![![-1, 1, 0], ![20, -37, 1], ![31, -21, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-21, 37, 1]] ![![83, 0, 0], ![-37, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-3071, 83, 0]], ![![-1743, 3071, 83], ![830, -1411, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-37, 1, 0]]], ![![![-21, 37, 1]], ![![10, -17, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![32, 10, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![32, 10, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![32, 10, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![32, 10, 1], ![53, 11, 10], ![530, -157, 11]]]
  hmulB := by decide  
  f := ![![![-31, -10, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -10, 89]], ![![0, 0, 1], ![-3, -1, 10], ![2, -3, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [12, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 88], [0, 1]]
 g := ![![[34, 39], [40], [22], [30, 80], [14, 34], [1]], ![[53, 50], [40], [22], [53, 9], [26, 55], [1]]]
 h' := ![![[37, 88], [59, 22], [19, 60], [85, 72], [10, 76], [77, 37], [0, 1]], ![[0, 1], [72, 67], [14, 29], [79, 17], [63, 13], [22, 52], [37, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [80, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [12, 52, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-675, 629, -35]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, 11, -35]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-10, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-10, 1, 0]] 
 ![![89, 0, 0], ![79, 1, 0], ![78, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-10, 1, 0], ![0, -10, 1], ![53, -21, -10]]]
  hmulB := by decide  
  f := ![![![111, -11, 0], ![979, 0, 0]], ![![101, -10, 0], ![891, 0, 0]], ![![102, -10, 0], ![900, 1, 0]]]
  g := ![![![1, 0, 0], ![-79, 89, 0], ![-78, 0, 89]], ![![-1, 1, 0], ![8, -10, 1], ![28, -21, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![32, 10, 1]] ![![89, 0, 0], ![-10, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-890, 89, 0]], ![![2848, 890, 89], ![-267, -89, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-10, 1, 0]]], ![![![32, 10, 1]], ![![-3, -1, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)


lemma PB96I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 95 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 95 (by omega)

def PB96I2 : PrimesBelowBoundCertificateInterval O 79 95 96 where
  m := 2
  g := ![2, 2]
  P := ![83, 89]
  hP := PB96I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![7921, 89]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
  β := ![I83N1, I89N1]
  Il := ![[I83N1], [I89N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
