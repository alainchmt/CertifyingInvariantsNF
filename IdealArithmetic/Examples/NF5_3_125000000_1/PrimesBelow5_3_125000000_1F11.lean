
import IdealArithmetic.Examples.NF5_3_125000000_1.RI5_3_125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp541 : Fact (Nat.Prime 541) := {out := by norm_num}

def I541N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23011, 2337, -2632, 1815, -2044]] i)))

def SI541N0: IdealEqSpanCertificate' Table ![![23011, 2337, -2632, 1815, -2044]] 
 ![![541, 0, 0, 0, 0], ![0, 541, 0, 0, 0], ![0, 0, 541, 0, 0], ![309, 259, 41, 1, 0], ![315, 376, 201, 0, 1]] where
  M :=![![![23011, 2337, -2632, 1815, -2044], ![-40880, -4149, 4674, -3220, 3630], ![36300, 3677, -4149, 2859, -3220], ![-11760, -1170, 1340, -929, 1044], ![10440, 1054, -1170, 818, -929]]]
  hmulB := by decide  
  f := ![![![-9, 7, 14, 3, 2]], ![![40, 29, 14, 26, 6]], ![![60, 63, 29, 11, 26]], ![![19, 23, 17, 15, 6]], ![![45, 48, 29, 24, 15]]]
  g := ![![![196, 556, 617, 1815, -2044], ![-350, -989, -1096, -3220, 3630], ![309, 876, 972, 2859, -3220], ![-99, -283, -315, -929, 1044], ![93, 256, 281, 818, -929]]]
  hle1 := by decide   
  hle2 := by decide  


def P541P0 : CertificateIrreducibleZModOfList' 541 3 2 9 [264, 236, 277, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [236, 483, 192], [28, 57, 349], [0, 1]]
 g := ![![[286, 334, 26], [269, 513], [470, 501, 109], [192, 505, 498], [345, 358, 498], [421, 446], [189, 41], [264, 1], []], ![[411, 221, 243, 196], [156, 525], [191, 239, 92, 136], [115, 309, 236, 80], [412, 64, 533, 187], [529, 330], [36, 420], [536, 3], [497, 76]], ![[303, 162, 356, 449], [261, 484], [311, 157, 139, 101], [226, 100, 150, 79], [232, 381, 14, 324], [23, 367], [316, 80], [64, 118], [340, 76]]]
 h' := ![![[236, 483, 192], [89, 113, 244], [350, 231, 355], [166, 515, 138], [349, 513, 223], [151, 133, 223], [410, 98, 304], [93, 188, 212], [0, 0, 1], [0, 1]], ![[28, 57, 349], [157, 7, 439], [15, 203, 208], [67, 230, 169], [223, 288, 302], [151, 147, 377], [339, 486, 438], [286, 446, 31], [228, 273, 57], [236, 483, 192]], ![[0, 1], [193, 421, 399], [131, 107, 519], [368, 337, 234], [174, 281, 16], [156, 261, 482], [122, 498, 340], [82, 448, 298], [289, 268, 483], [28, 57, 349]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 73], []]
 b := ![[], [534, 267, 442], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI541N0 : CertifiedPrimeIdeal' SI541N0 541 where
  n := 3
  hpos := by decide
  P := [264, 236, 277, 1]
  hirr := P541P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17396, 35625, 67170, 104461, 63904]
  a := ![0, -2, -3, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-96905, -94358, -31535, 104461, 63904]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI541N0 : Ideal.IsPrime I541N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI541N0 B_one_repr
lemma NI541N0 : Nat.card (O ⧸ I541N0) = 158340421 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI541N0

def I541N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 1, -6, -1, 2]] i)))

def SI541N1: IdealEqSpanCertificate' Table ![![11, 1, -6, -1, 2]] 
 ![![541, 0, 0, 0, 0], ![109, 1, 0, 0, 0], ![281, 0, 1, 0, 0], ![320, 0, 0, 1, 0], ![413, 0, 0, 0, 1]] where
  M :=![![![11, 1, -6, -1, 2], ![40, 29, 2, -14, -2], ![-20, 9, 29, 3, -14], ![-160, -94, 8, 43, 4], ![40, -52, -94, 6, 43]]]
  hmulB := by decide  
  f := ![![![831, -325, -540, -17, -228]], ![![159, -70, -110, -5, -46]], ![![431, -174, -285, -10, -120]], ![![480, -202, -324, -13, -136]], ![![623, -263, -422, -17, -177]]]
  g := ![![![2, 1, -6, -1, 2], ![3, 29, 2, -14, -2], ![-8, 9, 29, 3, -14], ![-14, -94, 8, 43, 4], ![23, -52, -94, 6, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI541N1 : Nat.card (O ⧸ I541N1) = 541 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI541N1)

lemma isPrimeI541N1 : Ideal.IsPrime I541N1 := prime_ideal_of_norm_prime hp541.out _ NI541N1

def I541N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, 3, -4, 4, -4]] i)))

def SI541N2: IdealEqSpanCertificate' Table ![![39, 3, -4, 4, -4]] 
 ![![541, 0, 0, 0, 0], ![350, 1, 0, 0, 0], ![424, 0, 1, 0, 0], ![283, 0, 0, 1, 0], ![247, 0, 0, 0, 1]] where
  M :=![![![39, 3, -4, 4, -4], ![-80, -13, 6, -4, 8], ![80, 11, -13, 2, -4], ![0, 16, 8, -9, -2], ![-20, -8, 16, 9, -9]]]
  hmulB := by decide  
  f := ![![![-3781, -1121, 838, -560, 436]], ![![-2430, -721, 538, -360, 280]], ![![-2984, -885, 661, -442, 344]], ![![-1963, -583, 434, -291, 226]], ![![-1747, -519, 386, -259, 201]]]
  g := ![![![1, 3, -4, 4, -4], ![2, -13, 6, -4, 8], ![4, 11, -13, 2, -4], ![-11, 16, 8, -9, -2], ![-8, -8, 16, 9, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI541N2 : Nat.card (O ⧸ I541N2) = 541 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI541N2)

lemma isPrimeI541N2 : Ideal.IsPrime I541N2 := prime_ideal_of_norm_prime hp541.out _ NI541N2
def MulI541N0 : IdealMulLeCertificate' Table 
  ![![23011, 2337, -2632, 1815, -2044]] ![![11, 1, -6, -1, 2]]
  ![![27081, 2774, -3064, 2156, -2436]] where
 M := ![![![27081, 2774, -3064, 2156, -2436]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI541N1 : IdealMulLeCertificate' Table 
  ![![27081, 2774, -3064, 2156, -2436]] ![![39, 3, -4, 4, -4]]
  ![![541, 0, 0, 0, 0]] where
 M := ![![![637839, 65461, -73576, 49772, -56264]]]
 hmul := by decide  
 g := ![![![![1179, 121, -136, 92, -104]]]]
 hle2 := by decide  


def PBC541 : ContainsPrimesAboveP 541 ![I541N0, I541N1, I541N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI541N0
    exact isPrimeI541N1
    exact isPrimeI541N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 541 (by decide) (𝕀 ⊙ MulI541N0 ⊙ MulI541N1)


lemma PB547I11_primes (p : ℕ) :
  p ∈ Set.range ![541] ↔ Nat.Prime p ∧ 523 < p ∧ p ≤ 546 := by
  rw [← List.mem_ofFn']
  convert primes_range 523 546 (by omega)

def PB547I11 : PrimesBelowBoundCertificateInterval O 523 546 547 where
  m := 1
  g := ![3]
  P := ![541]
  hP := PB547I11_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I541N0, I541N1, I541N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC541
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![158340421, 541, 541]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI541N0
      exact NI541N1
      exact NI541N2
  β := ![I541N1, I541N2]
  Il := ![[I541N1, I541N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
