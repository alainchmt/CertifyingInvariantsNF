
import IdealArithmetic.Examples.NF3_1_565068_1.RI3_1_565068_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-78, 38, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-78, 38, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![119, 38, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-78, 38, 1], ![-45, -69, 190], ![-1701, -1111, -107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-119, -38, 197]], ![![-1, 0, 1], ![-115, -37, 190], ![56, 15, -107]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [32, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [134, 196], [0, 1]]
 g := ![![[82, 109], [39], [184, 85], [164], [70], [9], [134, 1]], ![[110, 88], [39], [148, 112], [164], [70], [9], [71, 196]]]
 h' := ![![[134, 196], [24, 75], [22, 165], [80, 26], [194, 178], [55, 142], [46, 194], [0, 1]], ![[0, 1], [27, 122], [68, 32], [18, 171], [12, 19], [171, 55], [38, 3], [134, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [126, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [32, 63, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-859, -1895, -2896]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1745, 549, -2896]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![7, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![7, 1, 0]] 
 ![![197, 0, 0], ![7, 1, 0], ![107, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![7, 1, 0], ![0, 8, 5], ![-45, -29, 7]]]
  hmulB := by decide  
  f := ![![![1142, 163, 0], ![-32111, 0, 0]], ![![28, 4, 0], ![-787, 0, 0]], ![![618, 85, -2], ![-17377, 79, 0]]]
  g := ![![![1, 0, 0], ![-7, 197, 0], ![-107, 0, 197]], ![![0, 1, 0], ![-3, 8, 5], ![-3, -29, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-78, 38, 1]] ![![197, 0, 0], ![7, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![1379, 197, 0]], ![![-15366, 7486, 197], ![-591, 197, 197]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![7, 1, 0]]], ![![![-78, 38, 1]], ![![-3, 1, 1]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![72, 1, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![72, 1, 0]] 
 ![![199, 0, 0], ![72, 1, 0], ![103, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![72, 1, 0], ![0, 73, 5], ![-45, -29, 72]]]
  hmulB := by decide  
  f := ![![![2953, 41, 0], ![-8159, 0, 0]], ![![1080, 15, 0], ![-2984, 0, 0]], ![![1561, 7, -1], ![-4313, 40, 0]]]
  g := ![![![1, 0, 0], ![-72, 199, 0], ![-103, 0, 199]], ![![0, 1, 0], ![-29, 73, 5], ![-27, -29, 72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-47, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-47, 1, 0]] 
 ![![199, 0, 0], ![152, 1, 0], ![85, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-47, 1, 0], ![0, -46, 5], ![-45, -29, -47]]]
  hmulB := by decide  
  f := ![![![3573, -76, 0], ![15124, 0, 0]], ![![2774, -59, 0], ![11742, 0, 0]], ![![1563, -24, -1], ![6616, 40, 0]]]
  g := ![![![1, 0, 0], ![-152, 199, 0], ![-85, 0, 199]], ![![-1, 1, 0], ![33, -46, 5], ![42, -29, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-26, 1, 0]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-26, 1, 0]] 
 ![![199, 0, 0], ![173, 1, 0], ![69, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-26, 1, 0], ![0, -25, 5], ![-45, -29, -26]]]
  hmulB := by decide  
  f := ![![![651, -25, 0], ![4975, 0, 0]], ![![573, -22, 0], ![4379, 0, 0]], ![![261, -5, -1], ![1995, 40, 0]]]
  g := ![![![1, 0, 0], ![-173, 199, 0], ![-69, 0, 199]], ![![-1, 1, 0], ![20, -25, 5], ![34, -29, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![72, 1, 0]] ![![199, 0, 0], ![-47, 1, 0]]
  ![![199, 0, 0], ![-40, 45, 1]] where
 M := ![![![39601, 0, 0], ![-9353, 199, 0]], ![![14328, 199, 0], ![-3384, 26, 5]]]
 hmul := by decide  
 g := ![![![![199, 0, 0], ![0, 0, 0]], ![![-7, -44, -1], ![199, 0, 0]]], ![![![72, 1, 0], ![0, 0, 0]], ![![-16, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-40, 45, 1]] ![![199, 0, 0], ![-26, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-5174, 199, 0]], ![![-7960, 8955, 199], ![995, -1194, 199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-26, 1, 0]]], ![![![-40, 45, 1]], ![![5, -6, 1]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1, I199N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
    exact isPrimeI199N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0 ⊙ MulI199N1)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [195, 57, 197, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 168, 115], [209, 42, 96], [0, 1]]
 g := ![![[1, 92, 81], [120, 191, 24], [175, 170], [54, 171], [186, 51, 173], [93, 196], [1]], ![[33, 131, 152, 158], [210, 105, 165, 128], [193, 171], [198, 151], [58, 94, 167, 22], [127, 105], [44, 51, 150, 198]], ![[26, 150, 158, 201], [143, 185, 208, 172], [40, 109], [194, 52], [30, 193, 43, 44], [94, 126], [120, 156, 54, 13]]]
 h' := ![![[16, 168, 115], [21, 11, 202], [29, 21, 92], [82, 137, 176], [22, 102, 63], [56, 20, 157], [16, 154, 14], [0, 1]], ![[209, 42, 96], [62, 195, 43], [57, 99, 160], [61, 200, 148], [67, 11, 28], [199, 194, 32], [158, 99, 152], [16, 168, 115]], ![[0, 1], [29, 5, 177], [32, 91, 170], [206, 85, 98], [30, 98, 120], [196, 208, 22], [13, 169, 45], [209, 42, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 100], []]
 b := ![[], [117, 95, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [195, 57, 197, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![204670, 136517, 4853]
  a := ![-1, 1, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![970, 647, 23]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀



lemma PB213I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 212 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 212 (by omega)

def PB213I4 : PrimesBelowBoundCertificateInterval O 193 212 213 where
  m := 3
  g := ![2, 3, 1]
  P := ![197, 199, 211]
  hP := PB213I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![199, 199, 199]
    · exact ![9393931]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
      exact NI199N2
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
  β := ![I197N1, I199N0, I199N1, I199N2]
  Il := ![[I197N1], [I199N0, I199N1, I199N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
