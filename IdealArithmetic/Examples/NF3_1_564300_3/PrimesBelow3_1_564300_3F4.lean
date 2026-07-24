
import IdealArithmetic.Examples.NF3_1_564300_3.RI3_1_564300_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0]] 
 ![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [48, 172, 137, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 98, 66], [151, 98, 131], [0, 1]]
 g := ![![[6, 44, 19], [60, 70], [8, 24, 136], [184, 60], [194, 15], [133, 54], [1]], ![[33, 25, 21, 152], [155, 37], [139, 149, 104, 18], [12, 65], [148, 62], [149, 163], [37, 96, 13, 73]], ![[92, 138, 134, 123], [91, 36], [140, 182, 2, 98], [14, 174], [182, 155], [172, 178], [180, 101, 118, 124]]]
 h' := ![![[106, 98, 66], [175, 2, 120], [10, 34, 55], [196, 105, 147], [44, 60, 116], [57, 106, 58], [149, 25, 60], [0, 1]], ![[151, 98, 131], [10, 123, 72], [84, 7, 148], [172, 60, 60], [123, 103, 159], [174, 112, 72], [148, 148, 44], [106, 98, 66]], ![[0, 1], [135, 72, 5], [13, 156, 191], [138, 32, 187], [66, 34, 119], [118, 176, 67], [10, 24, 93], [151, 98, 131]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 31], []]
 b := ![[], [0, 101, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [48, 172, 137, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10638, -9850, -4137]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![54, -50, -21]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀

instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0]] 
 ![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [71, 51, 183, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [183, 129, 155], [32, 69, 44], [0, 1]]
 g := ![![[174, 87, 56], [35, 167, 102], [189, 109, 115], [99, 162], [19, 165], [76, 57], [1]], ![[142, 54, 84, 121], [89, 119, 47, 66], [148, 47, 184, 155], [70, 66], [72, 116], [135, 31], [108, 34, 4, 187]], ![[101, 97, 55, 189], [35, 95, 76, 192], [144, 191, 30, 174], [7, 140], [198, 70], [47, 162], [56, 125, 158, 12]]]
 h' := ![![[183, 129, 155], [102, 122, 97], [113, 198, 36], [191, 125, 48], [102, 191, 19], [43, 115, 31], [128, 148, 16], [0, 1]], ![[32, 69, 44], [61, 188, 131], [192, 115, 140], [66, 66, 1], [114, 136, 71], [98, 98, 64], [176, 8, 164], [183, 129, 155]], ![[0, 1], [118, 88, 170], [189, 85, 23], [156, 8, 150], [102, 71, 109], [35, 185, 104], [136, 43, 19], [32, 69, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 60], []]
 b := ![[], [77, 112, 128], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [71, 51, 183, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12338, 19104, -28656]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-62, 96, -144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def PBC199 : ContainsPrimesAboveP 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![199, 0, 0]]) timesTableT_eq_Table B_one_repr 199 (by decide) 𝕀

instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![6, 1, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![6, 1, 0]] 
 ![![211, 0, 0], ![6, 1, 0], ![35, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![6, 1, 0], ![0, 6, 5], ![30, -30, 6]]]
  hmulB := by decide  
  f := ![![![997, 166, 0], ![-35026, 0, 0]], ![![18, 3, 0], ![-632, 0, 0]], ![![161, 22, -4], ![-5656, 169, 0]]]
  g := ![![![1, 0, 0], ![-6, 211, 0], ![-35, 0, 211]], ![![0, 1, 0], ![-1, 6, 5], ![0, -30, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N0 : Nat.card (O ⧸ I211N0) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N0)

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := prime_ideal_of_norm_prime hp211.out _ NI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 1]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![31, 0, 1]] 
 ![![211, 0, 0], ![30, 1, 0], ![31, 0, 1]] where
  M :=![![![31, 0, 1], ![30, 1, 0], ![0, 6, 1]]]
  hmulB := by decide  
  f := ![![![1, 6, -1]], ![![0, 1, 0]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![0, 1, 0], ![-1, 6, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-36, 1, 0]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-36, 1, 0]] 
 ![![211, 0, 0], ![175, 1, 0], ![205, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-36, 1, 0], ![0, -36, 5], ![30, -30, -36]]]
  hmulB := by decide  
  f := ![![![6553, -182, 0], ![38402, 0, 0]], ![![5437, -151, 0], ![31862, 0, 0]], ![![6367, -148, -4], ![37312, 169, 0]]]
  g := ![![![1, 0, 0], ![-175, 211, 0], ![-205, 0, 211]], ![![-1, 1, 0], ![25, -36, 5], ![60, -30, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![6, 1, 0]] ![![31, 0, 1]]
  ![![211, 0, 0], ![36, -35, 1]] where
 M := ![![![6541, 0, 211]], ![![216, 1, 6]]]
 hmul := by decide  
 g := ![![![![-5, 35, 0], ![211, 0, 0]]], ![![![0, 1, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![36, -35, 1]] ![![211, 0, 0], ![-36, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-7596, 211, 0]], ![![7596, -7385, 211], ![-1266, 1266, -211]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-36, 1, 0]]], ![![![36, -35, 1]], ![![-6, 6, -1]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1, I211N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
    exact isPrimeI211N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0 ⊙ MulI211N1)


lemma PB213I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 212 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 212 (by omega)

def PB213I4 : PrimesBelowBoundCertificateInterval O 193 212 213 where
  m := 3
  g := ![1, 1, 3]
  P := ![197, 199, 211]
  hP := PB213I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0]
    · exact ![I211N0, I211N1, I211N2]
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
    · exact ![7645373]
    · exact ![7880599]
    · exact ![211, 211, 211]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
      exact NI211N2
  β := ![I211N0, I211N1, I211N2]
  Il := ![[], [], [I211N0, I211N1, I211N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
