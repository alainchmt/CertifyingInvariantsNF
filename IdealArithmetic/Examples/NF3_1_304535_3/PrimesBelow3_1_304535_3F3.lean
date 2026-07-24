
import IdealArithmetic.Examples.NF3_1_304535_3.RI3_1_304535_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-646, -54, -41]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-646, -54, -41]] 
 ![![139, 0, 0], ![0, 139, 0], ![70, 42, 1]] where
  M :=![![![-646, -54, -41], ![-4305, -359, -270], ![-5670, -483, -359]]]
  hmulB := by decide  
  f := ![![![11, -3, 1]], ![![105, 4, -15]], ![![35, 0, -4]]]
  g := ![![![16, 12, -41], ![105, 79, -270], ![140, 105, -359]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [2, 130, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 138], [0, 1]]
 g := ![![[65, 91], [49, 54], [107], [9, 34], [4], [81], [1]], ![[50, 48], [118, 85], [107], [37, 105], [4], [81], [1]]]
 h' := ![![[9, 138], [41, 62], [110, 101], [121, 78], [75, 112], [120, 137], [137, 9], [0, 1]], ![[0, 1], [43, 77], [46, 38], [128, 61], [110, 27], [102, 2], [79, 130], [9, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118]]
 b := ![[], [82, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [2, 130, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![212, -123, -132]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![68, 39, -132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -3, 1]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![11, -3, 1]] 
 ![![139, 0, 0], ![68, 1, 0], ![76, 0, 1]] where
  M :=![![![11, -3, 1], ![105, 4, -15], ![-315, 42, 4]]]
  hmulB := by decide  
  f := ![![![-646, -54, -41]], ![![-347, -29, -22]], ![![-394, -33, -25]]]
  g := ![![![1, -3, 1], ![7, 4, -15], ![-25, 42, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-646, -54, -41]] ![![11, -3, 1]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-22, 60, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-22, 60, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![127, 60, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-22, 60, 1], ![105, -29, 300], ![6300, -399, -29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-127, -60, 149]], ![![-1, 0, 1], ![-255, -121, 300], ![67, 9, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [28, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 148], [0, 1]]
 g := ![![[142, 16], [64], [125, 7], [102], [12, 102], [123], [1]], ![[0, 133], [64], [7, 142], [102], [38, 47], [123], [1]]]
 h' := ![![[47, 148], [110, 4], [76, 141], [78, 56], [111, 129], [22, 20], [121, 47], [0, 1]], ![[0, 1], [0, 145], [147, 8], [28, 93], [65, 20], [68, 129], [95, 102], [47, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [72, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [28, 102, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1333, 73, 257]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-228, -103, 257]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-2, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-2, 1, 0]] 
 ![![149, 0, 0], ![147, 1, 0], ![29, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-2, 1, 0], ![0, -2, 5], ![105, -7, -2]]]
  hmulB := by decide  
  f := ![![![155, -77, 0], ![11473, 0, 0]], ![![153, -76, 0], ![11325, 0, 0]], ![![31, -15, -1], ![2295, 30, 0]]]
  g := ![![![1, 0, 0], ![-147, 149, 0], ![-29, 0, 149]], ![![-1, 1, 0], ![1, -2, 5], ![8, -7, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-22, 60, 1]] ![![149, 0, 0], ![-2, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-298, 149, 0]], ![![-3278, 8940, 149], ![149, -149, 298]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-2, 1, 0]]], ![![![-22, 60, 1]], ![![1, -1, 2]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![48, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![48, 1, 0]] 
 ![![151, 0, 0], ![48, 1, 0], ![113, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![48, 1, 0], ![0, 48, 5], ![105, -7, 48]]]
  hmulB := by decide  
  f := ![![![3121, 65, 0], ![-9815, 0, 0]], ![![912, 19, 0], ![-2868, 0, 0]], ![![2279, 9, -4], ![-7167, 121, 0]]]
  g := ![![![1, 0, 0], ![-48, 151, 0], ![-113, 0, 151]], ![![0, 1, 0], ![-19, 48, 5], ![-33, -7, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-31, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-31, 1, 0]] 
 ![![151, 0, 0], ![120, 1, 0], ![140, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-31, 1, 0], ![0, -31, 5], ![105, -7, -31]]]
  hmulB := by decide  
  f := ![![![1582, -51, 0], ![7701, 0, 0]], ![![1272, -41, 0], ![6192, 0, 0]], ![![1484, -23, -4], ![7224, 121, 0]]]
  g := ![![![1, 0, 0], ![-120, 151, 0], ![-140, 0, 151]], ![![-1, 1, 0], ![20, -31, 5], ![35, -7, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-17, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-17, 1, 0]] 
 ![![151, 0, 0], ![134, 1, 0], ![63, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-17, 1, 0], ![0, -17, 5], ![105, -7, -17]]]
  hmulB := by decide  
  f := ![![![1531, -90, 0], ![13590, 0, 0]], ![![1344, -79, 0], ![11930, 0, 0]], ![![657, -25, -4], ![5832, 121, 0]]]
  g := ![![![1, 0, 0], ![-134, 151, 0], ![-63, 0, 151]], ![![-1, 1, 0], ![13, -17, 5], ![14, -7, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![48, 1, 0]] ![![151, 0, 0], ![-31, 1, 0]]
  ![![151, 0, 0], ![-56, -57, 1]] where
 M := ![![![22801, 0, 0], ![-4681, 151, 0]], ![![7248, 151, 0], ![-1488, 17, 5]]]
 hmul := by decide  
 g := ![![![![151, 0, 0], ![0, 0, 0]], ![![25, 58, -1], ![151, 0, 0]]], ![![![48, 1, 0], ![0, 0, 0]], ![![-8, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-56, -57, 1]] ![![151, 0, 0], ![-17, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-2567, 151, 0]], ![![-8456, -8607, 151], ![1057, 906, -302]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-17, 1, 0]]], ![![![-56, -57, 1]], ![![7, 6, -2]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)


lemma PB157I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 156 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 156 (by omega)

def PB157I3 : PrimesBelowBoundCertificateInterval O 137 156 157 where
  m := 3
  g := ![2, 2, 3]
  P := ![139, 149, 151]
  hP := PB157I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I139N1, I149N1, I151N0, I151N1, I151N2]
  Il := ![[I139N1], [I149N1], [I151N0, I151N1, I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
