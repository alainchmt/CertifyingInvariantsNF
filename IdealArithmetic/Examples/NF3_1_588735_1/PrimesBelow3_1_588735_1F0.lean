
import IdealArithmetic.Examples.NF3_1_588735_1.RI3_1_588735_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 3 2 1 [1, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [0, 1, 1], [0, 1]]
 g := ![![[]], ![[0, 1]], ![[0, 1]]]
 h' := ![![[0, 0, 1], [0, 1]], ![[0, 1, 1], [0, 0, 1]], ![[0, 1], [0, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], []]
 b := ![[], [1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 3
  hpos := by decide
  P := [1, 1, 0, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1616, 36750, -109940]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![808, 18375, -54970]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 8 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def PBC2 : ContainsPrimesAboveP 2 ![I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![2, 0, 0]]) timesTableT_eq_Table B_one_repr 2 (by decide) 𝕀


def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![0, 1, 0]] 
 ![![3, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![0, 1, 0], ![2, -1, 5], ![55, -30, 1]]]
  hmulB := by decide  
  f := ![![![-1, 2, -5], ![-3, 3, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-1, 0, -3], ![2, 2, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![-1, 0, 3]], ![![0, 1, 0], ![-1, -1, 5], ![18, -30, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![3, 0, 0], ![19, 1, 1]] where
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![0, 3, 0], ![2, -1, 5]]]
 hmul := by decide  
 g := ![![![![-16, -1, -1], ![3, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-12, -1, 1], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![19, 1, 1]] ![![3, 0, 0], ![0, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![57, 3, 3], ![57, -12, 6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![0, 1, 0]]], ![![![19, 1, 1]], ![![19, -4, 2]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![2, 1, 0]] 
 ![![5, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![2, 1, 0], ![2, 1, 5], ![55, -30, 3]]]
  hmulB := by decide  
  f := ![![![-1, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-20, 13, -1], ![-5, 0, 2]]]
  g := ![![![1, 0, 0], ![-2, 5, 0], ![0, 0, 5]], ![![0, 1, 0], ![0, 1, 5], ![23, -30, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-21, 1, -1]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-21, 1, -1]] 
 ![![5, 0, 0], ![4, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-21, 1, -1], ![-53, 8, 4], ![45, -35, 10]]]
  hmulB := by decide  
  f := ![![![23, -12, -12], ![-20, 10, 0]], ![![10, -9, -10], ![-18, 8, 0]], ![![4, 2, 3], ![6, -2, 0]]]
  g := ![![![1, 0, 0], ![-4, 5, 0], ![0, 0, 5]], ![![-5, 1, -1], ![-17, 8, 4], ![37, -35, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![-21, 1, -1]]
  ![![5, 0, 0], ![20, 0, 1]] where
 M := ![![![25, 0, 0], ![-105, 5, -5]], ![![10, 5, 0], ![-95, 10, 2]]]
 hmul := by decide  
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![-1, 1, 0], ![-5, 0, 0]]], ![![![2, 1, 0], ![0, 0, 0]], ![![-7, 2, 1], ![-3, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![20, 0, 1]] ![![5, 0, 0], ![-21, 1, -1]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![-105, 5, -5]], ![![100, 0, 5], ![-375, -15, -10]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![-21, 1, -1]]], ![![![20, 0, 1]], ![![-75, -3, -2]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![2, -1, 5], ![55, -30, 1]]]
  hmulB := by decide  
  f := ![![![-7, 3, -20], ![7, 28, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-6, 3, -17], ![3, 24, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![-6, 0, 7]], ![![0, 1, 0], ![-4, -1, 5], ![7, -30, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0], ![20, -3, 1]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![0, 7, 0], ![2, -1, 5]]]
 hmul := by decide  
 g := ![![![![-13, 3, -1], ![7, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![6, -1, 1], ![-2, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![20, -3, 1]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![140, -21, 7], ![49, -7, -14]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![0, 1, 0]]], ![![![20, -3, 1]], ![![7, -1, -2]]]]
 hle2 := by decide  

def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![15, 1, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![15, 1, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![4, 1, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![15, 1, 1], ![57, -16, 6], ![65, -25, -14]]]
  hmulB := by decide  
  f := ![![![-14, -1, -1], ![11, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -1, 11]], ![![1, 0, 1], ![3, -2, 6], ![11, -1, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 10], [0, 1]]
 g := ![![[5, 1], [2, 9], [1]], ![[8, 10], [7, 2], [1]]]
 h' := ![![[3, 10], [10, 10], [5, 3], [0, 1]], ![[0, 1], [7, 1], [3, 8], [3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [6, 8, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5339, 4630, -4841]
  a := ![5, -5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1275, 861, -4841]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![5, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![5, 1, 0]] 
 ![![11, 0, 0], ![5, 1, 0], ![3, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![5, 1, 0], ![2, 4, 5], ![55, -30, 6]]]
  hmulB := by decide  
  f := ![![![92, 245, 315], ![77, -693, 0]], ![![41, 109, 140], ![34, -308, 0]], ![![26, 67, 86], ![19, -189, 0]]]
  g := ![![![1, 0, 0], ![-5, 11, 0], ![-3, 0, 11]], ![![0, 1, 0], ![-3, 4, 5], ![17, -30, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![15, 1, 1]] ![![11, 0, 0], ![5, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![55, 11, 0]], ![![165, 11, 11], ![132, -11, 11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![5, 1, 0]]], ![![![15, 1, 1]], ![![12, -1, 1]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -2, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![3, -2, 1]] 
 ![![13, 0, 0], ![0, 1, 0], ![3, 0, 1]] where
  M :=![![![3, -2, 1], ![51, -25, -9], ![-100, 65, -29]]]
  hmulB := by decide  
  f := ![![![-1310, -7, -43]], ![![-183, -1, -6]], ![![-365, -2, -12]]]
  g := ![![![0, -2, 1], ![6, -25, -9], ![-1, 65, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![3, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![3, 1, 0]] 
 ![![13, 0, 0], ![3, 1, 0], ![7, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![3, 1, 0], ![2, 2, 5], ![55, -30, 4]]]
  hmulB := by decide  
  f := ![![![67, 70, 180], ![26, -468, 0]], ![![13, 15, 40], ![14, -104, 0]], ![![34, 37, 97], ![23, -252, 0]]]
  g := ![![![1, 0, 0], ![-3, 13, 0], ![-7, 0, 13]], ![![0, 1, 0], ![-3, 2, 5], ![9, -30, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-3, 1, 0]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-3, 1, 0]] 
 ![![13, 0, 0], ![10, 1, 0], ![11, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-3, 1, 0], ![2, -4, 5], ![55, -30, -2]]]
  hmulB := by decide  
  f := ![![![-86, 189, -240], ![39, 624, 0]], ![![-65, 142, -180], ![27, 468, 0]], ![![-73, 160, -203], ![32, 528, 0]]]
  g := ![![![1, 0, 0], ![-10, 13, 0], ![-11, 0, 13]], ![![-1, 1, 0], ![-1, -4, 5], ![29, -30, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![3, -2, 1]] ![![13, 0, 0], ![3, 1, 0]]
  ![![13, 0, 0], ![16, 3, 1]] where
 M := ![![![39, -26, 13], ![60, -31, -6]]]
 hmul := by decide  
 g := ![![![![-13, -5, 0], ![13, 0, 0]], ![![-4, -4, -1], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![16, 3, 1]] ![![13, 0, 0], ![-3, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-39, 13, 0]], ![![208, 39, 13], ![13, -26, 13]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-3, 1, 0]]], ![![![16, 3, 1]], ![![1, -2, 1]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [2, 7, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 12, 11], [0, 4, 6], [0, 1]]
 g := ![![[2], [8, 13], [13, 1], []], ![[2, 15, 2, 10], [6, 1], [15, 16], [1, 2]], ![[0, 9, 3, 7], [12, 13], [3, 8], [6, 2]]]
 h' := ![![[13, 12, 11], [14, 11], [8, 9, 9], [0, 0, 1], [0, 1]], ![[0, 4, 6], [4, 13, 2], [13, 12, 16], [14, 12, 4], [13, 12, 11]], ![[0, 1], [14, 10, 15], [2, 13, 9], [5, 5, 12], [0, 4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 14], []]
 b := ![[], [11, 15, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [2, 7, 4, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-144145975, 781524714, -2051575164]
  a := ![-66, 2, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8479175, 45972042, -120680892]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![24, 3, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![24, 3, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![5, 3, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![24, 3, 1], ![61, -9, 16], ![175, -85, -3]]]
  hmulB := by decide  
  f := ![![![-23, -3, -1], ![19, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -3, 19]], ![![1, 0, 1], ![-1, -3, 16], ![10, -4, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [2, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 18], [0, 1]]
 g := ![![[18, 9], [], [4], [1]], ![[17, 10], [], [4], [1]]]
 h' := ![![[2, 18], [0, 16], [15], [17, 2], [0, 1]], ![[0, 1], [13, 3], [15], [2, 17], [2, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [9, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [2, 17, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4056, 3977, -5185]
  a := ![-5, 4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1151, 1028, -5185]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![3, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![3, 1, 0]] 
 ![![19, 0, 0], ![3, 1, 0], ![3, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![3, 1, 0], ![2, 2, 5], ![55, -30, 4]]]
  hmulB := by decide  
  f := ![![![376, 385, 975], ![95, -3705, 0]], ![![57, 59, 150], ![20, -570, 0]], ![![57, 60, 154], ![30, -585, 0]]]
  g := ![![![1, 0, 0], ![-3, 19, 0], ![-3, 0, 19]], ![![0, 1, 0], ![-1, 2, 5], ![7, -30, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![24, 3, 1]] ![![19, 0, 0], ![3, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![57, 19, 0]], ![![456, 57, 19], ![133, 0, 19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![3, 1, 0]]], ![![![24, 3, 1]], ![![7, 0, 1]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![26, 4, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![26, 4, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![3, 4, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![26, 4, 1], ![63, -8, 21], ![230, -115, 0]]]
  hmulB := by decide  
  f := ![![![-25, -4, -1], ![23, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -4, 23]], ![![1, 0, 1], ![0, -4, 21], ![10, -5, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [1, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 22], [0, 1]]
 g := ![![[3, 1], [20, 12], [2, 9], [1]], ![[0, 22], [7, 11], [21, 14], [1]]]
 h' := ![![[20, 22], [3, 1], [21, 9], [22, 20], [0, 1]], ![[0, 1], [0, 22], [17, 14], [8, 3], [20, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [4, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [1, 3, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![249, 125, -745]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![108, 135, -745]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![2, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![2, 1, 0]] 
 ![![23, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![2, 1, 0], ![2, 1, 5], ![55, -30, 3]]]
  hmulB := by decide  
  f := ![![![-1, -1, 0], ![23, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-2, -1, -3], ![9, 14, 0]]]
  g := ![![![1, 0, 0], ![-2, 23, 0], ![0, 0, 23]], ![![0, 1, 0], ![0, 1, 5], ![5, -30, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![26, 4, 1]] ![![23, 0, 0], ![2, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![46, 23, 0]], ![![598, 92, 23], ![115, 0, 23]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![2, 1, 0]]], ![![![26, 4, 1]], ![![5, 0, 1]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![14, 1, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![14, 1, 0]] 
 ![![29, 0, 0], ![14, 1, 0], ![22, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![14, 1, 0], ![2, 13, 5], ![55, -30, 15]]]
  hmulB := by decide  
  f := ![![![467, 4199, 1620], ![377, -9396, 0]], ![![214, 2021, 780], ![204, -4524, 0]], ![![348, 3185, 1229], ![299, -7128, 0]]]
  g := ![![![1, 0, 0], ![-14, 29, 0], ![-22, 0, 29]], ![![0, 1, 0], ![-10, 13, 5], ![5, -30, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-12, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-12, 1, 0]] 
 ![![29, 0, 0], ![17, 1, 0], ![4, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-12, 1, 0], ![2, -13, 5], ![55, -30, -11]]]
  hmulB := by decide  
  f := ![![![337, -2800, 1080], ![-232, -6264, 0]], ![![205, -1634, 630], ![-115, -3654, 0]], ![![56, -387, 149], ![-9, -864, 0]]]
  g := ![![![1, 0, 0], ![-17, 29, 0], ![-4, 0, 29]], ![![-1, 1, 0], ![7, -13, 5], ![21, -30, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 1, 0]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-2, 1, 0]] 
 ![![29, 0, 0], ![27, 1, 0], ![5, 0, 1]] where
  M :=![![![-2, 1, 0], ![2, -3, 5], ![55, -30, -1]]]
  hmulB := by decide  
  f := ![![![-153, -1, -5]], ![![-152, -1, -5]], ![![-30, 0, -1]]]
  g := ![![![-1, 1, 0], ![2, -3, 5], ![30, -30, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![14, 1, 0]] ![![29, 0, 0], ![-12, 1, 0]]
  ![![-153, -1, -5]] where
 M := ![![![841, 0, 0], ![-348, 29, 0]], ![![406, 29, 0], ![-166, 1, 5]]]
 hmul := by decide  
 g := ![![![![-58, 29, 0]], ![![26, -15, 5]]], ![![![-26, 11, 5]], ![![21, -11, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-153, -1, -5]] ![![-2, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![29, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![15, -2, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![15, -2, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![15, 29, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![15, -2, 1], ![51, -13, -9], ![-100, 65, -17]]]
  hmulB := by decide  
  f := ![![![-14, 2, -1], ![31, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -29, 31]], ![![0, -1, 1], ![6, 8, -9], ![5, 18, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [11, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 30], [0, 1]]
 g := ![![[29, 28], [21, 5], [16, 2], [22, 1]], ![[25, 3], [7, 26], [29, 29], [13, 30]]]
 h' := ![![[22, 30], [17, 11], [10, 25], [6, 8], [0, 1]], ![[0, 1], [11, 20], [2, 6], [27, 23], [22, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [14, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [11, 9, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15045, -7369, 507]
  a := ![3, 18, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![240, -712, 507]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![9, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![9, 1, 0]] 
 ![![31, 0, 0], ![9, 1, 0], ![17, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![9, 1, 0], ![2, 8, 5], ![55, -30, 10]]]
  hmulB := by decide  
  f := ![![![-327, -1452, -910], ![-124, 5642, 0]], ![![-95, -415, -260], ![-30, 1612, 0]], ![![-177, -796, -499], ![-76, 3094, 0]]]
  g := ![![![1, 0, 0], ![-9, 31, 0], ![-17, 0, 31]], ![![0, 1, 0], ![-5, 8, 5], ![5, -30, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![15, -2, 1]] ![![31, 0, 0], ![9, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![279, 31, 0]], ![![465, -62, 31], ![186, -31, 0]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![9, 1, 0]]], ![![![15, -2, 1]], ![![6, -1, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB218I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB218I0 : PrimesBelowBoundCertificateInterval O 1 31 218 where
  m := 11
  g := ![1, 3, 3, 3, 2, 3, 1, 2, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB218I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N1, I5N1]
    · exact ![I7N0, I7N0, I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![8]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![529, 23]
    · exact ![29, 29, 29]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I5N0, I5N1, I7N0, I11N0, I11N1, I13N0, I13N1, I13N2, I19N1, I23N1, I29N0, I29N1, I29N2, I31N1]
  Il := ![[I2N0], [I3N0, I3N0, I3N0], [I5N0, I5N1, I5N1], [I7N0, I7N0, I7N0], [I11N0, I11N1], [I13N0, I13N1, I13N2], [], [I19N1], [I23N1], [I29N0, I29N1, I29N2], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
