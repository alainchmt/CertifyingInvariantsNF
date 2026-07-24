
import IdealArithmetic.Examples.NF5_1_7500000_1.RI5_1_7500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -1, -1, -1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![0, -1, -1, -1, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![0, -1, -1, -1, 0], ![0, -1, 0, -2, -2], ![-8, -8, 1, 4, -4], ![-8, -11, -6, 6, 5], ![6, -1, -8, -9, 4]]]
  hmulB := by decide  
  f := ![![![-51, 4, 5, 0, 7]], ![![14, -9, 2, -2, 0]], ![![0, 16, -7, 4, -4]], ![![-15, -7, 5, -2, 4]], ![![8, 11, -6, 3, -4]]]
  g := ![![![0, -1, -1, -1, 0], ![0, -1, 0, -2, -2], ![-4, -8, 1, 4, -4], ![-4, -11, -6, 6, 5], ![3, -1, -8, -9, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, 0, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-1, -1, 0, 1, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-1, -1, 0, 1, 0], ![0, -1, -2, 0, 2], ![8, 6, -1, -8, 0], ![0, 4, 8, -1, -9], ![-14, -11, 2, 13, -1]]]
  hmulB := by decide  
  f := ![![![12, -5, 0, -1, -1]], ![![-2, 4, -2, 1, -1]], ![![-4, -8, 3, -2, 2]], ![![11, -1, -2, 0, -2]], ![![1, -8, 2, -2, 1]]]
  g := ![![![-1, -1, 0, 1, 0], ![-1, -1, -2, 0, 2], ![8, 6, -1, -8, 0], ![5, 4, 8, -1, -9], ![-13, -11, 2, 13, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, 0, 0, 0]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-1, -1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-1, -1, 0, 0, 0], ![0, -1, -1, 0, 0], ![0, -1, -1, -2, 0], ![0, 0, 1, -1, -2], ![-4, -4, 0, 2, -1]]]
  hmulB := by decide  
  f := ![![![14, 7, -5, 2, -4]], ![![-1, 0, 0, 0, 0]], ![![15, 6, -5, 2, -4]], ![![7, 4, -3, 1, -2]], ![![4, 1, -1, 0, -1]]]
  g := ![![![0, -1, 0, 0, 0], ![1, -1, -1, 0, 0], ![2, -1, -1, -2, 0], ![0, 0, 1, -1, -2], ![-1, -4, 0, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![0, -1, -1, -1, 0]] ![![-1, -1, 0, 1, 0]]
  ![![-8, -9, -5, 9, 7]] where
 M := ![![![-8, -9, -5, 9, 7]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-8, -9, -5, 9, 7]] ![![-1, -1, 0, 1, 0]]
  ![![-130, -54, 109, 114, -106]] where
 M := ![![![-130, -54, 109, 114, -106]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-130, -54, 109, 114, -106]] ![![-1, -1, 0, 0, 0]]
  ![![554, 499, 59, -544, -122]] where
 M := ![![![554, 499, 59, -544, -122]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![554, 499, 59, -544, -122]] ![![-1, -1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-66, -624, -1102, 182, 1210]]]
 hmul := by decide  
 g := ![![![![-33, -312, -551, 91, 605]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -45, -13, -10, -6]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-31, -45, -13, -10, -6]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![1, 0, 1, 1, 0], ![2, 1, 0, 0, 1]] where
  M :=![![![-31, -45, -13, -10, -6], ![-24, -68, -35, -14, -20], ![-80, -139, -54, -30, -28], ![-44, -89, -37, -19, -20], ![-80, -150, -62, -32, -33]]]
  hmulB := by decide  
  f := ![![![3, 3, 1, -2, -2]], ![![-8, -4, 5, 6, -4]], ![![-16, -19, -10, 18, 12]], ![![5, -1, -10, -3, 10]], ![![10, 12, 7, -10, -9]]]
  g := ![![![-3, -13, -1, -10, -6], ![10, -16, -7, -14, -20], ![2, -37, -8, -30, -28], ![5, -23, -6, -19, -20], ![6, -39, -10, -32, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [2, 2, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1, 1], [0, 1, 2], [0, 1]]
 g := ![![[1]], ![[2, 2, 1, 1]], ![[0, 1, 2, 2]]]
 h' := ![![[1, 1, 1], [0, 1]], ![[0, 1, 2], [1, 1, 1]], ![[0, 1], [0, 1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 2], []]
 b := ![[], [1, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [2, 2, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![130646, 133339, 51366, -139854, -77276]
  a := ![0, -2, 2, -3, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![141684, 70205, 63740, -139854, -77276]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 5, 2, 1, 1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 5, 2, 1, 1]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![3, 5, 2, 1, 1], ![4, 9, 4, 2, 2], ![8, 16, 7, 4, 4], ![6, 11, 4, 2, 3], ![10, 19, 8, 3, 4]]]
  hmulB := by decide  
  f := ![![![1, -5, 2, -1, 1]], ![![2, -1, 0, 0, 0]], ![![-2, -6, 3, -2, 2]], ![![2, 1, 0, 0, -1]], ![![-3, -4, 2, 0, 1]]]
  g := ![![![-4, 5, 2, 1, 1], ![-8, 9, 4, 2, 2], ![-14, 16, 7, 4, 4], ![-9, 11, 4, 2, 3], ![-16, 19, 8, 3, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-31, -45, -13, -10, -6]] ![![3, 5, 2, 1, 1]]
  ![![-497, -992, -421, -211, -227]] where
 M := ![![![-497, -992, -421, -211, -227]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-497, -992, -421, -211, -227]] ![![3, 5, 2, 1, 1]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-12363, -24783, -10569, -5268, -5706]]]
 hmul := by decide  
 g := ![![![![-4121, -8261, -3523, -1756, -1902]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45, 99, 42, 21, 23]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![45, 99, 42, 21, 23]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![45, 99, 42, 21, 23], ![92, 179, 78, 38, 42], ![168, 338, 141, 72, 76], ![106, 217, 94, 46, 51], ![186, 371, 156, 79, 84]]]
  hmulB := by decide  
  f := ![![![1, 7, 10, -3, -11]], ![![-8, -1, 10, 6, -10]], ![![-4, -6, -7, 4, 8]], ![![38, 27, -10, -36, 7]], ![![12, 25, 28, -15, -32]]]
  g := ![![![-113, 99, 42, 21, 23], ![-204, 179, 78, 38, 42], ![-380, 338, 141, 72, 76], ![-248, 217, 94, 46, 51], ![-418, 371, 156, 79, 84]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![45, 99, 42, 21, 23]] ![![45, 99, 42, 21, 23]]
  ![![24693, 49462, 21096, 10514, 11388]] where
 M := ![![![24693, 49462, 21096, 10514, 11388]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![24693, 49462, 21096, 10514, 11388]] ![![45, 99, 42, 21, 23]]
  ![![12438469, 24935239, 10634522, 5300317, 5741445]] where
 M := ![![![12438469, 24935239, 10634522, 5300317, 5741445]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![12438469, 24935239, 10634522, 5300317, 5741445]] ![![45, 99, 42, 21, 23]]
  ![![6270115161, 12569529532, 5360727160, 2671821252, 2894186044]] where
 M := ![![![6270115161, 12569529532, 5360727160, 2671821252, 2894186044]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![6270115161, 12569529532, 5360727160, 2671821252, 2894186044]] ![![45, 99, 42, 21, 23]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![3160685718965, 6336141201255, 2702274890370, 1346831371185, 1458922664755]]]
 hmul := by decide  
 g := ![![![![632137143793, 1267228240251, 540454978074, 269366274237, 291784532951]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [1, 2, 6, 6, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 5, 0, 6, 1], [2, 4, 0, 3, 2], [4, 0, 6, 0, 3], [2, 4, 1, 5, 1], [0, 1]]
 g := ![![[1, 0, 1], []], ![[1, 5, 1, 4, 6, 5, 4, 1], [1, 3, 0, 1, 5, 4, 4, 1]], ![[5, 1, 3, 5, 2, 2], [2, 2, 1, 5, 0, 6, 1, 1]], ![[2, 6, 5, 2, 5, 4, 5, 3], [2, 3, 0, 0, 6, 0, 0, 6]], ![[0, 6, 6, 3, 6, 2], [1, 0, 0, 2, 1, 2, 1, 1]]]
 h' := ![![[6, 5, 0, 6, 1], [0, 0, 0, 1], [0, 1]], ![[2, 4, 0, 3, 2], [5, 3, 4, 6, 1], [6, 5, 0, 6, 1]], ![[4, 0, 6, 0, 3], [6, 0, 2, 6], [2, 4, 0, 3, 2]], ![[2, 4, 1, 5, 1], [6, 0, 4, 5, 6], [4, 0, 6, 0, 3]], ![[0, 1], [0, 4, 4, 3], [2, 4, 1, 5, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 3, 4, 6], [], [], []]
 b := ![[], [3, 2, 0, 4, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [1, 2, 6, 6, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3657890762918, 1037938710473, -3868060368389, -3272330305580, 3710737696099]
  a := ![3, -65, -1, -66, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![522555823274, 148276958639, -552580052627, -467475757940, 530105385157]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 16807 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, -172, -34, -38, -20]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-35, -172, -34, -38, -20]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![10, 7, 2, 1, 0], ![2, 3, 10, 0, 1]] where
  M :=![![![-35, -172, -34, -38, -20], ![-80, -149, -134, -28, -76], ![-304, -518, -121, -116, -56], ![-72, -250, -134, -51, -78], ![-308, -518, -160, -114, -79]]]
  hmulB := by decide  
  f := ![![![-41, -44, -18, 42, 24]], ![![96, 37, -86, -84, 84]], ![![336, 346, 121, -340, -168]], ![![50, 35, -14, -47, 10]], ![![270, 263, 68, -270, -103]]]
  g := ![![![35, 14, 22, -38, -20], ![32, 25, 62, -28, -76], ![88, 42, 61, -116, -56], ![54, 31, 68, -51, -78], ![90, 47, 78, -114, -79]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [9, 6, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 5, 9], [6, 5, 2], [0, 1]]
 g := ![![[3, 0, 4], [6, 1, 1], []], ![[9, 1, 9, 9], [3, 6, 7, 5], [6, 4]], ![[10, 1, 0, 7], [6, 6, 8, 6], [2, 4]]]
 h' := ![![[6, 5, 9], [1, 10, 2], [0, 0, 1], [0, 1]], ![[6, 5, 2], [3, 4, 1], [4, 10, 5], [6, 5, 9]], ![[0, 1], [9, 8, 8], [7, 1, 5], [6, 5, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], []]
 b := ![[], [6, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [9, 6, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19700, 6365, -17477, -19832, 14861]
  a := ![1, -4, 1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![17118, 9146, -11493, -19832, 14861]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -44, -18, 42, 24]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-41, -44, -18, 42, 24]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![8, 7, 1, 0, 0], ![5, 2, 0, 1, 0], ![7, 10, 0, 0, 1]] where
  M :=![![![-41, -44, -18, 42, 24], ![96, 37, -86, -84, 84], ![336, 346, 121, -340, -168], ![-384, -126, 386, 331, -382], ![-596, -590, -168, 598, 247]]]
  hmulB := by decide  
  f := ![![![-35, -172, -34, -38, -20]], ![![-80, -149, -134, -28, -76]], ![![-104, -267, -121, -56, -68]], ![![-37, -128, -52, -27, -30]], ![![-123, -292, -158, -60, -89]]]
  g := ![![![-25, -22, -18, 42, 24], ![56, -3, -86, -84, 84], ![204, 169, 121, -340, -168], ![-223, 30, 386, 331, -382], ![-361, -280, -168, 598, 247]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [1, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 10], [0, 1]]
 g := ![![[10, 1], [10, 1], [1]], ![[0, 10], [0, 10], [1]]]
 h' := ![![[1, 10], [1, 10], [10, 1], [0, 1]], ![[0, 1], [0, 1], [0, 10], [1, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [7, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [1, 10, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3352, -1322, 1092, 4864, 1226]
  a := ![1, 18, -3, 17, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4090, -2814, 1092, 4864, 1226]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-35, -172, -34, -38, -20]] ![![-41, -44, -18, 42, 24]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 0, -1, 3, -1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![1, 0, -1, 3, -1]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![3, 7, 6, 1, 0], ![8, 8, 6, 0, 1]] where
  M :=![![![1, 0, -1, 3, -1], ![-4, -4, -3, 0, 6], ![24, 17, -4, -18, 0], ![2, 12, 19, -4, -21], ![-30, -23, 6, 31, -4]]]
  hmulB := by decide  
  f := ![![![-11, -2, 7, -1, 5]], ![![20, 16, -1, 4, -2]], ![![-8, 11, 12, 2, 8]], ![![5, 14, 7, 3, 4]], ![![2, 15, 10, 3, 6]]]
  g := ![![![0, -1, -1, 3, -1], ![-4, -4, -3, 0, 6], ![6, 11, 8, -18, 0], ![14, 16, 13, -4, -21], ![-7, -16, -12, 31, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [2, 4, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 1, 9], [6, 11, 4], [0, 1]]
 g := ![![[9, 7, 1], [6, 1], [1]], ![[1, 2, 1, 9], [1, 1], [2, 1, 10, 1]], ![[4, 10], [1, 4], [12, 9, 7, 12]]]
 h' := ![![[8, 1, 9], [5, 3, 1], [11, 9, 1], [0, 1]], ![[6, 11, 4], [12, 7, 12], [1, 0, 1], [8, 1, 9]], ![[0, 1], [7, 3], [10, 4, 11], [6, 11, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 12], []]
 b := ![[], [5, 10, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [2, 4, 12, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-430547, 157314, 1021545, 297190, -1080411]
  a := ![-1, 2, 5, 4, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![563167, 516944, 440067, 297190, -1080411]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -7, -2, 7, 3]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-7, -7, -2, 7, 3]] 
 ![![13, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-7, -7, -2, 7, 3], ![12, 3, -14, -10, 14], ![56, 54, 13, -56, -20], ![-46, -7, 62, 38, -63], ![-98, -91, -16, 97, 28]]]
  hmulB := by decide  
  f := ![![![245, 77, -42, 23, -43]], ![![81, 32, -12, 9, -13]], ![![33, 11, -1, 3, -3]], ![![158, 55, -26, 16, -27]], ![![6, 5, 4, 1, 2]]]
  g := ![![![-2, -7, -2, 7, 3], ![7, 3, -14, -10, 14], ![17, 54, 13, -56, -20], ![-29, -7, 62, 38, -63], ![-31, -91, -16, 97, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59, -17, 63, -8, 42]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-59, -17, 63, -8, 42]] 
 ![![13, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-59, -17, 63, -8, 42], ![168, 172, -9, 42, -16], ![-64, 95, 130, 14, 84], ![84, 115, 45, 25, 22], ![12, 156, 110, 30, 67]]]
  hmulB := by decide  
  f := ![![![-103, 9, 187, 80, -194]], ![![-131, -47, 124, 114, -122]], ![![-30, -9, 32, 26, -32]], ![![193, 236, 142, -203, -176]], ![![-138, 54, 332, 98, -349]]]
  g := ![![![-68, -17, 63, -8, 42], ![-116, 172, -9, 42, -16], ![-245, 95, 130, 14, 84], ![-142, 115, 45, 25, 22], ![-264, 156, 110, 30, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![1, 0, -1, 3, -1]] ![![-7, -7, -2, 7, 3]]
  ![![-103, 9, 187, 80, -194]] where
 M := ![![![-103, 9, 187, 80, -194]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-103, 9, 187, 80, -194]] ![![-59, -17, 63, -8, 42]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [3, 3, 10, 2, 3, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 7, 10, 2, 1], [13, 9, 14, 12], [16, 16, 14, 10, 5], [11, 1, 13, 10, 11], [0, 1]]
 g := ![![[3, 11, 1, 8, 9], [9, 7, 14, 1], [], []], ![[14, 0, 8, 2, 14, 16, 12, 4], [11, 11, 0, 1], [3, 15, 12, 4], [2, 2, 1, 1]], ![[11, 15, 12, 1, 16, 15, 5], [11, 6, 11, 4], [5, 1, 5, 16], [6, 8]], ![[16, 12, 11, 1, 14, 7, 4, 12], [4, 14, 7, 1], [12, 1, 14, 8], [16, 13, 8, 8]], ![[9, 16, 8, 4, 0, 7, 7, 11], [8, 15, 7, 1], [12, 11, 6, 2], [2, 12, 10, 2]]]
 h' := ![![[8, 7, 10, 2, 1], [7, 3, 0, 3, 3], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[13, 9, 14, 12], [3, 4, 7, 13, 15], [6, 3, 16, 10, 1], [7, 15, 10, 6, 2], [8, 7, 10, 2, 1]], ![[16, 16, 14, 10, 5], [3, 3, 14, 4, 4], [6, 13, 9, 7, 15], [15, 5, 4, 13, 4], [13, 9, 14, 12]], ![[11, 1, 13, 10, 11], [14, 10, 9, 3, 13], [14, 12, 11, 12, 16], [4, 0, 5, 14, 5], [16, 16, 14, 10, 5]], ![[0, 1], [2, 14, 4, 11, 16], [14, 6, 15, 5, 1], [13, 14, 14, 1, 6], [11, 1, 13, 10, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 12, 10, 14], [], [], []]
 b := ![[], [1, 2, 16, 10, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [3, 3, 10, 2, 3, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-73220663229, -52796988638, 17642339594, 69255206356, -11573326810]
  a := ![0, -10, -2, -20, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4307097837, -3105705214, 1037784682, 4073835668, -680783930]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 1419857 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [16, 11, 11, 17, 7, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 9, 6, 18, 17], [15, 0, 18, 18, 11], [5, 15, 5, 6, 6], [4, 13, 9, 15, 4], [0, 1]]
 g := ![![[15, 18, 10, 7, 7], [11, 17, 13, 12, 1], [], []], ![[9, 2, 1, 10, 1, 7, 17, 6], [11, 14, 7, 0, 15, 9], [8, 13, 15, 17], [5, 1, 14, 4]], ![[7, 14, 14, 18, 3, 1, 8, 6], [6, 3, 8, 12, 14, 5, 6, 16], [12, 14, 2, 17], [1, 15, 5, 7]], ![[1, 0, 11, 15, 2, 10, 0, 11], [2, 6, 16, 18, 2, 17, 0, 16], [0, 17, 9, 5], [14, 3, 10, 17]], ![[7, 8, 16, 17, 9, 18, 13, 7], [8, 18, 15, 12, 9, 16, 2, 9], [7, 7, 0, 5], [13, 7, 8, 16]]]
 h' := ![![[7, 9, 6, 18, 17], [14, 6, 16, 13, 8], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[15, 0, 18, 18, 11], [1, 6, 8, 6, 4], [16, 18, 6, 10], [7, 17, 8, 8, 6], [7, 9, 6, 18, 17]], ![[5, 15, 5, 6, 6], [2, 4, 5, 9, 2], [17, 5, 2, 2, 13], [0, 15, 18, 1, 13], [15, 0, 18, 18, 11]], ![[4, 13, 9, 15, 4], [17, 17, 2, 8, 9], [5, 18, 2, 10, 16], [10, 5, 4, 13, 9], [5, 15, 5, 6, 6]], ![[0, 1], [16, 5, 7, 2, 15], [6, 16, 9, 16, 8], [17, 1, 7, 16, 10], [4, 13, 9, 15, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 1, 8, 4], [], [], []]
 b := ![[], [8, 5, 3, 17, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [16, 11, 11, 17, 7, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6620994087, 14288112936, 16910962730, -8299465981, -19216422597]
  a := ![13, 0, 4, 1, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![348473373, 752005944, 890050670, -436813999, -1011390663]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![247, 385, -201, 102, -134]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![247, 385, -201, 102, -134]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![10, 10, 13, 14, 1]] where
  M :=![![![247, 385, -201, 102, -134], ![-536, -490, 283, -134, 204], ![816, 563, -356, 158, -268], ![-268, -61, 61, -21, 56], ![520, 290, -198, 84, -155]]]
  hmulB := by decide  
  f := ![![![1, 1, 1, -2, -2]], ![![-8, -6, 3, 6, -4]], ![![-16, -21, -12, 14, 12]], ![![28, 13, -19, -27, 16]], ![![6, -5, -16, -8, 13]]]
  g := ![![![69, 75, 67, 86, -134], ![-112, -110, -103, -130, 204], ![152, 141, 136, 170, -268], ![-36, -27, -29, -35, 56], ![90, 80, 79, 98, -155]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [2, 18, 0, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 4, 11, 1], [22, 0, 14, 14], [17, 18, 21, 8], [0, 1]]
 g := ![![[20, 5, 15, 12], [6, 2, 9, 1], [22, 1], []], ![[2, 14, 15, 9, 19, 16], [11, 5, 6, 22, 6, 4], [15, 10, 21, 14, 10, 9], [16, 21, 1]], ![[14, 21, 5, 20, 13, 19], [10, 16, 1, 0, 13, 19], [2, 17, 5, 0, 15, 7], [0, 12, 12]], ![[15, 12, 1, 7, 2, 2], [11, 11, 22, 0, 5, 12], [1, 20, 11, 3, 13, 12], [20, 19, 18]]]
 h' := ![![[6, 4, 11, 1], [11, 7, 10, 14], [2, 16, 5, 1], [0, 0, 1], [0, 1]], ![[22, 0, 14, 14], [9, 1, 14, 4], [20, 15, 20, 21], [4, 17, 21, 20], [6, 4, 11, 1]], ![[17, 18, 21, 8], [1, 5, 20, 16], [18, 1, 3, 7], [1, 22, 8, 9], [22, 0, 14, 14]], ![[0, 1], [15, 10, 2, 12], [17, 14, 18, 17], [19, 7, 16, 17], [17, 18, 21, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 0, 22], []]
 b := ![[], [], [21, 16, 0, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [2, 18, 0, 1, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3232816, 3171038, 853249, -3238071, -1276143]
  a := ![-1, -4, -1, -5, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![695402, 692716, 758396, 635997, -1276143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, -1, 2, 2]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-1, -1, -1, 2, 2]] 
 ![![23, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-1, -1, -1, 2, 2], ![8, 6, -3, -6, 4], ![16, 21, 12, -14, -12], ![-28, -13, 19, 27, -16], ![-24, -26, -14, 28, 21]]]
  hmulB := by decide  
  f := ![![![-247, -385, 201, -102, 134]], ![![-170, -280, 145, -74, 96]], ![![-261, -376, 199, -100, 134]], ![![-85, -148, 76, -39, 50]], ![![-130, -180, 96, -48, 65]]]
  g := ![![![0, -1, -1, 2, 2], ![-1, 6, -3, -6, 4], ![-16, 21, 12, -14, -12], ![-12, -13, 19, 27, -16], ![12, -26, -14, 28, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![247, 385, -201, 102, -134]] ![![-1, -1, -1, 2, 2]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB171I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB171I0 : PrimesBelowBoundCertificateInterval O 1 23 171 where
  m := 9
  g := ![5, 3, 5, 1, 2, 3, 1, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB171I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![27, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![16807]
    · exact ![1331, 121]
    · exact ![2197, 13, 13]
    · exact ![1419857]
    · exact ![2476099]
    · exact ![279841, 23]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
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
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I11N1, I13N1, I13N2, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N1], [I13N1, I13N2], [], [], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
