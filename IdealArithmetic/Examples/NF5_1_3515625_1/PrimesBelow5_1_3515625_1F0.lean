
import IdealArithmetic.Examples.NF5_1_3515625_1.RI5_1_3515625_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![88, -9, 38, -14, 111]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![88, -9, 38, -14, 111]] 
 ![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![1, 1, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 1, 0, 0, 1]] where
  M :=![![![88, -9, 38, -14, 111], ![110, -9, 47, -17, 136], ![136, -9, 59, -21, 170], ![172, -13, 75, -27, 218], ![39, -2, 17, -6, 49]]]
  hmulB := by decide  
  f := ![![![-2, 2, -1, 1, -2]], ![![4, -1, -2, -3, 14]], ![![3, -3, 4, -3, 1]], ![![-27, 10, 4, 19, -65]], ![![-1, 1, -2, 1, 2]]]
  g := ![![![32, -79, 38, -14, 111], ![40, -96, 47, -17, 136], ![49, -119, 59, -21, 170], ![62, -153, 75, -27, 218], ![14, -34, 17, -6, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![838103, -345487, -2269, -606492, 1793726]
  a := ![-239, -1, 122, 120, -658]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![723432, -1068472, -2269, -606492, 1793726]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 1, 0, 2]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 1, 0, 2]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 2]] where
  M :=![![![2, 0, 1, 0, 2], ![4, 0, 0, -1, 8], ![8, -3, 4, -4, 10], ![-12, 2, 13, 10, -48], ![-2, 1, 1, 2, -6]]]
  hmulB := by decide  
  f := ![![![2, 8, -5, 3, -21]], ![![-9, 10, -2, 2, -9]], ![![-2, -2, 2, -1, 8]], ![![8, -9, 2, -2, 10]], ![![1, -6, 3, -2, 13]]]
  g := ![![![1, 0, 1, 0, 1], ![2, 0, 0, -1, 4], ![4, -3, 4, -4, 5], ![-6, 2, 13, 10, -24], ![-1, 1, 1, 2, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P1 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N1 : CertifiedPrimeIdeal' SI2N1 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4284, -1525, -599, -3019, 10144]
  a := ![-17, 1, 9, 8, -47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2142, -1525, -599, -3019, 5072]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![152, -24, 62, -24, 183]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![152, -24, 62, -24, 183]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![152, -24, 62, -24, 183], ![174, -7, 72, -25, 204], ![208, -5, 93, -32, 266], ![276, -26, 123, -45, 360], ![57, 1, 27, -9, 77]]]
  hmulB := by decide  
  f := ![![![18, -7, -1, -13, 40]], ![![-3, -8, 22, -1, -43]], ![![-73, 42, -27, 57, -111]], ![![255, -18, -209, -156, 893]], ![![51, -15, -15, -35, 134]]]
  g := ![![![69, -24, 62, -24, 183], ![67, -7, 72, -25, 204], ![76, -5, 93, -32, 266], ![112, -26, 123, -45, 360], ![19, 1, 27, -9, 77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![88, -9, 38, -14, 111]] ![![2, 0, 1, 0, 2]]
  ![![390, -31, 169, -61, 490]] where
 M := ![![![390, -31, 169, -61, 490]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![390, -31, 169, -61, 490]] ![![152, -24, 62, -24, 183]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![100132, -7912, 43392, -15658, 125770]]]
 hmul := by decide  
 g := ![![![![50066, -3956, 21696, -7829, 62885]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 10, -2, 2, -9]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-9, 10, -2, 2, -9]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-9, 10, -2, 2, -9], ![-2, -2, 2, -1, 8], ![8, -9, 2, -2, 10], ![4, 0, -1, 0, -4], ![5, -5, 1, -1, 4]]]
  hmulB := by decide  
  f := ![![![6, -1, 3, -1, 7]], ![![2, 0, 1, 0, 2]], ![![4, 0, 0, -1, 8]], ![![8, -3, 4, -4, 10]], ![![5, -1, 3, -1, 5]]]
  g := ![![![3, 10, -2, 2, -9], ![-6, -2, 2, -1, 8], ![-4, -9, 2, -2, 10], ![4, 0, -1, 0, -4], ![-1, -5, 1, -1, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 2, 1, 0, 1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![6, 2, 1, 0, 1]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![6, 2, 1, 0, 1], ![2, 5, 2, 0, 4], ![8, -2, 5, -2, 16], ![16, -6, 6, -3, 20], ![3, -2, 2, -1, 7]]]
  hmulB := by decide  
  f := ![![![-1, 0, 1, 1, -5]], ![![-1, 1, -1, 1, -1]], ![![6, -2, -1, -4, 14]], ![![-3, -6, 17, 0, -35]], ![![-3, 0, 3, 2, -12]]]
  g := ![![![0, 2, 1, 0, 1], ![-5, 5, 2, 0, 4], ![-10, -2, 5, -2, 16], ![-9, -6, 6, -3, 20], ![-4, -2, 2, -1, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, -4, 22, -8, 64]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![51, -4, 22, -8, 64]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![51, -4, 22, -8, 64], ![64, -5, 28, -10, 80], ![80, -6, 35, -12, 100], ![104, -8, 42, -17, 136], ![24, -2, 10, -4, 31]]]
  hmulB := by decide  
  f := ![![![17, -8, -2, 0, -8]], ![![6, 3, -4, 2, -16]], ![![6, -2, -1, 0, -4]], ![![14, -12, 2, -1, 0]], ![![3, -2, 0, 0, -1]]]
  g := ![![![-11, -4, 22, -8, 64], ![-14, -5, 28, -10, 80], ![-18, -6, 35, -12, 100], ![-22, -8, 42, -17, 136], ![-5, -2, 10, -4, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-9, 10, -2, 2, -9]] ![![6, 2, 1, 0, 1]]
  ![![-45, 42, -5, 7, -24]] where
 M := ![![![-45, 42, -5, 7, -24]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-45, 42, -5, 7, -24]] ![![6, 2, 1, 0, 1]]
  ![![-186, 136, 8, 13, 15]] where
 M := ![![![-186, 136, 8, 13, 15]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-186, 136, 8, 13, 15]] ![![51, -4, 22, -8, 64]]
  ![![1570, -118, 692, -249, 2009]] where
 M := ![![![1570, -118, 692, -249, 2009]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![1570, -118, 692, -249, 2009]] ![![51, -4, 22, -8, 64]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![150198, -11868, 65088, -23487, 188655]]]
 hmul := by decide  
 g := ![![![![50066, -3956, 21696, -7829, 62885]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N2, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N2
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 2, 0, 0, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-3, 2, 0, 0, 1]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-3, 2, 0, 0, 1], ![2, -4, 2, -1, 4], ![0, -1, 0, 2, -6], ![4, 4, -9, -2, 20], ![3, -1, -1, -1, 4]]]
  hmulB := by decide  
  f := ![![![-174, 13, -75, 27, -217]], ![![-148, 11, -64, 23, -185]], ![![-90, 7, -39, 14, -113]], ![![-140, 11, -60, 22, -176]], ![![-51, 4, -22, 8, -64]]]
  g := ![![![-2, 2, 0, 0, 1], ![2, -4, 2, -1, 4], ![1, -1, 0, 2, -6], ![-3, 4, -9, -2, 20], ![1, -1, -1, -1, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-3, 2, 0, 0, 1]] ![![-3, 2, 0, 0, 1]]
  ![![16, -15, 3, -3, 9]] where
 M := ![![![16, -15, 3, -3, 9]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![16, -15, 3, -3, 9]] ![![-3, 2, 0, 0, 1]]
  ![![-63, 68, -12, 18, -86]] where
 M := ![![![-63, 68, -12, 18, -86]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-63, 68, -12, 18, -86]] ![![-3, 2, 0, 0, 1]]
  ![![139, -228, 60, -42, 297]] where
 M := ![![![139, -228, 60, -42, 297]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![139, -228, 60, -42, 297]] ![![-3, 2, 0, 0, 1]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-150, 665, -375, 135, -785]]]
 hmul := by decide  
 g := ![![![![-30, 133, -75, 27, -157]]]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [6, 2, 1, 5, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 2, 5, 3, 3], [1, 1, 5, 2], [3, 4, 6, 4, 3], [2, 6, 5, 5, 1], [0, 1]]
 g := ![![[4, 3, 1], []], ![[1, 3, 1, 6, 6, 5, 1, 3], [6, 1, 4, 1, 4, 0, 1, 6]], ![[6, 0, 2, 1, 6, 5, 4], [4, 2, 3, 0, 1]], ![[6, 2, 5, 0, 5, 3, 0, 3], [2, 3, 6, 3, 5, 3, 0, 6]], ![[5, 5, 6, 1, 5, 0, 3, 2], [0, 5, 1, 0, 3, 6, 4, 1]]]
 h' := ![![[4, 2, 5, 3, 3], [0, 0, 0, 1], [0, 1]], ![[1, 1, 5, 2], [0, 1, 4, 4, 1], [4, 2, 5, 3, 3]], ![[3, 4, 6, 4, 3], [5, 4, 6, 2, 4], [1, 1, 5, 2]], ![[2, 6, 5, 5, 1], [1, 2, 3, 1, 6], [3, 4, 6, 4, 3]], ![[0, 1], [1, 0, 1, 6, 3], [2, 6, 5, 5, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 2, 4], [], [], []]
 b := ![[], [0, 1, 0, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [6, 2, 1, 5, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-557107243000259, 154260376859729, 185759818484695, 379364997923989, -1500043526678662]
  a := ![103, -3, -50, -52, 283]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-79586749000037, 22037196694247, 26537116926385, 54194999703427, -214291932382666]
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


def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 1, -8, 3, -24]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-19, 1, -8, 3, -24]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![3, 0, 1, 0, 0], ![0, 3, 0, 1, 0], ![3, 4, 0, 0, 1]] where
  M :=![![![-19, 1, -8, 3, -24], ![-24, 2, -11, 4, -30], ![-28, 2, -14, 3, -32], ![-40, 1, -10, 6, -62], ![-10, 1, -3, 2, -15]]]
  hmulB := by decide  
  f := ![![![-25, 26, -5, 5, -22]], ![![-4, -8, 6, -3, 22]], ![![-5, 5, -1, 1, -4]], ![![0, -2, 1, -1, 6]], ![![-7, 3, 1, 0, 3]]]
  g := ![![![7, 8, -8, 3, -24], ![9, 10, -11, 4, -30], ![10, 11, -14, 3, -32], ![16, 21, -10, 6, -62], ![4, 5, -3, 2, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [1, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 10], [0, 1]]
 g := ![![[5, 1], [6, 3], [1]], ![[0, 10], [2, 8], [1]]]
 h' := ![![[6, 10], [5, 1], [10, 6], [0, 1]], ![[0, 1], [0, 10], [2, 5], [6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [5, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [1, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26023, -11873, 2365, -19272, 51666]
  a := ![-43, 5, 22, 23, -118]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12370, -14611, 2365, -19272, 51666]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-211, 18, -91, 33, -264]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-211, 18, -91, 33, -264]] 
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 11]] where
  M :=![![![-211, 18, -91, 33, -264], ![-264, 20, -114, 41, -330], ![-332, 25, -144, 52, -418], ![-420, 34, -183, 66, -528], ![-96, 7, -42, 15, -121]]]
  hmulB := by decide  
  f := ![![![3, -7, 2, -1, 10]], ![![3, -5, 1, -1, 8]], ![![2, -4, 2, -1, 4]], ![![-6, 1, 2, 4, -14]], ![![-12, 9, -3, 8, -23]]]
  g := ![![![13, 18, -91, 33, -24], ![18, 20, -114, 41, -30], ![23, 25, -144, 52, -38], ![28, 34, -183, 66, -48], ![7, 7, -42, 15, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [8, 8, 1] where
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
 g := ![![[1, 3], [1, 9], [1]], ![[10, 8], [6, 2], [1]]]
 h' := ![![[3, 10], [3, 6], [3, 3], [0, 1]], ![[0, 1], [10, 5], [1, 8], [3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [8, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [8, 8, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1968, 329, 2019, 1581, -7667]
  a := ![3, 4, 6, 6, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1777, 329, 2019, 1581, -697]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28, 0, 20, -7, 61]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![28, 0, 20, -7, 61]] 
 ![![11, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![28, 0, 20, -7, 61], ![66, -26, 28, -13, 90], ![76, -11, 26, -10, 74], ![68, 12, 29, -8, 76], ![23, -1, 6, -2, 15]]]
  hmulB := by decide  
  f := ![![![31, -5, -19, -20, 99]], ![![26, -8, -7, -18, 68]], ![![-30, 10, 6, 21, -74]], ![![30, 29, -98, -8, 228]], ![![26, -2, -21, -16, 91]]]
  g := ![![![-25, 0, 20, -7, 61], ![-14, -26, 28, -13, 90], ![-18, -11, 26, -10, 74], ![-38, 12, 29, -8, 76], ![-4, -1, 6, -2, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-19, 1, -8, 3, -24]] ![![-211, 18, -91, 33, -264]]
  ![![7445, -588, 3226, -1164, 9350]] where
 M := ![![![7445, -588, 3226, -1164, 9350]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![7445, -588, 3226, -1164, 9350]] ![![28, 0, 20, -7, 61]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![550726, -43516, 238656, -86119, 691735]]]
 hmul := by decide  
 g := ![![![![50066, -3956, 21696, -7829, 62885]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [9, 6, 12, 10, 7, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 0, 9, 2, 7], [4, 0, 10, 2, 2], [1, 10, 6, 3, 10], [3, 2, 1, 6, 7], [0, 1]]
 g := ![![[6, 8, 10], [6, 1], []], ![[3, 5, 9, 9, 1, 5, 4, 6], [5, 12, 3, 3], [8, 4, 12, 9, 6, 12, 12, 5]], ![[10, 11, 8, 0, 1, 5, 2, 11], [0, 3, 4, 1], [10, 9, 3, 10, 3, 2, 7, 8]], ![[5, 0, 6, 0, 11, 8, 1, 9], [0, 5, 12, 3], [4, 8, 1, 3, 11, 8, 10, 12]], ![[12, 3, 2, 9, 1, 11, 6, 11], [4, 9, 1, 1], [9, 11, 3, 3, 9, 7, 2, 5]]]
 h' := ![![[11, 0, 9, 2, 7], [11, 7, 0, 6], [0, 0, 0, 1], [0, 1]], ![[4, 0, 10, 2, 2], [11, 3, 6, 6, 8], [11, 7, 10, 3, 4], [11, 0, 9, 2, 7]], ![[1, 10, 6, 3, 10], [0, 12, 2, 7, 8], [0, 2, 6, 1, 12], [4, 0, 10, 2, 2]], ![[3, 2, 1, 6, 7], [3, 12, 7, 6, 7], [4, 12, 5, 4, 9], [1, 10, 6, 3, 10]], ![[0, 1], [7, 5, 11, 1, 3], [11, 5, 5, 4, 1], [3, 2, 1, 6, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 6, 1, 12], [], [], []]
 b := ![[], [12, 12, 7, 4, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [9, 6, 12, 10, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-923088374, 485474782, -234234078, 705603821, -1582324042]
  a := ![-7, -1, 4, 2, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-71006798, 37344214, -18018006, 54277217, -121717234]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 371293 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, -2, -2, 10]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![3, 0, -2, -2, 10]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![16, 13, 1, 0, 0], ![13, 0, 0, 1, 0], ![1, 6, 0, 0, 1]] where
  M :=![![![3, 0, -2, -2, 10], ![4, -5, 8, -4, -4], ![-40, 12, 11, 28, -104], ![16, 36, -100, 3, 200], ![14, 0, -14, -8, 53]]]
  hmulB := by decide  
  f := ![![![55, -48, 22, -14, 82]], ![![52, -13, 8, -4, 20]], ![![92, -53, 27, -16, 92]], ![![43, -36, 18, -11, 66]], ![![21, -6, 4, -2, 11]]]
  g := ![![![3, -2, -2, -2, 10], ![-4, -5, 8, -4, -4], ![-28, 29, 11, 28, -104], ![81, 8, -100, 3, 200], ![17, -8, -14, -8, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [5, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16], [0, 1]]
 g := ![![[16, 1], [15], [8], [1]], ![[4, 16], [15], [8], [1]]]
 h' := ![![[5, 16], [14, 1], [2, 7], [12, 5], [0, 1]], ![[0, 1], [2, 16], [3, 10], [3, 12], [5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [1, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [5, 12, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-814, -10, 1022, 533, -3372]
  a := ![9, 0, 4, -7, 24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1219, 408, 1022, 533, -3372]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, 57, -13, 12, -57]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-49, 57, -13, 12, -57]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![6, 2, 1, 0, 0], ![5, 2, 0, 1, 0], ![8, 10, 0, 0, 1]] where
  M :=![![![-49, 57, -13, 12, -57], ![-18, -4, 9, -4, 36], ![40, -50, 12, -11, 56], ![24, -5, -6, 0, -18], ![27, -29, 6, -6, 26]]]
  hmulB := by decide  
  f := ![![![-108, 8, -46, 17, -137]], ![![-138, 12, -60, 23, -174]], ![![-64, 5, -28, 10, -80]], ![![-60, 4, -25, 9, -77]], ![![-135, 11, -58, 22, -171]]]
  g := ![![![25, 37, -13, 12, -57], ![-20, -22, 9, -4, 36], ![-25, -36, 12, -11, 56], ![12, 11, -6, 0, -18], ![-11, -17, 6, -6, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [5, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 16], [0, 1]]
 g := ![![[13, 2], [9], [9], [1]], ![[2, 15], [9], [9], [1]]]
 h' := ![![[3, 16], [15, 11], [14, 14], [12, 3], [0, 1]], ![[0, 1], [14, 6], [5, 3], [4, 14], [3, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [9, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [5, 14, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14275, -5933, 80, -10313, 30219]
  a := ![31, -3, -16, -16, 85]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10376, -16921, 80, -10313, 30219]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-250, 20, -108, 39, -313]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-250, 20, -108, 39, -313]] 
 ![![17, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-250, 20, -108, 39, -313], ![-314, 24, -136, 49, -394], ![-396, 31, -172, 62, -498], ![-500, 40, -217, 78, -628], ![-115, 9, -50, 18, -145]]]
  hmulB := by decide  
  f := ![![![-5, -9, 9, -2, 13]], ![![0, -2, 1, 0, 2]], ![![-1, -7, 5, -3, 17]], ![![0, -7, 10, -4, 2]], ![![-1, -1, 2, 0, -2]]]
  g := ![![![84, 20, -108, 39, -313], ![106, 24, -136, 49, -394], ![134, 31, -172, 62, -498], ![169, 40, -217, 78, -628], ![39, 9, -50, 18, -145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![3, 0, -2, -2, 10]] ![![-49, 57, -13, 12, -57]]
  ![![-5, -9, 9, -2, 13]] where
 M := ![![![-5, -9, 9, -2, 13]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-5, -9, 9, -2, 13]] ![![-250, 20, -108, 39, -313]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
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


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [14, 3, 0, 3, 16, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 10, 1, 0, 13], [14, 10, 6, 17, 10], [2, 8, 5, 4, 4], [3, 9, 7, 17, 11], [0, 1]]
 g := ![![[12, 4, 13, 8, 17], [6, 9, 6, 3, 1], [], []], ![[16, 11, 16, 1, 6, 6, 6, 2], [10, 12, 4, 16, 2, 14, 10, 12], [4, 1, 18, 16], [16, 14, 13, 17]], ![[13, 6, 15, 7, 12, 8, 17, 2], [2, 11, 7, 9, 13, 5, 8, 12], [1, 16, 4, 4], [11, 15, 13, 5]], ![[16, 1, 15, 2, 17, 12, 1, 1], [17, 9, 18, 1, 18, 3, 15, 16], [9, 3, 12, 9], [0, 1, 4, 16]], ![[0, 4, 0, 5, 14, 1, 11, 7], [1, 12, 15, 13, 0, 1, 9, 4], [6, 15, 4, 6], [6, 11, 15, 7]]]
 h' := ![![[3, 10, 1, 0, 13], [11, 8, 3, 17, 6], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[14, 10, 6, 17, 10], [15, 1, 15, 0, 14], [18, 16, 0, 16, 13], [13, 6, 15, 18, 15], [3, 10, 1, 0, 13]], ![[2, 8, 5, 4, 4], [9, 1, 17, 0, 2], [2, 12, 16, 2, 10], [4, 18, 3, 17, 2], [14, 10, 6, 17, 10]], ![[3, 9, 7, 17, 11], [3, 11, 9, 15, 9], [4, 18, 5, 9, 17], [4, 18, 6, 12, 16], [2, 8, 5, 4, 4]], ![[0, 1], [0, 17, 13, 6, 7], [12, 11, 17, 11, 16], [1, 15, 13, 10, 5], [3, 9, 7, 17, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 12, 12, 7], [], [], []]
 b := ![[], [9, 3, 15, 8, 17], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [14, 3, 0, 3, 16, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10968000382, -3551189756, -2444168702, -7640809416, 27510822532]
  a := ![12, 0, -5, -3, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![577263178, -186904724, -128640458, -402147864, 1447938028]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -2, 0, 0, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![1, -2, 0, 0, 1]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![7, 5, 1, 0, 0], ![11, 5, 0, 1, 0], ![1, 21, 0, 0, 1]] where
  M :=![![![1, -2, 0, 0, 1], ![2, 0, -2, -1, 4], ![0, -1, 4, -2, -6], ![-28, 8, 7, 18, -68], ![-5, 3, -1, 3, -8]]]
  hmulB := by decide  
  f := ![![![-22, 15, -9, 5, -31]], ![![-22, 4, -5, 2, -14]], ![![-12, 5, -4, 2, -13]], ![![-16, 8, -6, 3, -19]], ![![-21, 4, -5, 2, -14]]]
  g := ![![![0, -1, 0, 0, 1], ![1, -3, -2, -1, 4], ![0, 5, 4, -2, -6], ![-9, 57, 7, 18, -68], ![-1, 7, -1, 3, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [13, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 22], [0, 1]]
 g := ![![[5, 16], [20, 18], [6, 16], [1]], ![[0, 7], [0, 5], [1, 7], [1]]]
 h' := ![![[4, 22], [16, 19], [14, 8], [10, 4], [0, 1]], ![[0, 1], [0, 4], [0, 15], [3, 19], [4, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [5, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [13, 19, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![37125, -8573, -16489, -24260, 104860]
  a := ![37, -1, -40, -15, 100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13676, -87256, -16489, -24260, 104860]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 4, -1, 1, -6]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![1, 4, -1, 1, -6]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![6, 15, 1, 0, 0], ![2, 11, 0, 1, 0], ![3, 14, 0, 0, 1]] where
  M :=![![![1, 4, -1, 1, -6], ![-4, 6, 0, 1, -2], ![4, -3, 2, -2, 14], ![12, -8, 5, -4, 12], ![2, -3, 2, -1, 5]]]
  hmulB := by decide  
  f := ![![![7, -3, 2, -1, 4]], ![![0, 4, 1, 2, -6]], ![![2, 2, 1, 1, -2]], ![![2, 1, 1, 0, 0]], ![![1, 2, 1, 1, -3]]]
  g := ![![![1, 4, -1, 1, -6], ![0, 1, 0, 1, -2], ![-2, -9, 2, -2, 14], ![-2, -9, 5, -4, 12], ![-1, -4, 2, -1, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [16, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 22], [0, 1]]
 g := ![![[7, 13], [4, 9], [0, 9], [1]], ![[0, 10], [8, 14], [4, 14], [1]]]
 h' := ![![[3, 22], [5, 6], [0, 20], [7, 3], [0, 1]], ![[0, 1], [0, 17], [14, 3], [16, 20], [3, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [15, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [16, 20, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1912, -654, -272, -1331, 4223]
  a := ![7, 1, -9, -4, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-281, -1785, -272, -1331, 4223]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 2, -2, 1, -7]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-4, 2, -2, 1, -7]] 
 ![![23, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-4, 2, -2, 1, -7], ![-6, 2, -2, 1, -6], ![-4, -1, -2, 0, -2], ![-4, -2, -1, 0, -8], ![-1, -1, 0, 0, -1]]]
  hmulB := by decide  
  f := ![![![11, -11, 1, -2, 3]], ![![1, -1, 0, 0, -1]], ![![6, -6, 0, -1, 2]], ![![4, -3, 0, -2, 6]], ![![10, -10, 1, -2, 3]]]
  g := ![![![7, 2, -2, 1, -7], ![6, 2, -2, 1, -6], ![3, -1, -2, 0, -2], ![8, -2, -1, 0, -8], ![1, -1, 0, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![1, -2, 0, 0, 1]] ![![1, 4, -1, 1, -6]]
  ![![11, -11, 1, -2, 3]] where
 M := ![![![11, -11, 1, -2, 3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![11, -11, 1, -2, 3]] ![![-4, 2, -2, 1, -7]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)


lemma PB117I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB117I0 : PrimesBelowBoundCertificateInterval O 1 23 117 where
  m := 9
  g := ![3, 5, 5, 1, 3, 1, 3, 1, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB117I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N2, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0]
    · exact ![I23N0, I23N1, I23N2]
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
    · exact ![4, 4, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![16807]
    · exact ![121, 121, 11]
    · exact ![371293]
    · exact ![289, 289, 17]
    · exact ![2476099]
    · exact ![529, 529, 23]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
      exact NI3N2
      exact NI3N2
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
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I11N2, I17N2, I23N2]
  Il := ![[I2N0, I2N1, I2N2], [I3N0, I3N1, I3N1, I3N2, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N2], [], [I17N2], [], [I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
