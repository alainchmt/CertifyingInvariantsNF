
import IdealArithmetic.Examples.NF5_1_2025000000_5.RI5_1_2025000000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 2, 4, 0], ![0, 0, -1, -2, 1], ![58, 1, 4, -11, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![-29, 0, 0, 6, 0], ![-1, -4, 0, 0, 1]], ![![0, 0, 0, 1, 0], ![0, 1, 0, 1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 2, 4, 0], ![0, 0, -1, -2, 1], ![29, 1, 4, -11, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-5, -7, 2, 0, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![-5, -7, 2, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-5, -7, 2, 0, 1], ![58, -2, 1, -3, 0], ![0, 59, 3, 10, -3], ![-58, -29, 9, 2, 4], ![116, -44, 24, 2, 7]]]
  hmulB := by decide  
  f := ![![![150, -100, 10, -19, 8], ![-10, -6, 2, 0, 0]], ![![2366, -1563, 179, -290, 131], ![-179, -96, 29, 1, 0]], ![![56, -35, 1, -8, 2], ![-1, -2, 1, 0, 0]], ![![75, -50, 5, -9, 4], ![-5, -3, 1, 0, 0]], ![![-2363, 1567, -180, 290, -131], ![180, 96, -29, -1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, -7, 2, 0, 1], ![31, -2, 1, -3, 0], ![-36, 59, 3, 10, -3], ![-20, -29, 9, 2, 4], ![67, -44, 24, 2, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-5, -6, 2, 0, 1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![-5, -6, 2, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-5, -6, 2, 0, 1], ![58, -2, 2, -3, 0], ![0, 60, 5, 14, -3], ![-58, -29, 8, 0, 5], ![174, -43, 28, -9, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![2265, -1552, 493, -224, 212], ![-405, -112, 8, 1, 0]], ![![-278, 197, -62, 28, -27], ![51, 14, -1, 0, 0]], ![![-19, 13, -5, 2, -2], ![4, 1, 0, 0, 0]], ![![3, 3, -1, 0, 0], ![1, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![-1, -6, 2, 0, 1], ![29, -2, 2, -3, 0], ![-31, 60, 5, 14, -3], ![-21, -29, 8, 0, 5], ![91, -43, 28, -9, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![-5, -7, 2, 0, 1]]
  ![![2, 0, 0, 0, 0], ![-4, 2, 1, 1, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![-10, -14, 4, 0, 2]], ![![0, 2, 0, 0, 0], ![58, -2, 1, -3, 0]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-65, -478, 374, 253, 144], ![-30, -254, 0, 16, 0]]], ![![![12, 58, -48, -33, -18], ![6, 32, 0, -2, 0]], ![![3, -51, 52, 35, 18], ![-13, -32, 0, 2, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-4, 2, 1, 1, 0]] ![![2, 0, 0, 0, 0], ![-5, -7, 2, 0, 1]]
  ![![2, 0, 0, 0, 0], ![-8, 1, 0, 1, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![-10, -14, 4, 0, 2]], ![![-8, 4, 2, 2, 0], ![78, 54, 6, 6, -3]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![3, 0, 2, 1, 0], ![2, 2, 0, 0, 0]]], ![![![4, 1, 1, 0, 0], ![2, 0, 0, 0, 0]], ![![7, 19, 3, 4, 0], ![-8, -3, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-8, 1, 0, 1, 0]] ![![2, 0, 0, 0, 0], ![-5, -6, 2, 0, 1]]
  ![![2, 0, 0, 0, 0], ![-14, -5, 2, 1, 1]] where
 M := ![![![4, 0, 0, 0, 0], ![-10, -12, 4, 0, 2]], ![![-16, 2, 0, 2, 0], ![40, 17, -6, -3, -3]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![9, -1, 0, -1, 0], ![2, 0, 0, 0, 0]]], ![![![6, 6, -2, 0, -1], ![2, 0, 0, 0, 0]], ![![13, 6, -2, -1, -1], ![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-14, -5, 2, 1, 1]] ![![2, 0, 0, 0, 0], ![-5, -6, 2, 0, 1]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![-10, -12, 4, 0, 2]], ![![-28, -10, 4, 2, 2], ![-104, 142, 8, 34, -8]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0]], ![![-5, -6, 2, 0, 1]]], ![![![-14, -5, 2, 1, 1]], ![![-52, 71, 4, 17, -4]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![-8, 2, 0, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![-8, 2, 0, 1, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 2, 0, 1, 0], ![1, 2, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![-8, 2, 0, 1, 0], ![0, -8, 1, -2, 1], ![58, 2, 0, -3, -2], ![-58, 15, -1, 9, 0], ![-58, -27, 2, -7, 7]]]
  hmulB := by decide  
  f := ![![![-799, -3398, 458, -799, 450], ![-387, -1374, -12, 0, 0]], ![![-396, -1683, 227, -396, 223], ![-192, -681, -6, 0, 0]], ![![-261, -1134, 153, -267, 150], ![-127, -458, -4, 0, 0]], ![![-393, -1692, 228, -398, 224], ![-191, -684, -6, 0, 0]], ![![-533, -2254, 304, -530, 299], ![-258, -912, -8, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-1, 0, 3, 0, 0], ![-1, -2, 0, 3, 0], ![-1, -2, 0, 0, 3]], ![![-3, 0, 0, 1, 0], ![0, -2, 1, -2, 1], ![21, 4, 0, -3, -2], ![-22, -1, -1, 9, 0], ![-20, -9, 2, -7, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [1, 0, 1] where
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

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![64729, -19378, 6648, -16310, 6936]
  a := ![0, -9, -8, -9, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![22485, -210, 6648, -16310, 6936]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, 1, 4, 0], ![0, 0, -1, -3, 1], ![58, 1, 4, -11, -1]]]
  hmulB := by decide  
  f := ![![![2, 1, 0, 6, -2], ![3, 6, 0, 6, 0]], ![![1, 1, 1, 6, -2], ![1, 3, 0, 6, 0]], ![![1, 1, 3, 10, -2], ![1, 1, -3, 6, 0]], ![![2, -1, 0, 2, -1], ![4, 2, 1, 3, 0]], ![![1, 1, 0, 4, -1], ![1, 4, 0, 4, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![-2, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![-4, 1, 1, 4, 0], ![2, 0, -1, -3, 1], ![24, 1, 4, -11, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![-8, 2, 0, 1, 0]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![-4, 2, 1, 1, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![-3, 3, 0, 0, 0]], ![![-24, 6, 0, 3, 0], ![8, -10, 1, -3, 1]]]
 hmul := by decide  
 g := ![![![![-21, 15, 3, 4, -1], ![-18, 3, 0, 0, 0]], ![![15, -7, -4, -4, 0], ![12, 0, 0, 0, 0]]], ![![![80, -42, -22, -21, 0], ![66, 0, 0, 0, 0]], ![![-24, 14, 3, 3, -1], ![-20, 4, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![-4, 2, 1, 1, 0]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![-14, -5, 2, 1, 1]] where
 M := ![![![9, 0, 0, 0, 0], ![-3, 3, 0, 0, 0]], ![![-12, 6, 3, 3, 0], ![4, -5, 2, 1, 1]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![13, 6, -2, -1, -1], ![3, 0, 0, 0, 0]]], ![![![10, 7, -1, 0, -1], ![3, 0, 0, 0, 0]], ![![6, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![-14, -5, 2, 1, 1]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![-3, 3, 0, 0, 0]], ![![-42, -15, 6, 3, 3], ![72, -6, 0, -6, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0]], ![![-1, 1, 0, 0, 0]]], ![![![-14, -5, 2, 1, 1]], ![![24, -2, 0, -2, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![5, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![0, 0, 5, 0, 0], ![0, 0, 0, 5, 0], ![0, 0, 0, 0, 5]], ![![-2, 1, 0, 0, 0], ![0, -2, 1, 0, 0], ![0, 1, 0, 4, 0], ![0, 0, -1, -4, 1], ![58, 1, 4, -11, -2]]]
  hmulB := by decide  
  f := ![![![1, -3, 5, 20, -2], ![0, -15, -15, 10, 0]], ![![5, 1, 2, 20, -2], ![11, 0, -15, 10, 0]], ![![3, 2, 1, 16, -1], ![7, 1, -15, 5, 0]], ![![1, 1, 1, 9, -1], ![1, 0, -6, 5, 0]], ![![1, -2, 3, 12, -1], ![1, -9, -9, 6, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 5, 0, 0, 0], ![-1, 0, 5, 0, 0], ![-3, 0, 0, 5, 0], ![-3, 0, 0, 0, 5]], ![![-1, 1, 0, 0, 0], ![1, -2, 1, 0, 0], ![-3, 1, 0, 4, 0], ![2, 0, -1, -4, 1], ![18, 1, 4, -11, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![-8, 3, 0, 1, 0]] where
 M := ![![![25, 0, 0, 0, 0], ![-10, 5, 0, 0, 0]], ![![-10, 5, 0, 0, 0], ![4, -4, 1, 0, 0]]]
 hmul := by decide  
 g := ![![![![-21841, 10188, -458, 3240, -244], ![-13835, 1170, -25, 0, 0]], ![![4468, -2076, 92, -661, 49], ![2830, -235, 5, 0, 0]]], ![![![4468, -2076, 92, -661, 49], ![2830, -235, 5, 0, 0]], ![![802, -367, 15, -117, 8], ![508, -38, 1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![-8, 3, 0, 1, 0]] ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![12, -2, 1, -1, 0]] where
 M := ![![![25, 0, 0, 0, 0], ![-10, 5, 0, 0, 0]], ![![-40, 15, 0, 5, 0], ![16, -14, 2, -4, 1]]]
 hmul := by decide  
 g := ![![![![-379, 77, -31, 38, -1], ![160, -5, 0, 0, 0]], ![![142, -36, 11, -18, 1], ![-60, 5, 0, 0, 0]]], ![![![640, -144, 51, -71, 3], ![-270, 15, 0, 0, 0]], ![![-280, 47, -23, 24, 0], ![118, -1, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![12, -2, 1, -1, 0]] ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![14, -12, 1, -3, 1]] where
 M := ![![![25, 0, 0, 0, 0], ![-10, 5, 0, 0, 0]], ![![60, -10, 5, -5, 0], ![-24, 17, -1, 8, -1]]]
 hmul := by decide  
 g := ![![![![-9, 12, -1, 3, -1], ![5, 0, 0, 0, 0]], ![![-2, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![-2, 10, 0, 2, -1], ![5, 0, 0, 0, 0]], ![![-2, 1, 0, 1, 0], ![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![14, -12, 1, -3, 1]] ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![25, 0, 0, 0, 0], ![-10, 5, 0, 0, 0]], ![![70, -60, 5, -15, 5], ![30, 40, -5, 5, -5]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0]], ![![-2, 1, 0, 0, 0]]], ![![![14, -12, 1, -3, 1]], ![![6, 8, -1, 1, -1]]]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [4, 0, 6, 5, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 2, 0, 4, 5], [2, 3, 3, 4, 1], [1, 4, 1, 5, 4], [2, 4, 3, 1, 4], [0, 1]]
 g := ![![[4, 3, 1], []], ![[1, 5, 4, 3, 5, 4, 0, 3], [1, 1, 3, 2, 1, 2, 3, 6]], ![[2, 0, 5, 2, 6, 5, 1, 1], [0, 5, 0, 4, 5, 6, 1, 1]], ![[5, 6, 3, 4, 4, 1, 3, 1], [4, 6, 5, 1, 3, 1, 5, 1]], ![[1, 2, 2, 4, 0, 2, 0, 4], [1, 4, 5, 6, 6, 3, 2, 1]]]
 h' := ![![[5, 2, 0, 4, 5], [0, 0, 0, 1], [0, 1]], ![[2, 3, 3, 4, 1], [2, 6, 0, 2, 3], [5, 2, 0, 4, 5]], ![[1, 4, 1, 5, 4], [1, 2, 6, 4, 1], [2, 3, 3, 4, 1]], ![[2, 4, 3, 1, 4], [6, 2, 0, 1, 4], [1, 4, 1, 5, 4]], ![[0, 1], [4, 4, 1, 6, 6], [2, 4, 3, 1, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 1, 1, 6], [], [], []]
 b := ![[], [3, 0, 2, 1, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [4, 0, 6, 5, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1310598471413676032, -219760457358521982, -169062942846668724, 41535194220023952, 16346529093946926]
  a := ![3, -125, -127, -194, -121]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-187228353059096576, -31394351051217426, -24151848978095532, 5933599174289136, 2335218441992418]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [4, 0, 1, 8, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3, 8, 7, 6], [3, 8, 0, 8, 4], [6, 0, 5, 10, 10], [7, 10, 9, 8, 2], [0, 1]]
 g := ![![[7, 6, 10, 4, 1], [1], []], ![[7, 10, 1, 10, 1, 9, 4, 7], [9, 1, 7, 1, 1, 6], [7, 7, 4, 3]], ![[4, 0, 9, 0, 10, 1, 3, 5], [4, 0, 4, 2, 3, 1, 6, 3], [7, 9, 4, 5]], ![[1, 3, 0, 3, 1, 10, 9, 6], [2, 7, 2, 5, 2, 5, 6, 2], [10, 4, 1, 1]], ![[6, 1, 3, 5, 4, 5, 7, 2], [10, 3, 4, 5, 0, 8, 6, 6], [4, 7, 6, 4]]]
 h' := ![![[5, 3, 8, 7, 6], [7, 0, 10, 3, 10], [0, 0, 1], [0, 1]], ![[3, 8, 0, 8, 4], [9, 7, 8, 9, 5], [8, 2, 0, 10], [5, 3, 8, 7, 6]], ![[6, 0, 5, 10, 10], [0, 2, 10, 4, 2], [3, 1, 8, 7, 3], [3, 8, 0, 8, 4]], ![[7, 10, 9, 8, 2], [0, 3, 3, 3, 4], [7, 6, 2, 10, 3], [6, 0, 5, 10, 10]], ![[0, 1], [4, 10, 2, 3, 1], [0, 2, 0, 6, 5], [7, 10, 9, 8, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 6, 4, 1], [], [], []]
 b := ![[], [10, 0, 8, 7, 9], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [4, 0, 1, 8, 1, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3459865275625, -1030648115409, -483664284829, -87794733741, 132897494378]
  a := ![1, -9, -9, -13, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-314533206875, -93695283219, -43969480439, -7981339431, 12081590398]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 161051 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![-33, 3, 1, 4, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![-33, 3, 1, 4, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![8, 4, 10, 1, 0], ![8, 9, 7, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![-33, 3, 1, 4, 0], ![0, -32, 1, -4, 4], ![232, 5, -10, -32, -4], ![-174, 60, 5, 34, -7], ![-522, -51, 8, 65, 16]]]
  hmulB := by decide  
  f := ![![![-428, 71, 12, 56, -4], ![-169, 13, 0, 0, 0]], ![![0, 65, -2, 8, -8], ![0, 26, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![-238, 54, 7, 33, -4], ![-94, 13, 0, 0, 0]], ![![-7, -230, 8, -28, 29], ![-3, -94, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-8, -4, -10, 13, 0], ![-8, -9, -7, 0, 13]], ![![-5, -1, -3, 4, 0], ![0, -4, 1, -4, 4], ![40, 13, 26, -32, -4], ![-30, -1, -22, 34, -7], ![-90, -35, -58, 65, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [6, 7, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6, 10], [10, 6, 3], [0, 1]]
 g := ![![[0, 4, 9], [2, 9], [1]], ![[7, 7, 1, 4], [9, 9], [8, 7, 9, 12]], ![[2, 3, 3, 3], [], [3, 6, 3, 1]]]
 h' := ![![[0, 6, 10], [11, 3, 3], [7, 6, 10], [0, 1]], ![[10, 6, 3], [1, 9, 9], [4, 6, 3], [0, 6, 10]], ![[0, 1], [10, 1, 1], [7, 1], [10, 6, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 12], []]
 b := ![[], [4, 5, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [6, 7, 3, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4307562983, -389947185, 338286745, -685789719, 111662301]
  a := ![1, 45, 41, 55, 53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![684660179, 103711614, 493426756, -685789719, 111662301]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![6, 1, 0, 0, 0], ![0, 6, 1, 0, 0], ![0, 1, 8, 4, 0], ![0, 0, -1, 4, 1], ![58, 1, 4, -11, 6]]]
  hmulB := by decide  
  f := ![![![-1109, -362, -2380, -1092, 24], ![2405, -260, 3861, -312, 0]], ![![-570, -188, -1226, -564, 12], ![1236, -130, 1989, -156, 0]], ![![-267, -87, -577, -264, 6], ![579, -64, 936, -78, 0]], ![![-1020, -334, -2186, -1003, 22], ![2212, -236, 3546, -286, 0]], ![![-599, -198, -1282, -588, 13], ![1299, -134, 2079, -168, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 13, 0, 0, 0], ![-3, 0, 13, 0, 0], ![-12, 0, 0, 13, 0], ![-7, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0], ![-3, 6, 1, 0, 0], ![-6, 1, 8, 4, 0], ![-4, 0, -1, 4, 1], ![10, 1, 4, -11, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![-5, 1, 0, 0, 0], ![0, -5, 1, 0, 0], ![0, 1, -3, 4, 0], ![0, 0, -1, -7, 1], ![58, 1, 4, -11, -5]]]
  hmulB := by decide  
  f := ![![![-9, 27, -82, 169, -7], ![-26, -13, -390, 91, 0]], ![![-4, 21, -55, 115, -5], ![-12, 0, -260, 65, 0]], ![![-3, 6, -14, 27, -1], ![-8, 1, -65, 13, 0]], ![![4, 5, -12, 24, -1], ![10, 4, -55, 13, 0]], ![![4, 5, -13, 26, -1], ![10, 3, -60, 14, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-8, 13, 0, 0, 0], ![-1, 0, 13, 0, 0], ![-2, 0, 0, 13, 0], ![-2, 0, 0, 0, 13]], ![![-1, 1, 0, 0, 0], ![3, -5, 1, 0, 0], ![-1, 1, -3, 4, 0], ![1, 0, -1, -7, 1], ![6, 1, 4, -11, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![-33, 3, 1, 4, 0]] ![![13, 0, 0, 0, 0], ![6, 1, 0, 0, 0]]
  ![![13, 0, 0, 0, 0], ![-30, 3, 5, 5, 1]] where
 M := ![![![169, 0, 0, 0, 0], ![78, 13, 0, 0, 0]], ![![-429, 39, 13, 52, 0], ![-198, -14, 7, 20, 4]]]
 hmul := by decide  
 g := ![![![![13, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![6, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![-3, 0, -4, -1, -1], ![13, 0, 0, 0, 0]], ![![24, -5, -6, -5, -1], ![17, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![-30, 3, 5, 5, 1]] ![![13, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![169, 0, 0, 0, 0], ![-65, 13, 0, 0, 0]], ![![-390, 39, 65, 65, 13], ![208, -39, -13, -26, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0, 0, 0]], ![![-5, 1, 0, 0, 0]]], ![![![-30, 3, 5, 5, 1]], ![![16, -3, -1, -2, 0]]]]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [4, 14, 2, 0, 16, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6, 12, 10, 7], [13, 8, 3, 13, 15], [9, 3, 7, 4], [10, 16, 12, 7, 12], [0, 1]]
 g := ![![[12, 3, 9], [16, 1, 1, 1], [], []], ![[1, 3, 11, 2, 10, 12, 5, 7], [15, 9, 10, 2], [10, 11, 1, 15], [3, 15, 2, 15]], ![[11, 3, 10, 2, 16, 2, 9, 8], [12, 5, 2, 13], [14, 11, 13, 8], [11, 7, 3, 4]], ![[15, 7, 1, 16, 9], [0, 5, 14, 1], [4, 7, 10, 13], [4, 16]], ![[10, 11, 5, 13, 16, 5, 5, 10], [11, 8, 9, 4], [10, 14, 7, 9], [12, 3, 6, 8]]]
 h' := ![![[3, 6, 12, 10, 7], [4, 10, 1, 14], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[13, 8, 3, 13, 15], [0, 6, 8, 13, 16], [3, 8, 12, 12, 6], [14, 2, 3, 1, 10], [3, 6, 12, 10, 7]], ![[9, 3, 7, 4], [12, 9, 10, 1, 8], [14, 4, 1, 6, 9], [6, 9, 10, 8, 12], [13, 8, 3, 13, 15]], ![[10, 16, 12, 7, 12], [15, 15, 6, 10], [10, 6, 15, 2, 16], [14, 2, 5, 14, 9], [9, 3, 7, 4]], ![[0, 1], [15, 11, 9, 13, 10], [12, 16, 6, 14, 2], [1, 4, 15, 11, 3], [10, 16, 12, 7, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 0, 4, 9], [], [], []]
 b := ![[], [10, 3, 14, 14, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [4, 14, 2, 0, 16, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![78837756290215, 768181693684, 628392063255, -11184942808318, -2912041785897]
  a := ![-1, -6, 1, 10, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4637515075895, 45187158452, 36964239015, -657937812254, -171296575641]
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


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [10, 14, 13, 11, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 11, 1, 1, 1], [8, 1, 11, 5, 17], [5, 13, 9, 9, 16], [15, 12, 17, 4, 4], [0, 1]]
 g := ![![[17, 9, 14, 10, 1], [11, 7, 13, 10, 1], [], []], ![[18, 16, 16, 13, 18, 6, 2, 5], [1, 16, 2, 15, 3, 5, 18, 5], [8, 9, 13, 17], [11, 17, 12, 1]], ![[13, 7, 12, 11, 17, 14, 13, 17], [18, 18, 17, 3, 1, 0, 0, 17], [12, 3, 1, 1], [7, 4, 1, 4]], ![[2, 7, 4, 15, 2, 6], [2, 13, 14, 1, 3, 6, 9, 5], [8, 6], [0, 3, 17, 9]], ![[4, 15, 3, 13, 18, 7, 13, 1], [18, 5, 8, 6, 12, 4], [7, 7, 16, 6], [0, 15, 2, 16]]]
 h' := ![![[1, 11, 1, 1, 1], [4, 4, 9, 0, 18], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[8, 1, 11, 5, 17], [13, 16, 16, 4, 10], [2, 8, 6, 1, 10], [5, 2, 2, 17, 6], [1, 11, 1, 1, 1]], ![[5, 13, 9, 9, 16], [9, 15, 0, 12, 1], [11, 12, 15, 1, 1], [13, 11, 1, 14, 18], [8, 1, 11, 5, 17]], ![[15, 12, 17, 4, 4], [8, 0, 1, 13], [13, 2, 2, 16, 7], [6, 5, 9, 14], [5, 13, 9, 9, 16]], ![[0, 1], [3, 3, 12, 9, 9], [15, 16, 15, 1], [16, 1, 6, 12, 14], [15, 12, 17, 4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 9, 2, 18], [], [], []]
 b := ![[], [8, 7, 15, 6, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [10, 14, 13, 11, 9, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![72085851038290, -32692334422128, -1144461738156, -24518420296500, 4539739257204]
  a := ![0, -2, -14, -36, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3793992159910, -1720649180112, -60234828324, -1290443173500, 238933645116]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-25, 16, 1, 5, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-25, 16, 1, 5, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![18, 17, 14, 1, 0], ![17, 11, 1, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-25, 16, 1, 5, 0], ![0, -24, 13, -6, 5], ![290, 18, 28, 9, -6], ![-232, 75, -7, 37, 4], ![58, -67, 54, -63, 39]]]
  hmulB := by decide  
  f := ![![![-4874, 3216, 143, 999, -20], ![-4485, 92, 0, 0, 0]], ![![350, -223, -14, -70, 0], ![322, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![-3584, 2367, 105, 735, -15], ![-3298, 69, 0, 0, 0]], ![![-3446, 2269, 104, 705, -13], ![-3171, 60, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-18, -17, -14, 23, 0], ![-17, -11, -1, 0, 23]], ![![-5, -3, -3, 5, 0], ![1, 1, 4, -6, 5], ![10, -3, -4, 9, -6], ![-42, -26, -23, 37, 4], ![23, 25, 39, -63, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [8, 17, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 22, 4], [17, 0, 19], [0, 1]]
 g := ![![[8, 11, 2], [11, 12, 4], [7, 22, 1], []], ![[2, 10, 20, 18], [7, 5, 7, 12], [7, 6], [22, 16]], ![[19, 11, 14, 19], [15, 13, 11, 15], [14, 5, 6, 19], [7, 16]]]
 h' := ![![[5, 22, 4], [4, 1, 18], [13, 4, 2], [0, 0, 1], [0, 1]], ![[17, 0, 19], [5, 6, 4], [7, 7, 16], [10, 17], [5, 22, 4]], ![[0, 1], [6, 16, 1], [18, 12, 5], [3, 6, 22], [17, 0, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 21], []]
 b := ![[], [14, 18, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [8, 17, 1, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-97663257, -11140148, -4228712, 8558788, 4443552]
  a := ![13, -7, -2, 3, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14228775, -8935592, -5586752, 8558788, 4443552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-7, 1, 0, 0, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-7, 1, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-7, 1, 0, 0, 0], ![0, -7, 1, 0, 0], ![0, 1, -5, 4, 0], ![0, 0, -1, -9, 1], ![58, 1, 4, -11, -7]]]
  hmulB := by decide  
  f := ![![![491, -269, 1154, -1035, 11], ![1610, 115, 5382, -253, 0]], ![![358, -194, 843, -756, 8], ![1174, 92, 3933, -184, 0]], ![![430, -233, 1020, -918, 10], ![1410, 116, 4761, -230, 0]], ![![441, -246, 1052, -943, 10], ![1446, 99, 4905, -230, 0]], ![![50, -22, 100, -90, 1], ![164, 18, 468, -22, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-16, 23, 0, 0, 0], ![-20, 0, 23, 0, 0], ![-21, 0, 0, 23, 0], ![-2, 0, 0, 0, 23]], ![![-1, 1, 0, 0, 0], ![4, -7, 1, 0, 0], ![0, 1, -5, 4, 0], ![9, 0, -1, -9, 1], ![9, 1, 4, -11, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, 1, 4, 0], ![0, 0, -1, -3, 1], ![58, 1, 4, -11, -1]]]
  hmulB := by decide  
  f := ![![![4, -222, -219, -874, -2], ![69, 23, 5060, 46, 0]], ![![2, -220, -219, -874, -2], ![24, 23, 5060, 46, 0]], ![![2, -210, -207, -830, -2], ![24, 1, 4807, 46, 0]], ![![2, -116, -115, -458, -1], ![34, 17, 2651, 23, 0]], ![![2, -116, -114, -456, -1], ![34, 6, 2640, 24, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-22, 23, 0, 0, 0], ![-22, 0, 23, 0, 0], ![-12, 0, 0, 23, 0], ![-12, 0, 0, 0, 23]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![-4, 1, 1, 4, 0], ![2, 0, -1, -3, 1], ![4, 1, 4, -11, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![-25, 16, 1, 5, 0]] ![![23, 0, 0, 0, 0], ![-7, 1, 0, 0, 0]]
  ![![23, 0, 0, 0, 0], ![-57, 5, -8, 1, 1]] where
 M := ![![![529, 0, 0, 0, 0], ![-161, 23, 0, 0, 0]], ![![-575, 368, 23, 115, 0], ![175, -136, 6, -41, 5]]]
 hmul := by decide  
 g := ![![![![23, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![50, -4, 8, -1, -1], ![23, 0, 0, 0, 0]]], ![![![32, 11, 9, 4, -1], ![23, 0, 0, 0, 0]], ![![20, -7, 2, -2, 0], ![5, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![-57, 5, -8, 1, 1]] ![![23, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![529, 0, 0, 0, 0], ![-23, 23, 0, 0, 0]], ![![-1311, 115, -184, 23, 23], ![115, -69, 0, -46, 0]]]
 hmul := by decide  
 g := ![![![![23, 0, 0, 0, 0]], ![![-1, 1, 0, 0, 0]]], ![![![-57, 5, -8, 1, 1]], ![![5, -3, 0, -2, 0]]]]
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


lemma PB2802I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB2802I0 : PrimesBelowBoundCertificateInterval O 1 23 2802 where
  m := 9
  g := ![5, 4, 5, 1, 1, 3, 1, 1, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB2802I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0]
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
    · exact ![2, 2, 2, 2, 2]
    · exact ![9, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![16807]
    · exact ![161051]
    · exact ![2197, 13, 13]
    · exact ![1419857]
    · exact ![2476099]
    · exact ![12167, 23, 23]
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
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I13N0, I13N1, I13N2, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [], [I13N0, I13N1, I13N2], [], [], [I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
