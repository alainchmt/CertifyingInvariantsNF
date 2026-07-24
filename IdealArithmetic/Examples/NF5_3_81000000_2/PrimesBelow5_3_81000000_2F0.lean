
import IdealArithmetic.Examples.NF5_3_81000000_2.RI5_3_81000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![68, 184, 124, 4, -17]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![68, 184, 124, 4, -17]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![68, 184, 124, 4, -17], ![-102, -187, -67, 5, 8], ![48, 18, -62, -11, 10], ![60, 198, 157, 8, -22], ![-90, -144, -31, 7, 3]]]
  hmulB := by decide  
  f := ![![![73, 88, 63, 3, -9]], ![![-27, -31, -22, 0, 3]], ![![18, 18, 14, -1, 0]], ![![0, 18, 17, 14, -2]], ![![-15, -24, -6, 2, 14]]]
  g := ![![![34, 184, 124, 4, -17], ![-51, -187, -67, 5, 8], ![24, 18, -62, -11, 10], ![30, 198, 157, 8, -22], ![-45, -144, -31, 7, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -5, -5, -1, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-1, -5, -5, -1, 1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-1, -5, -5, -1, 1], ![6, 14, 9, 2, -2], ![-12, -24, -14, -5, 4], ![24, 48, 31, 14, -10], ![-24, -51, -37, -17, 12]]]
  hmulB := by decide  
  f := ![![![16, 19, 14, 1, -2]], ![![-6, -7, -5, 0, 1]], ![![6, 9, 8, 2, 0]], ![![0, 6, 11, 8, 4]], ![![17, 35, 40, 19, 7]]]
  g := ![![![-1, -5, -5, -1, 1], ![4, 14, 9, 2, -2], ![-8, -24, -14, -5, 4], ![17, 48, 31, 14, -10], ![-18, -51, -37, -17, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, 0, 0, 0]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-1, -1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-1, -1, 0, 0, 0], ![0, -1, -1, 0, 0], ![0, 0, -1, -1, 0], ![0, 0, -1, -1, -2], ![-6, -15, -15, -7, -1]]]
  hmulB := by decide  
  f := ![![![-14, -16, -13, -1, 2]], ![![-1, 0, 0, 0, 0]], ![![-13, -17, -13, -1, 2]], ![![-1, 1, -1, 0, 0]], ![![-7, -8, -6, -1, 1]]]
  g := ![![![0, -1, 0, 0, 0], ![1, -1, -1, 0, 0], ![1, 0, -1, -1, 0], ![2, 0, -1, -1, -2], ![16, -15, -15, -7, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![68, 184, 124, 4, -17]] ![![-1, -5, -5, -1, 1]]
  ![![52, 319, 333, 25, -48]] where
 M := ![![![52, 319, 333, 25, -48]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![52, 319, 333, 25, -48]] ![![-1, -5, -5, -1, 1]]
  ![![-382, -138, 500, 87, -80]] where
 M := ![![![-382, -138, 500, 87, -80]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-382, -138, 500, 87, -80]] ![![-1, -1, 0, 0, 0]]
  ![![862, 1720, 751, -27, -94]] where
 M := ![![![862, 1720, 751, -27, -94]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![862, 1720, 751, -27, -94]] ![![-1, -1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-298, -1172, -1034, -66, 148]]]
 hmul := by decide  
 g := ![![![![-149, -586, -517, -33, 74]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![135, 161, 111, 2, -20]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![135, 161, 111, 2, -20]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![135, 161, 111, 2, -20], ![-120, -165, -137, -29, 4], ![24, -60, -134, -109, -58], ![-348, -846, -1039, -540, -218], ![-666, -1779, -2261, -1228, -511]]]
  hmulB := by decide  
  f := ![![![-567, -681, 107, 72, -26]], ![![-52, -319, -333, -25, 48]], ![![288, 668, 376, 3, -50]], ![![-300, -462, -79, 26, 6]], ![![-126, -439, -361, -20, 51]]]
  g := ![![![45, 161, 111, 2, -20], ![-40, -165, -137, -29, 4], ![8, -60, -134, -109, -58], ![-116, -846, -1039, -540, -218], ![-222, -1779, -2261, -1228, -511]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![135, 161, 111, 2, -20]] ![![135, 161, 111, 2, -20]]
  ![![14193, 22398, 21196, 6982, 1290]] where
 M := ![![![14193, 22398, 21196, 6982, 1290]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![14193, 22398, 21196, 6982, 1290]] ![![135, 161, 111, 2, -20]]
  ![![-3551877, -10884039, -14504355, -8285920, -3604902]] where
 M := ![![![-3551877, -10884039, -14504355, -8285920, -3604902]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-3551877, -10884039, -14504355, -8285920, -3604902]] ![![135, 161, 111, 2, -20]]
  ![![5762841657, 15517284516, 19800192868, 10790724528, 4517189456]] where
 M := ![![![5762841657, 15517284516, 19800192868, 10790724528, 4517189456]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N3 : IdealMulLeCertificate' Table 
  ![![5762841657, 15517284516, 19800192868, 10790724528, 4517189456]] ![![135, 161, 111, 2, -20]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-7372506202833, -19985579003355, -25564346543685, -13970796487350, -5862260640540]]]
 hmul := by decide  
 g := ![![![![-2457502067611, -6661859667785, -8521448847895, -4656932162450, -1954086880180]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 37, 26, 11, -8]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![17, 37, 26, 11, -8]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![17, 37, 26, 11, -8], ![-48, -103, -72, -30, 22], ![132, 282, 197, 82, -60], ![-360, -768, -536, -223, 164], ![426, 909, 636, 265, -193]]]
  hmulB := by decide  
  f := ![![![1, 13, -10, -3, 2]], ![![3, 14, 2, -1, 0]], ![![-7, -13, -13, -1, 2]], ![![10, 22, 4, -1, 0]], ![![2, 17, 0, -1, 1]]]
  g := ![![![-22, 37, 26, 11, -8], ![61, -103, -72, -30, 22], ![-167, 282, 197, 82, -60], ![454, -768, -536, -223, 164], ![-539, 909, 636, 265, -193]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![17, 37, 26, 11, -8]] ![![17, 37, 26, 11, -8]]
  ![![-5423, -11570, -8084, -3364, 2466]] where
 M := ![![![-5423, -11570, -8084, -3364, 2466]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-5423, -11570, -8084, -3364, 2466]] ![![17, 37, 26, 11, -8]]
  ![![1657637, 3536517, 2470974, 1028221, -753750]] where
 M := ![![![1657637, 3536517, 2470974, 1028221, -753750]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![1657637, 3536517, 2470974, 1028221, -753750]] ![![17, 37, 26, 11, -8]]
  ![![-506661479, -1080946492, -755260240, -314278668, 230385832]] where
 M := ![![![-506661479, -1080946492, -755260240, -314278668, 230385832]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-506661479, -1080946492, -755260240, -314278668, 230385832]] ![![17, 37, 26, 11, -8]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![154862519705, 330394364585, 230847436890, 96060167255, -70418083720]]]
 hmul := by decide  
 g := ![![![![30972503941, 66078872917, 46169487378, 19212033451, -14083616744]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, -59, -17, 2, 2]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-43, -59, -17, 2, 2]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![3, 2, 2, 1, 1]] where
  M :=![![![-43, -59, -17, 2, 2], ![12, -13, -27, -3, 4], ![24, 72, 44, 1, -6], ![-36, -66, -17, 2, 2], ![-6, -39, -39, -2, 5]]]
  hmulB := by decide  
  f := ![![![-1, -1, -1, 0, 0]], ![![0, -1, -1, -1, 0]], ![![0, 0, -2, -1, -2]], ![![-12, -30, -31, -16, -2]], ![![-3, -8, -11, -6, -3]]]
  g := ![![![-7, -9, -3, 0, 2], ![0, -3, -5, -1, 4], ![6, 12, 8, 1, -6], ![-6, -10, -3, 0, 2], ![-3, -7, -7, -1, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [6, 2, 6, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 5, 4, 3], [3, 6], [1, 2, 3, 4], [0, 1]]
 g := ![![[2, 2, 6, 1], []], ![[1, 3, 2, 0, 1, 6], [5, 6, 0, 1, 4, 6]], ![[5, 5, 1, 6], []], ![[6, 2, 3, 1, 0, 1], [5, 3, 4, 6, 3, 1]]]
 h' := ![![[2, 5, 4, 3], [0, 0, 0, 1], [0, 1]], ![[3, 6], [6, 0, 2, 4], [2, 5, 4, 3]], ![[1, 2, 3, 4], [6, 1, 2, 6], [3, 6]], ![[0, 1], [6, 6, 3, 3], [1, 2, 3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6], []]
 b := ![[], [], [0, 3, 4, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [6, 2, 6, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8109117984, 21980592199, 28126691116, 15370925055, 6457209118]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1608929910, 1295167709, 2173181840, 1273387991, 6457209118]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 1, 0, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![1, 1, 1, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1, 1, 1, 0, 0], ![0, 1, 1, 1, 0], ![0, 0, 2, 1, 2], ![12, 30, 31, 16, 2], ![6, 21, 37, 22, 15]]]
  hmulB := by decide  
  f := ![![![43, 59, 17, -2, -2]], ![![29, 44, 16, -1, -2]], ![![15, 15, 1, -1, 0]], ![![42, 60, 17, -2, -2]], ![![7, 14, 8, 0, -1]]]
  g := ![![![-1, 1, 1, 0, 0], ![-2, 1, 1, 1, 0], ![-2, 0, 2, 1, 2], ![-47, 30, 31, 16, 2], ![-51, 21, 37, 22, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-43, -59, -17, 2, 2]] ![![1, 1, 1, 0, 0]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 16, 11, 5, -4]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![7, 16, 11, 5, -4]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![10, 9, 5, 1, 0], ![8, 10, 9, 0, 1]] where
  M :=![![![7, 16, 11, 5, -4], ![-24, -53, -39, -17, 10], ![60, 126, 80, 31, -34], ![-204, -450, -353, -158, 62], ![156, 300, 121, 25, -141]]]
  hmulB := by decide  
  f := ![![![-19, -44, -53, -5, 8]], ![![48, 101, 71, 3, -10]], ![![-60, -102, -46, 1, 6]], ![![-2, -1, -12, -2, 2]], ![![-16, -16, -7, 0, 1]]]
  g := ![![![-1, 1, 2, 5, -4], ![6, 0, -4, -17, 10], ![2, 17, 21, 31, -34], ![80, 32, -11, -158, 62], ![94, 135, 115, 25, -141]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [2, 3, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 4, 6], [10, 6, 5], [0, 1]]
 g := ![![[0, 6, 9], [9, 10, 1], []], ![[6, 7], [1, 4, 6, 7], [1, 3]], ![[9, 5, 3, 1], [2, 8, 2, 3], [2, 3]]]
 h' := ![![[0, 4, 6], [4, 8, 3], [0, 0, 1], [0, 1]], ![[10, 6, 5], [9, 5], [9, 2, 6], [0, 4, 6]], ![[0, 1], [9, 9, 8], [8, 9, 4], [10, 6, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6], []]
 b := ![[], [5, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [2, 3, 1, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-810811, -1695144, -919142, -588509, 594051]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![29261, -212643, -302096, -588509, 594051]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -44, -53, -5, 8]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-19, -44, -53, -5, 8]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![1, 6, 1, 0, 0], ![5, 9, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-19, -44, -53, -5, 8], ![48, 101, 71, 3, -10], ![-60, -102, -46, 1, 6], ![36, 30, -11, -4, 2], ![36, 84, 51, 1, -7]]]
  hmulB := by decide  
  f := ![![![7, 16, 11, 5, -4]], ![![-24, -53, -39, -17, 10]], ![![-7, -16, -13, -6, 2]], ![![-35, -77, -59, -26, 12]], ![![18, 36, 17, 5, -15]]]
  g := ![![![1, 29, -53, -5, 8], ![2, -32, 71, 3, -10], ![-5, 15, -46, 1, 6], ![5, 12, -11, -4, 2], ![2, -21, 51, 1, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 10], [0, 1]]
 g := ![![[2, 9], [0, 1], [1]], ![[4, 2], [10, 10], [1]]]
 h' := ![![[10, 10], [0, 8], [5, 10], [0, 1]], ![[0, 1], [3, 3], [6, 1], [10, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [6, 1, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![800, 2163, 2826, 1539, 666]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1247, -2604, 2826, 1539, 666]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![7, 16, 11, 5, -4]] ![![-19, -44, -53, -5, 8]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77, 171, 91, 0, -12]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![77, 171, 91, 0, -12]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![9, 11, 1, 0, 0], ![5, 5, 0, 1, 0], ![12, 2, 0, 0, 1]] where
  M :=![![![77, 171, 91, 0, -12], ![-72, -103, -9, 7, 0], ![0, -72, -96, -9, 14], ![84, 210, 129, 2, -18], ![-54, -57, 19, 6, -5]]]
  hmulB := by decide  
  f := ![![![53, 51, 37, -6, -2]], ![![-12, 23, 15, 23, -12]], ![![21, 40, 28, 10, -8]], ![![37, 76, 53, 21, -16]], ![![18, -11, -7, -20, 9]]]
  g := ![![![-46, -62, 91, 0, -12], ![-2, -3, -9, 7, 0], ![57, 77, -96, -9, 14], ![-67, -91, 129, 2, -18], ![-15, -22, 19, 6, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [4, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 12], [0, 1]]
 g := ![![[9, 10], [12], [3, 1]], ![[0, 3], [12], [6, 12]]]
 h' := ![![[3, 12], [5, 7], [1, 5], [0, 1]], ![[0, 1], [0, 6], [3, 8], [3, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [7, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [4, 10, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4749, 14322, 20751, 11509, 5971]
  a := ![1, 19, 4, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23939, -21802, 20751, 11509, 5971]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-83, -189, -104, -1, 14]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-83, -189, -104, -1, 14]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![2, 7, 1, 0, 0], ![12, 5, 0, 1, 0], ![7, 11, 0, 0, 1]] where
  M :=![![![-83, -189, -104, -1, 14], ![84, 127, 20, -6, -2], ![-12, 54, 91, 6, -12], ![-72, -192, -120, 7, 12], ![42, 27, -48, -21, 13]]]
  hmulB := by decide  
  f := ![![![709, 867, 620, 37, -92]], ![![-552, -671, -476, -24, 74]], ![![-154, -185, -129, -4, 22]], ![![420, 521, 380, 31, -50]], ![![-83, -85, -44, 16, 21]]]
  g := ![![![3, 30, -104, -1, 14], ![10, 3, 20, -6, -2], ![-14, -37, 91, 6, -12], ![0, 37, -120, 7, 12], ![23, 25, -48, -21, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [3, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 12], [0, 1]]
 g := ![![[11, 9], [10], [6, 1]], ![[0, 4], [10], [12, 12]]]
 h' := ![![[6, 12], [8, 3], [8, 7], [0, 1]], ![[0, 1], [0, 10], [11, 6], [6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [10, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [3, 7, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7797, -16608, -10876, -4282, 4214]
  a := ![0, 0, 4, -10, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2757, 2660, -10876, -4282, 4214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -104, -72, -30, 22]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-49, -104, -72, -30, 22]] 
 ![![13, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-49, -104, -72, -30, 22], ![132, 281, 196, 82, -60], ![-360, -768, -537, -224, 164], ![984, 2100, 1468, 611, -448], ![-1164, -2484, -1736, -722, 529]]]
  hmulB := by decide  
  f := ![![![395, 488, 336, 18, -50]], ![![220, 273, 188, 10, -28]], ![![47, 56, 39, 2, -6]], ![![139, 172, 116, 5, -18]], ![![360, 444, 304, 14, -47]]]
  g := ![![![57, -104, -72, -30, 22], ![-154, 281, 196, 82, -60], ![421, -768, -537, -224, 164], ![-1151, 2100, 1468, 611, -448], ![1362, -2484, -1736, -722, 529]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![77, 171, 91, 0, -12]] ![![-83, -189, -104, -1, 14]]
  ![![6377, 11754, 4269, -305, -512]] where
 M := ![![![6377, 11754, 4269, -305, -512]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![6377, 11754, 4269, -305, -512]] ![![-49, -104, -72, -30, 22]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-1937, -7618, -6721, -429, 962]]]
 hmul := by decide  
 g := ![![![![-149, -586, -517, -33, 74]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -20, -3, 1, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-13, -20, -3, 1, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![4, 14, 14, 1, 0], ![6, 6, 3, 0, 1]] where
  M :=![![![-13, -20, -3, 1, 0], ![0, -13, -19, -3, 2], ![12, 30, 14, -5, -6], ![-36, -78, -65, -28, -10], ![-36, -108, -135, -65, -25]]]
  hmulB := by decide  
  f := ![![![91, 112, 79, 5, -12]], ![![-72, -89, -63, -5, 10]], ![![60, 78, 56, 7, -10]], ![![8, 12, 9, 2, -2]], ![![18, 24, 17, 2, -3]]]
  g := ![![![-1, -2, -1, 1, 0], ![0, 1, 1, -3, 2], ![4, 8, 6, -5, -6], ![8, 22, 21, -28, -10], ![22, 56, 50, -65, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [8, 8, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 8, 10], [7, 8, 7], [0, 1]]
 g := ![![[13, 12, 13], [], [5, 1], []], ![[16, 10, 5, 10], [7, 16], [6, 13], [14, 15]], ![[14, 0, 11, 3], [0, 16], [5, 13], [0, 15]]]
 h' := ![![[15, 8, 10], [2, 15, 9], [11, 3], [0, 0, 1], [0, 1]], ![[7, 8, 7], [3, 5, 1], [5, 7, 13], [11, 8, 8], [15, 8, 10]], ![[0, 1], [4, 14, 7], [15, 7, 4], [15, 9, 8], [7, 8, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 7], []]
 b := ![[], [0, 3, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [8, 8, 12, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9124561, -24961628, -32408313, -17781662, -7747397]
  a := ![13, -1, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6381557, 15909766, 14104538, -17781662, -7747397]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -15, -14, -1, 2]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-5, -15, -14, -1, 2]] 
 ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-5, -15, -14, -1, 2], ![12, 25, 14, 0, -2], ![-12, -18, -5, 0, 0], ![0, -12, -18, -5, 0], ![6, 9, -6, -9, -5]]]
  hmulB := by decide  
  f := ![![![47, 117, 82, 41, -28]], ![![15, 40, 28, 15, -10]], ![![40, 90, 63, 28, -20]], ![![-39, -69, -48, -14, 12]], ![![115, 252, 176, 76, -55]]]
  g := ![![![11, -15, -14, -1, 2], ![-15, 25, 14, 0, -2], ![10, -18, -5, 0, 0], ![15, -12, -18, -5, 0], ![7, 9, -6, -9, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 24, 18, 2, -2]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![19, 24, 18, 2, -2]] 
 ![![17, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![19, 24, 18, 2, -2], ![-12, -11, -4, 4, 4], ![24, 48, 53, 24, 8], ![48, 144, 192, 109, 48], ![132, 360, 460, 252, 105]]]
  hmulB := by decide  
  f := ![![![-13, -216, -262, -22, 38]], ![![5, -107, -150, -14, 22]], ![![-27, -216, -237, -18, 34]], ![![-1, -72, -94, -9, 14]], ![![4, -168, -228, -20, 33]]]
  g := ![![![-29, 24, 18, 2, -2], ![5, -11, -4, 4, 4], ![-91, 48, 53, 24, 8], ![-337, 144, 192, 109, 48], ![-804, 360, 460, 252, 105]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-13, -20, -3, 1, 0]] ![![-5, -15, -14, -1, 2]]
  ![![-139, -263, -101, 8, 14]] where
 M := ![![![-139, -263, -101, 8, 14]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-139, -263, -101, 8, 14]] ![![19, 24, 18, 2, -2]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![323, 901, 1173, 646, 272]]]
 hmul := by decide  
 g := ![![![![19, 53, 69, 38, 16]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![347, 1180, 954, 50, -134]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![347, 1180, 954, 50, -134]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![14, 17, 15, 7, 1]] where
  M :=![![![347, 1180, 954, 50, -134], ![-804, -1663, -780, 16, 100], ![600, 696, -147, -80, 32], ![192, 1080, 1096, 77, -160], ![-780, -1452, -548, 28, 61]]]
  hmulB := by decide  
  f := ![![![-127, -148, -106, -2, 14]], ![![84, 83, 60, -8, -4]], ![![-24, 24, 15, 32, -16]], ![![-96, -264, -184, -97, 64]], ![![-62, -91, -65, -13, 13]]]
  g := ![![![117, 182, 156, 52, -134], ![-116, -177, -120, -36, 100], ![8, 8, -33, -16, 32], ![128, 200, 184, 63, -160], ![-86, -131, -77, -21, 61]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [8, 13, 1, 10, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 18, 11, 4], [14, 18], [11, 1, 8, 15], [0, 1]]
 g := ![![[2, 7, 8, 6], [6, 5, 8, 5], [1], []], ![[0, 8, 8, 13, 2, 4], [18, 13, 12, 0, 3, 17], [6, 7, 1], [0, 4, 16]], ![[6, 3, 13, 13], [12, 4, 9, 14], [1], []], ![[15, 4, 15, 15, 16, 15], [18, 10, 17, 9, 15, 2], [15, 3, 1], [0, 4, 16]]]
 h' := ![![[3, 18, 11, 4], [9, 3, 16, 14], [11, 6, 18, 9], [0, 0, 1], [0, 1]], ![[14, 18], [7, 9, 11, 1], [14, 18, 8, 16], [9, 0, 1, 18], [3, 18, 11, 4]], ![[11, 1, 8, 15], [12, 0, 15, 5], [9, 12, 16, 10], [6, 10, 1], [14, 18]], ![[0, 1], [17, 7, 15, 18], [5, 2, 15, 3], [7, 9, 16, 1], [11, 1, 8, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3], []]
 b := ![[], [], [16, 9, 16, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [8, 13, 1, 10, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![384699143, 1048663077, 1354549008, 742231697, 319114913]
  a := ![-1, -3, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-214889981, -230331076, -180640773, -78503826, 319114913]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-127, -148, -106, -2, 14]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-127, -148, -106, -2, 14]] 
 ![![19, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-127, -148, -106, -2, 14], ![84, 83, 60, -8, -4], ![-24, 24, 15, 32, -16], ![-96, -264, -184, -97, 64], ![204, 420, 292, 116, -89]]]
  hmulB := by decide  
  f := ![![![347, 1180, 954, 50, -134]], ![![49, 223, 210, 14, -30]], ![![269, 844, 645, 30, -90]], ![![211, 740, 610, 33, -86]], ![![32, 172, 172, 12, -25]]]
  g := ![![![103, -148, -106, -2, 14], ![-53, 83, 60, -8, -4], ![-33, 24, 15, 32, -16], ![233, -264, -184, -97, 64], ![-348, 420, 292, 116, -89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![347, 1180, 954, 50, -134]] ![![-127, -148, -106, -2, 14]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![121, 146, 106, 6, -14]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![121, 146, 106, 6, -14]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![16, 6, 22, 16, 1]] where
  M :=![![![121, 146, 106, 6, -14], ![-84, -89, -58, 8, 12], ![72, 96, 99, 26, 16], ![96, 312, 362, 211, 52], ![120, 390, 602, 350, 203]]]
  hmulB := by decide  
  f := ![![![23, 2, -38, -6, 6]], ![![36, 113, 86, 4, -12]], ![![-72, -144, -63, 2, 8]], ![![48, 48, -22, -7, 4]], ![![-8, -68, -76, -6, 11]]]
  g := ![![![15, 10, 18, 10, -14], ![-12, -7, -14, -8, 12], ![-8, 0, -11, -10, 16], ![-32, 0, -34, -27, 52], ![-136, -36, -168, -126, 203]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [6, 21, 1, 18, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 16, 2, 2], [8, 17, 18, 3], [22, 12, 3, 18], [0, 1]]
 g := ![![[8, 8, 1, 1], [20, 11, 22, 1], [5, 1], []], ![[1, 4, 9, 15, 2, 18], [21, 15, 3, 17, 3, 16], [21, 14, 9, 7, 15, 8], [20, 5, 4]], ![[22, 22, 8, 8], [16, 3, 9, 8, 21, 16], [18, 1, 14, 19, 7, 6], [9, 15, 9]], ![[20, 7, 13, 2, 22, 12], [13, 18, 18, 8, 1, 2], [0, 16, 7, 5, 3, 8], [17, 3, 2]]]
 h' := ![![[21, 16, 2, 2], [18, 0, 21, 1], [16, 4, 20, 1], [0, 0, 1], [0, 1]], ![[8, 17, 18, 3], [19, 8, 18, 3], [10, 11, 19, 13], [22, 15, 7, 21], [21, 16, 2, 2]], ![[22, 12, 3, 18], [5, 6, 8], [2, 12, 19, 17], [10, 16, 15, 18], [8, 17, 18, 3]], ![[0, 1], [8, 9, 22, 19], [11, 19, 11, 15], [14, 15, 0, 7], [22, 12, 3, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15, 22, 9], []]
 b := ![[], [], [9, 21, 18, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [6, 21, 1, 18, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8699979585, 23878413024, 31191368041, 17145484296, 7569874067]
  a := ![3, 0, 7, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4887739369, -936557886, -5884602671, -4520543512, 7569874067]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -2, 38, 6, -6]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-23, -2, 38, 6, -6]] 
 ![![23, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-23, -2, 38, 6, -6], ![-36, -113, -86, -4, 12], ![72, 144, 63, -2, -8], ![-48, -48, 22, 7, -4], ![-48, -126, -82, -2, 11]]]
  hmulB := by decide  
  f := ![![![-121, -146, -106, -6, 14]], ![![-70, -85, -62, -4, 8]], ![![-61, -74, -55, -4, 6]], ![![-41, -58, -48, -11, 2]], ![![-21, -36, -40, -16, -7]]]
  g := ![![![-19, -2, 38, 6, -6], ![108, -113, -86, -4, 12], ![-113, 144, 63, -2, -8], ![15, -48, 22, 7, -4], ![113, -126, -82, -2, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![121, 146, 106, 6, -14]] ![![-23, -2, 38, 6, -6]]
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


lemma PB441I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB441I0 : PrimesBelowBoundCertificateInterval O 1 23 441 where
  m := 9
  g := ![5, 5, 5, 2, 2, 3, 3, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB441I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1]
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
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![2401, 7]
    · exact ![1331, 121]
    · exact ![169, 169, 13]
    · exact ![4913, 17, 17]
    · exact ![130321, 19]
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
      exact NI3N0
      exact NI3N0
      exact NI3N0
      exact NI3N0
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
      exact NI7N1
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
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I5N0, I7N1, I11N1, I13N0, I13N1, I13N2, I17N1, I17N2, I19N1, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N0, I3N0, I3N0], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1], [I13N0, I13N1, I13N2], [I17N1, I17N2], [I19N1], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
