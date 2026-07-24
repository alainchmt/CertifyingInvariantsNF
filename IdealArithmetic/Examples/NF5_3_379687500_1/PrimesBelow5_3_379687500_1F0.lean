
import IdealArithmetic.Examples.NF5_3_379687500_1.RI5_3_379687500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-292, 121, -531, 239, 606]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-292, 121, -531, 239, 606]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-292, 121, -531, 239, 606], ![128, -53, 232, -104, -264], ![-56, 24, -101, 48, 120], ![24, -8, 48, -5, -24], ![-23, 9, -43, 15, 41]]]
  hmulB := by decide  
  f := ![![![3, 5, 1, -5, -18]], ![![-4, -1, 4, 12, 48]], ![![24, 8, -13, -80, -312]], ![![-152, -56, 80, 499, 1944]], ![![84, 33, -43, -273, -1063]]]
  g := ![![![-449, 121, -531, 239, 606], ![196, -53, 232, -104, -264], ![-88, 24, -101, 48, 120], ![24, -8, 48, -5, -24], ![-32, 9, -43, 15, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18, -36, 16, -6, -17]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-18, -36, 16, -6, -17]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-18, -36, 16, -6, -17], ![-5, -24, -37, 16, 37], ![5, 11, -13, 13, 43], ![17, 18, 7, -50, -185], ![-10, -10, 1, 25, 95]]]
  hmulB := by decide  
  f := ![![![2086, -869, 3790, -1705, -4324]], ![![586, -244, 1065, -478, -1213]], ![![1243, -517, 2260, -1010, -2566]], ![![954, -392, 1744, -741, -1909]], ![![83, -36, 148, -78, -190]]]
  g := ![![![4, -36, 16, -6, -17], ![20, -24, -37, 16, 37], ![-3, 11, -13, 13, 43], ![21, 18, 7, -50, -185], ![-13, -10, 1, 25, 95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-320, -559, 541, -227, -603]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-320, -559, 541, -227, -603]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-320, -559, 541, -227, -603], ![-149, -547, -637, 300, 717], ![117, 151, -364, 161, 411], ![89, 278, 223, -93, -225], ![-57, -137, -18, 8, 14]]]
  hmulB := by decide  
  f := ![![![-187, -90, 164, 681, 2685]], ![![568, 202, -284, -1844, -7179]], ![![-4246, -1568, 2297, 13967, 54459]], ![![25770, 9429, -13678, -84493, -329325]], ![![-14119, -5183, 7545, 46346, 180665]]]
  g := ![![![264, -559, 541, -227, -603], ![9, -547, -637, 300, 717], ![-121, 151, -364, 161, 411], ![-47, 278, 223, -93, -225], ![38, -137, -18, 8, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-292, 121, -531, 239, 606]] ![![-18, -36, 16, -6, -17]]
  ![![-1, 9, 33, -15, -37]] where
 M := ![![![-1, 9, 33, -15, -37]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-1, 9, 33, -15, -37]] ![![-18, -36, 16, -6, -17]]
  ![![253, 283, -920, 404, 1029]] where
 M := ![![![253, 283, -920, 404, 1029]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![253, 283, -920, 404, 1029]] ![![-18, -36, 16, -6, -17]]
  ![![-13991, -29038, 9394, -3425, -10375]] where
 M := ![![![-13991, -29038, 9394, -3425, -10375]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-13991, -29038, 9394, -3425, -10375]] ![![-320, -559, 541, -227, -603]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![10189430, 25592474, 6931634, -3787484, -7897364]]]
 hmul := by decide  
 g := ![![![![5094715, 12796237, 3465817, -1893742, -3948682]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N1, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, 12, -51, 25, 62]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-29, 12, -51, 25, 62]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-29, 12, -51, 25, 62], ![12, -4, 25, 2, -4], ![-8, 14, 6, 83, 152], ![-14, 75, 111, 505, 902], ![2, -19, -32, -131, -233]]]
  hmulB := by decide  
  f := ![![![-7, -3, 9, 16, 66]], ![![9, 2, -4, -33, -128]], ![![-78, -29, 44, 252, 984]], ![![455, 167, -240, -1494, -5822]], ![![-248, -91, 132, 813, 3169]]]
  g := ![![![12, 12, -51, 25, 62], ![-12, -4, 25, 2, -4], ![-39, 14, 6, 83, 152], ![-272, 75, 111, 505, 902], ![72, -19, -32, -131, -233]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -72, -147, 69, 170]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-11, -72, -147, 69, 170]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-11, -72, -147, 69, 170], ![32, 58, -35, 6, 8], ![-4, 38, 68, 19, 116], ![78, 15, -21, -305, -1174], ![-46, -19, 4, 169, 645]]]
  hmulB := by decide  
  f := ![![![-2269, 943, -4127, 1838, 4674]], ![![-1180, 485, -2157, 917, 2362]], ![![-1650, 653, -3066, 1102, 2984]], ![![-1398, 368, -2965, -394, 180]], ![![-1586, 715, -2774, 1685, 3975]]]
  g := ![![![-17, -72, -147, 69, 170], ![-14, 58, -35, 6, 8], ![-162, 38, 68, 19, 116], ![1016, 15, -21, -305, -1174], ![-548, -19, 4, 169, 645]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 1, 1, -18, -68]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![7, 1, 1, -18, -68]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![7, 1, 1, -18, -68], ![-32, -11, 15, 103, 400], ![194, 71, -102, -634, -2474], ![-1206, -440, 643, 3964, 15430], ![654, 239, -348, -2147, -8363]]]
  hmulB := by decide  
  f := ![![![-163, -204, 533, -233, -596]], ![![-152, -268, 253, -106, -282]], ![![-92, -130, 256, -111, -286]], ![![-86, -75, 383, -169, -428]], ![![-12, -25, 8, -3, -9]]]
  g := ![![![13, 1, 1, -18, -68], ![-82, -11, 15, 103, 400], ![508, 71, -102, -634, -2474], ![-3180, -440, 643, 3964, 15430], ![1722, 239, -348, -2147, -8363]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-29, 12, -51, 25, 62]] ![![-11, -72, -147, 69, 170]]
  ![![5, 43, 98, -45, -110]] where
 M := ![![![5, 43, 98, -45, -110]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![5, 43, 98, -45, -110]] ![![-11, -72, -147, 69, 170]]
  ![![2479, 7273, 4929, -2400, -5558]] where
 M := ![![![2479, 7273, 4929, -2400, -5558]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![2479, 7273, 4929, -2400, -5558]] ![![-11, -72, -147, 69, 170]]
  ![![254219, 500250, -255628, 101038, 284068]] where
 M := ![![![254219, 500250, -255628, 101038, 284068]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![254219, 500250, -255628, 101038, 284068]] ![![7, 1, 1, -18, -68]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![108345, 37413, -56205, -361404, -1407564]]]
 hmul := by decide  
 g := ![![![![36115, 12471, -18735, -120468, -469188]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N1, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 3, 0, -41, -156]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![15, 3, 0, -41, -156]] 
 ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![15, 3, 0, -41, -156], ![-74, -26, 36, 239, 930], ![452, 165, -239, -1481, -5772], ![-2810, -1029, 1494, 9216, 35922], ![1524, 558, -810, -4998, -19481]]]
  hmulB := by decide  
  f := ![![![-21, -57, -18, 5, 12]], ![![-8, -26, -18, 1, 6]], ![![-1, -12, -11, -34, -60]], ![![-5, -66, -54, -225, -402]], ![![-15, -27, 0, 63, 115]]]
  g := ![![![120, 3, 0, -41, -156], ![-713, -26, 36, 239, 930], ![4424, 165, -239, -1481, -5772], ![-27532, -1029, 1494, 9216, 35922], ![14931, 558, -810, -4998, -19481]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![15, 3, 0, -41, -156]] ![![15, 3, 0, -41, -156]]
  ![![-122531, -44892, 65214, 401934, 1566684]] where
 M := ![![![-122531, -44892, 65214, 401934, 1566684]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-122531, -44892, 65214, 401934, 1566684]] ![![15, 3, 0, -41, -156]]
  ![![1289152647, 472179495, -685726902, -4228350239, -16481347788]] where
 M := ![![![1289152647, 472179495, -685726902, -4228350239, -16481347788]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![1289152647, 472179495, -685726902, -4228350239, -16481347788]] ![![15, 3, 0, -41, -156]]
  ![![-13561462409951, -4967173817532, 7213623642612, 44480857624440, 173378373768432]] where
 M := ![![![-13561462409951, -4967173817532, 7213623642612, 44480857624440, 173378373768432]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-13561462409951, -4967173817532, 7213623642612, 44480857624440, 173378373768432]] ![![15, 3, 0, -41, -156]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![142662138511222695, 52253040100293255, -75884955769531980, -467924039426074625, -1823883650977198980]]]
 hmul := by decide  
 g := ![![![![28532427702244539, 10450608020058651, -15176991153906396, -93584807885214925, -364776730195439796]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-301, -1119, -1341, 630, 1508]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-301, -1119, -1341, 630, 1508]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![6, 4, 1, 0, 0], ![4, 4, 0, 1, 0], ![1, 1, 0, 0, 1]] where
  M :=![![![-301, -1119, -1341, 630, 1508], ![248, 329, -737, 321, 824], ![182, 569, 468, -224, -526], ![-78, -42, 423, -184, -466], ![-4, -91, -254, 115, 283]]]
  hmulB := by decide  
  f := ![![![545, 202, -297, -1795, -7000]], ![![-3410, -1250, 1817, 11188, 43610]], ![![1552, 570, -830, -5095, -19862]], ![![-20520, -7515, 10913, 67303, 262332]], ![![9831, 3601, -5230, -32246, -125689]]]
  g := ![![![531, 31, -1341, 630, 1508], ![366, 167, -737, 321, 824], ![-172, 17, 468, -224, -526], ![-202, -76, 423, -184, -466], ![111, 26, -254, 115, 283]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6], [0, 1]]
 g := ![![[3, 1], [5, 1]], ![[1, 6], [3, 6]]]
 h' := ![![[5, 6], [6, 1], [0, 1]], ![[0, 1], [4, 6], [5, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [3, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18156, 18177, 39321, 197016, 443415]
  a := ![5, -3, -9, -44, -105]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-212223, -195798, 39321, 197016, 443415]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -8, 25, -11, -28]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-7, -8, 25, -11, -28]] 
 ![![7, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![-7, -8, 25, -11, -28], ![-6, -18, -13, 6, 14], ![2, 0, -14, 5, 14], ![4, 7, 1, -13, -28], ![-2, -3, 2, 3, 7]]]
  hmulB := by decide  
  f := ![![![511, -213, 929, -418, -1060]], ![![187, -78, 340, -153, -388]], ![![379, -158, 689, -310, -786]], ![![432, -180, 785, -354, -898]], ![![40, -17, 74, -31, -77]]]
  g := ![![![-6, -8, 25, -11, -4], ![11, -18, -13, 6, 2], ![6, 0, -14, 5, 2], ![8, 7, 1, -13, -4], ![-3, -3, 2, 3, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6], [0, 1]]
 g := ![![[2, 2], [4, 1]], ![[3, 5], [1, 6]]]
 h' := ![![[4, 6], [1, 4], [0, 1]], ![[0, 1], [3, 3], [4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [6, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [5, 3, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2351537, 3174388, 6072765, 30057889, 64405404]
  a := ![59, -60, -118, -533, -1236]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31797980, 3174388, 6072765, 30057889, 9200772]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, 224, -710, -562, -2544]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-67, 224, -710, -562, -2544]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-67, 224, -710, -562, -2544], ![-1420, -629, 1082, 5000, 19644], ![9644, 3580, -5273, -31782, -123948], ![-60384, -22138, 32182, 198121, 772272], ![32736, 12010, -17472, -107434, -418787]]]
  hmulB := by decide  
  f := ![![![5643, 22436, 29442, -13774, -33096]], ![![2432, 11659, 18854, -8748, -21180]], ![![3517, 14356, 19505, -9112, -21924]], ![![1069, 3418, 3000, -1437, -3384]], ![![4025, 16258, 21790, -10184, -24491]]]
  g := ![![![2267, 224, -710, -562, -2544], ![-15362, -629, 1082, 5000, 19644], ![96173, 3580, -5273, -31782, -123948], ![-598889, -22138, 32182, 198121, 772272], ![324775, 12010, -17472, -107434, -418787]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-301, -1119, -1341, 630, 1508]] ![![-7, -8, 25, -11, -28]]
  ![![5643, 22436, 29442, -13774, -33096]] where
 M := ![![![5643, 22436, 29442, -13774, -33096]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![5643, 22436, 29442, -13774, -33096]] ![![-67, 224, -710, -562, -2544]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65, -27, 44, 223, 874]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-65, -27, 44, 223, 874]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![5, 4, 7, 1, 0], ![6, 1, 9, 0, 1]] where
  M :=![![![-65, -27, 44, 223, 874], ![428, 158, -232, -1409, -5492], ![-2674, -981, 1423, 8767, 34186], ![16652, 6093, -8866, -54654, -212948], ![-9030, -3306, 4806, 29628, 115463]]]
  hmulB := by decide  
  f := ![![![437, 1047, 154, -97, -178]], ![![16, 340, 934, -427, -1048]], ![![-194, -411, 107, -37, -118]], ![![77, 317, 441, -206, -496]], ![![86, 281, 269, -128, -303]]]
  g := ![![![-584, -163, -853, 223, 874], ![3675, 1026, 5369, -1409, -5492], ![-22875, -6385, -33420, 8767, 34186], ![142510, 39787, 208204, -54654, -212948], ![-77268, -21571, -112887, 29628, 115463]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [2, 8, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 2, 9], [5, 8, 2], [0, 1]]
 g := ![![[3, 8, 4], [4, 10, 1], []], ![[5, 6, 1, 9], [10, 0, 1, 4], [10, 4]], ![[0, 5, 4, 2], [10, 4, 7, 8], [6, 4]]]
 h' := ![![[5, 2, 9], [3, 3, 2], [0, 0, 1], [0, 1]], ![[5, 8, 2], [6, 2, 10], [5, 9, 8], [5, 2, 9]], ![[0, 1], [0, 6, 10], [2, 2, 2], [5, 8, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 4], []]
 b := ![[], [7, 0, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [2, 8, 1, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31161318, -65034534, -107910802, -525452256, -1048871546]
  a := ![4, -3, -7, -36, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![813786534, 280513276, 1182736264, -525452256, -1048871546]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![437, 1047, 154, -97, -178]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![437, 1047, 154, -97, -178]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![5, 4, 1, 0, 0], ![2, 0, 0, 1, 0], ![9, 10, 0, 0, 1]] where
  M :=![![![437, 1047, 154, -97, -178], ![16, 340, 934, -427, -1048], ![-194, -411, 107, -37, -118], ![-44, -231, -404, 186, 452], ![54, 168, 138, -66, -155]]]
  hmulB := by decide  
  f := ![![![-65, -27, 44, 223, 874]], ![![428, 158, -232, -1409, -5492]], ![![-117, -44, 65, 386, 1508]], ![![1502, 549, -798, -4928, -19200]], ![![-485, -179, 262, 1595, 6219]]]
  g := ![![![133, 201, 154, -97, -178], ![512, 644, 934, -427, -1048], ![37, 31, 107, -37, -118], ![-224, -285, -404, 186, 452], ![81, 106, 138, -66, -155]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [3, 5, 1] where
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
 g := ![![[9, 4], [4, 3], [1]], ![[0, 7], [0, 8], [1]]]
 h' := ![![[6, 10], [10, 2], [8, 6], [0, 1]], ![[0, 1], [0, 9], [0, 5], [6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [3, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [3, 5, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-492949, 514561, 1092710, 5465233, 12216686]
  a := ![-26, 23, 50, 230, 547]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11530649, -11456649, 1092710, 5465233, 12216686]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-65, -27, 44, 223, 874]] ![![437, 1047, 154, -97, -178]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [8, 1, 1, 10, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 0, 11, 4, 7], [12, 10, 10, 6, 1], [3, 9, 6, 12, 12], [6, 6, 12, 4, 6], [0, 1]]
 g := ![![[8, 10, 5, 12, 10], [9, 1], []], ![[3, 7, 6, 12, 7, 0, 5, 2], [10, 3], [3, 1, 6, 12, 4, 8, 9, 5]], ![[9, 4, 7, 7, 6, 2, 11, 9], [1, 4, 3, 9], [7, 10, 1, 8, 8, 7, 1, 1]], ![[3, 10, 7, 1, 8, 9, 11, 10], [10, 2, 2, 9], [3, 5, 10, 4, 8, 8, 1, 12]], ![[9, 3, 1, 7, 6, 4, 6, 11], [1, 9, 7, 10], [1, 8, 4, 10, 12, 8, 10, 8]]]
 h' := ![![[1, 0, 11, 4, 7], [6, 9, 3, 0, 6], [0, 0, 0, 1], [0, 1]], ![[12, 10, 10, 6, 1], [7, 4, 7, 5, 2], [3, 2, 7, 9], [1, 0, 11, 4, 7]], ![[3, 9, 6, 12, 12], [4, 4, 8, 1, 3], [8, 8, 4, 0, 10], [12, 10, 10, 6, 1]], ![[6, 6, 12, 4, 6], [7, 4, 5, 3, 4], [3, 5, 10, 11, 10], [3, 9, 6, 12, 12]], ![[0, 1], [5, 5, 3, 4, 11], [0, 11, 5, 5, 6], [6, 6, 12, 4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 10, 5, 4], [], [], []]
 b := ![[], [0, 6, 3, 9, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [8, 1, 1, 10, 4, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![69789509720417929, -42495805121139292, -118433686525927084, -605698628350715224, -1471326880943957232]
  a := ![11, -6, -16, -92, -232]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5368423824647533, -3268908086241484, -9110283578917468, -46592202180824248, -113178990841842864]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![453, -99, 555, -652, -2164]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![453, -99, 555, -652, -2164]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![8, 13, 8, 8, 1]] where
  M :=![![![453, -99, 555, -652, -2164], ![-860, -199, 109, 2455, 9404], ![4494, 1595, -2238, -14580, -56758], ![-27598, -10086, 14613, 90450, 352526], ![14978, 5465, -7904, -49061, -191201]]]
  hmulB := by decide  
  f := ![![![-27, -58, 9, 5, 4]], ![![-6, -22, -47, 70, 142]], ![![2, 64, 46, 291, 526]], ![![-56, 293, 411, 1837, 3280]], ![![-42, 119, 177, 1029, 1851]]]
  g := ![![![1045, 1649, 1051, 980, -2164], ![-4476, -7203, -4419, -4281, 9404], ![26974, 43497, 26578, 25852, -56758], ![-167518, -270172, -165035, -160574, 352526], ![90858, 146534, 89512, 87091, -191201]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [8, 14, 6, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 16, 6, 13], [5, 14, 0, 8], [8, 3, 11, 13], [0, 1]]
 g := ![![[13, 4], [2, 9, 2], [1], []], ![[11, 2, 3, 0, 8, 8], [12, 16, 16], [4, 6, 8], [13, 9, 16]], ![[13, 13, 2, 15], [13, 11, 15], [1, 3, 9], [2, 7, 13]], ![[8, 7, 11, 1, 15, 8], [3, 7, 8], [14, 1, 4], [0, 3, 16]]]
 h' := ![![[15, 16, 6, 13], [14, 5, 2], [9, 3, 11, 11], [0, 0, 1], [0, 1]], ![[5, 14, 0, 8], [8, 5, 0, 7], [6, 1, 14, 4], [2, 5, 2, 5], [15, 16, 6, 13]], ![[8, 3, 11, 13], [6, 12, 15], [5, 1, 6, 7], [9, 5, 16, 14], [5, 14, 0, 8]], ![[0, 1], [12, 12, 0, 10], [6, 12, 3, 12], [13, 7, 15, 15], [8, 3, 11, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 13, 14], []]
 b := ![[], [], [6, 12, 7, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [8, 14, 6, 6, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1008788797936, -368842976852, 537369148408, 3312356303248, 12902506855896]
  a := ![-4, 2, 8, 24, 84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6131108449712, -9888319535500, -6040157982280, -5876923443760, 12902506855896]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 58, -9, -5, -4]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![27, 58, -9, -5, -4]] 
 ![![17, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![27, 58, -9, -5, -4], ![6, 22, 47, -70, -142], ![-2, -64, -46, -291, -526], ![56, -293, -411, -1837, -3280], ![-12, 83, 108, 481, 859]]]
  hmulB := by decide  
  f := ![![![-453, 99, -555, 652, 2164]], ![![-56, 35, -137, 9, -44]], ![![-291, -88, 99, 896, 3466]], ![![1277, 669, -1284, -4822, -19082]], ![![-961, -304, 367, 3001, 11629]]]
  g := ![![![-7, 58, -9, -5, -4], ![71, 22, 47, -70, -142], ![333, -64, -46, -291, -526], ![2080, -293, -411, -1837, -3280], ![-546, 83, 108, 481, 859]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![453, -99, 555, -652, -2164]] ![![27, 58, -9, -5, -4]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
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


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [6, 6, 4, 11, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 10, 9, 10, 5], [7, 2, 18, 11, 2], [8, 3, 6, 10, 4], [15, 3, 5, 7, 8], [0, 1]]
 g := ![![[9, 11, 9, 17, 9], [12, 0, 14, 14, 1], [], []], ![[14, 14, 18, 4, 1, 9, 4, 17], [13, 15, 15, 14, 0, 13, 12, 16], [10, 5, 2, 5], [8, 2, 13, 6]], ![[6, 12, 5, 5, 14, 0, 8, 15], [0, 1, 7, 5, 18, 18, 2, 15], [17, 18, 9, 6], [17, 10, 5, 4]], ![[7, 2, 5, 2, 17, 1, 2, 9], [8, 7, 3, 3, 13, 5, 0, 6], [3, 2, 1, 17], [11, 10, 0, 16]], ![[3, 11, 7, 10, 5, 18, 13, 13], [4, 17, 7, 16, 2, 9, 1, 14], [10, 13, 14, 7], [15, 9, 1, 7]]]
 h' := ![![[3, 10, 9, 10, 5], [4, 4, 1, 4, 3], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[7, 2, 18, 11, 2], [10, 2, 6, 6, 12], [17, 5, 6, 15, 8], [18, 0, 13, 11, 9], [3, 10, 9, 10, 5]], ![[8, 3, 6, 10, 4], [16, 10, 10, 17, 13], [9, 10, 4, 3, 13], [4, 18, 3, 2, 5], [7, 2, 18, 11, 2]], ![[15, 3, 5, 7, 8], [0, 11, 15, 13, 8], [5, 16, 8, 15, 12], [17, 17, 1, 15, 13], [8, 3, 6, 10, 4]], ![[0, 1], [10, 11, 6, 17, 2], [1, 7, 1, 5, 4], [2, 3, 1, 10, 11], [15, 3, 5, 7, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 1, 17, 10], [], [], []]
 b := ![[], [5, 13, 6, 2, 17], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [6, 6, 4, 11, 5, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-954822663951728, 2392021360196297, 3783560728888331, 18311093735016154, 35536186340788305]
  a := ![-4, 8, 13, 41, 97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-50253824418512, 125895861062963, 199134775204649, 963741775527166, 1870325596883595]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![859, -336, 1495, -771, -2080]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![859, -336, 1495, -771, -2080]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![3, 2, 1, 0, 0], ![17, 22, 0, 1, 0], ![11, 21, 0, 0, 1]] where
  M :=![![![859, -336, 1495, -771, -2080], ![-538, 88, -569, 868, 2978], ![1242, 330, -286, -3681, -14170], ![-6808, -2439, 3457, 22157, 86288], ![3720, 1311, -1824, -12039, -46853]]]
  hmulB := by decide  
  f := ![![![701, -237, -5713, 2562, 6400]], ![![1276, 3263, 1049, -559, -1196]], ![![199, 284, -533, 230, 594]], ![![1713, 2887, -3218, 1356, 3578]], ![![1511, 2883, -1798, 726, 1997]]]
  g := ![![![1407, 2492, 1495, -771, -2080], ![-2015, -3496, -569, 868, 2978], ![9589, 16498, -286, -3681, -14170], ![-58392, -100385, 3457, 22157, 86288], ![31706, 54510, -1824, -12039, -46853]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [19, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 22], [0, 1]]
 g := ![![[4, 16], [18, 18], [15, 3], [1]], ![[7, 7], [7, 5], [17, 20], [1]]]
 h' := ![![[16, 22], [3, 4], [14, 15], [4, 16], [0, 1]], ![[0, 1], [21, 19], [1, 8], [7, 7], [16, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [19, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [19, 7, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2317, 5965, 9404, 45479, 88010]
  a := ![2, -3, -4, -20, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-77034, -124417, 9404, 45479, 88010]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-605, 381, -1486, 89, -510]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-605, 381, -1486, 89, -510]] 
 ![![23, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-605, 381, -1486, 89, -510], ![-688, -516, 1158, 3087, 12408], ![6234, 2399, -3663, -20811, -81282], ![-39660, -14577, 21248, 130242, 507732], ![21482, 7916, -11570, -70610, -275293]]]
  hmulB := by decide  
  f := ![![![573, -3149, -13824, 6261, 15486]], ![![378, -1072, -6004, 2709, 6720]], ![![387, -1938, -8745, 3944, 9768]], ![![221, -1632, -6582, 2887, 7194]], ![![218, -1070, -4874, 2232, 5507]]]
  g := ![![![912, 381, -1486, 89, -510], ![-6353, -516, 1158, 3087, 12408], ![39842, 2399, -3663, -20811, -81282], ![-248136, -14577, 21248, 130242, 507732], ![134562, 7916, -11570, -70610, -275293]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -2, 2, 16, 62]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-5, -2, 2, 16, 62]] 
 ![![23, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![-5, -2, 2, 16, 62], ![30, 11, -16, -98, -382], ![-186, -68, 99, 610, 2378], ![1158, 424, -616, -3799, -14806], ![-628, -230, 334, 2060, 8029]]]
  hmulB := by decide  
  f := ![![![-51, 154, -114, 48, 130]], ![![-34, 107, -72, 30, 82]], ![![-46, 132, -101, 42, 114]], ![![-4, 12, -12, 1, 6]], ![![-29, 88, -64, 28, 75]]]
  g := ![![![-37, -2, 2, 16, 62], ![232, 11, -16, -98, -382], ![-1444, -68, 99, 610, 2378], ![8990, 424, -616, -3799, -14806], ![-4875, -230, 334, 2060, 8029]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2

def I23N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 82, -861, 383, 964]] i)))

def SI23N3: IdealEqSpanCertificate' Table ![![157, 82, -861, 383, 964]] 
 ![![23, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![157, 82, -861, 383, 964], ![198, 540, 267, -134, -302], ![-34, 64, 440, -199, -494], ![-96, -233, -39, 21, 40], ![44, 79, -68, 29, 77]]]
  hmulB := by decide  
  f := ![![![16143, -6725, 29327, -13198, -33472]], ![![12326, -5135, 22393, -10077, -25556]], ![![14875, -6196, 27021, -12164, -30854]], ![![9059, -3779, 16472, -7392, -18718]], ![![5674, -2361, 10300, -4647, -11801]]]
  g := ![![![177, 82, -861, 383, 964], ![-477, 540, 267, -134, -302], ![-169, 64, 440, -199, -494], ![188, -233, -39, 21, 40], ![-41, 79, -68, 29, 77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N3 : Nat.card (O ⧸ I23N3) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N3)

lemma isPrimeI23N3 : Ideal.IsPrime I23N3 := prime_ideal_of_norm_prime hp23.out _ NI23N3
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![859, -336, 1495, -771, -2080]] ![![-605, 381, -1486, 89, -510]]
  ![![-5073397, -1139253, 541645, 14378992, 55024300]] where
 M := ![![![-5073397, -1139253, 541645, 14378992, 55024300]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-5073397, -1139253, 541645, 14378992, 55024300]] ![![-5, -2, 2, 16, 62]]
  ![![-18013944239, -6598113241, 9582361237, 59085143284, 230303424990]] where
 M := ![![![-18013944239, -6598113241, 9582361237, 59085143284, 230303424990]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N2 : IdealMulLeCertificate' Table 
  ![![-18013944239, -6598113241, 9582361237, 59085143284, 230303424990]] ![![157, 82, -861, 383, 964]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![760994997, 278730468, -404788684, -2496021732, -9729043102]]]
 hmul := by decide  
 g := ![![![![33086739, 12118716, -17599508, -108522684, -423001874]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2, I23N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
    exact isPrimeI23N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1 ⊙ MulI23N2)


lemma PB953I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB953I0 : PrimesBelowBoundCertificateInterval O 1 23 953 where
  m := 9
  g := ![5, 5, 5, 3, 2, 1, 2, 1, 4]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB953I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N1, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1, I23N2, I23N3]
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
    · exact ![49, 49, 7]
    · exact ![1331, 121]
    · exact ![371293]
    · exact ![83521, 17]
    · exact ![2476099]
    · exact ![529, 23, 23, 23]
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
      exact NI2N1
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
      exact NI3N1
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
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
      exact NI23N3
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I7N0, I7N1, I7N2, I11N1, I17N1, I23N0, I23N1, I23N2, I23N3]
  Il := ![[I2N0, I2N1, I2N1, I2N1, I2N2], [I3N0, I3N1, I3N1, I3N1, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N1], [], [I17N1], [], [I23N0, I23N1, I23N2, I23N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
