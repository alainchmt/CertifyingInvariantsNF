
import IdealArithmetic.Examples.NF5_3_125000000_3.RI5_3_125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -8, 9, 3, 23]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![2, -8, 9, 3, 23]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![4, 19, 1, 0, 0], ![20, 25, 0, 1, 0], ![6, 23, 0, 0, 1]] where
  M :=![![![2, -8, 9, 3, 23], ![20, 46, -61, -26, -140], ![64, -107, 90, 22, 264], ![254, 373, -551, -249, -1206], ![-63, -24, 59, 33, 106]]]
  hmulB := by decide  
  f := ![![![-24, 44, -17, -15, -65]], ![![100, -16, -41, -14, -100]], ![![60, -7, -23, -8, -56]], ![![66, 25, -54, -27, -154]], ![![77, -4, -38, -15, -98]]]
  g := ![![![-8, -27, 9, 3, 23], ![56, 175, -61, -26, -140], ![-80, -291, 90, 22, 264], ![506, 1545, -551, -249, -1206], ![-55, -152, 59, 33, 106]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [23, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 28], [0, 1]]
 g := ![![[1, 24], [9], [7, 24], [6, 1]], ![[0, 5], [9], [6, 5], [12, 28]]]
 h' := ![![[6, 28], [20, 16], [13, 3], [7, 13], [0, 1]], ![[0, 1], [0, 13], [2, 26], [27, 16], [6, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [3, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [23, 23, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-571394, -349868, 687125, 357215, 1337353]
  a := ![174, 136, -265, -119, -551]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-637528, -1830853, 687125, 357215, 1337353]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![429, 314, -132, -92, -402]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![429, 314, -132, -92, -402]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![16, 22, 1, 0, 0], ![27, 13, 0, 1, 0], ![2, 16, 0, 0, 1]] where
  M :=![![![429, 314, -132, -92, -402], ![600, 437, -184, -128, -560], ![832, 608, -251, -176, -768], ![276, 208, -84, -59, -264], ![-162, -120, 48, 34, 149]]]
  hmulB := by decide  
  f := ![![![-11, -10, 20, 8, 50]], ![![8, 57, -72, -32, -192]], ![![0, 30, -35, -16, -96]], ![![-9, 27, -24, -11, -66]], ![![4, 32, -40, -18, -107]]]
  g := ![![![201, 374, -132, -92, -402], ![280, 521, -184, -128, -560], ![384, 714, -251, -176, -768], ![129, 243, -84, -59, -264], ![-74, -138, 48, 34, 149]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 28], [0, 1]]
 g := ![![[20, 24], [24], [10, 1], [27, 1]], ![[1, 5], [24], [8, 28], [25, 28]]]
 h' := ![![[27, 28], [16, 13], [28, 13], [6, 1], [0, 1]], ![[0, 1], [19, 16], [2, 16], [4, 28], [27, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [22, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [3, 2, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-108402990, -72620674, 137441608, 70476181, 271392954]
  a := ![2553, 2006, -3890, -1701, -8084]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-163900397, -288097023, 137441608, 70476181, 271392954]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34, -16, -9, -1, -17]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![34, -16, -9, -1, -17]] 
 ![![29, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![34, -16, -9, -1, -17], ![-44, -24, 67, 34, 196], ![-32, 161, -172, -106, -552], ![190, -187, 71, 67, 290], ![-31, -46, 83, 45, 250]]]
  hmulB := by decide  
  f := ![![![648, 468, -199, -139, -601]], ![![412, 298, -128, -89, -385]], ![![72, 49, -25, -17, -69]], ![![302, 217, -111, -73, -310]], ![![433, 314, -129, -91, -396]]]
  g := ![![![23, -16, -9, -1, -17], ![-139, -24, 67, 34, 196], ![335, 161, -172, -106, -552], ![-114, -187, 71, 67, 290], ![-168, -46, 83, 45, 250]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![2, -8, 9, 3, 23]] ![![429, 314, -132, -92, -402]]
  ![![648, 468, -199, -139, -601]] where
 M := ![![![648, 468, -199, -139, -601]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![648, 468, -199, -139, -601]] ![![34, -16, -9, -1, -17]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-254, -205, 124, 79, 377]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-254, -205, 124, 79, 377]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![5, 21, 0, 22, 1]] where
  M :=![![![-254, -205, 124, 79, 377], ![-388, -123, 0, 4, -28], ![-208, -576, 217, 176, 752], ![-414, -102, 248, 119, 686], ![7, 203, -124, -87, -414]]]
  hmulB := by decide  
  f := ![![![-4, -23, 28, 11, 67]], ![![4, 83, -96, -36, -236]], ![![-80, -352, 439, 176, 1040]], ![![-34, 546, -600, -215, -1514]], ![![-21, 441, -488, -176, -1227]]]
  g := ![![![-69, -262, 4, -265, 377], ![-8, 15, 0, 20, -28], ![-128, -528, 7, -528, 752], ![-124, -468, 8, -483, 686], ![67, 287, -4, 291, -414]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [22, 19, 28, 9, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 25, 2, 12], [6, 30, 25, 15], [24, 6, 4, 4], [0, 1]]
 g := ![![[6, 4, 20, 25], [26, 27, 22, 18], [4, 22, 22, 1], []], ![[18, 12, 5, 15, 7, 6], [18, 5, 29, 17, 28, 27], [13, 22, 12, 20, 19, 15], [24, 6, 23, 16, 6, 23]], ![[22, 3, 19, 16, 28, 12], [13, 25, 0, 23, 10, 13], [23, 23, 6, 12, 15, 23], [4, 17, 1, 14, 16, 27]], ![[8, 18, 7, 25, 6, 14], [25, 25, 16, 5, 11, 4], [22, 5, 1, 13, 15, 8], [19, 8, 30, 5, 19, 2]]]
 h' := ![![[23, 25, 2, 12], [17, 22, 22, 26], [5, 29, 9, 24], [0, 0, 0, 1], [0, 1]], ![[6, 30, 25, 15], [29, 9, 20, 4], [6, 12, 18, 14], [14, 27, 26, 3], [23, 25, 2, 12]], ![[24, 6, 4, 4], [8, 9, 7, 10], [24, 2, 21, 25], [4, 0, 29, 4], [6, 30, 25, 15]], ![[0, 1], [20, 22, 13, 22], [4, 19, 14, 30], [14, 4, 7, 23], [24, 6, 4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [14, 20, 18], []]
 b := ![[], [], [16, 22, 25, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [22, 19, 28, 9, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5848861668385, -2889634422581, 6263477929495, 3361070391412, 11791723716867]
  a := ![157, 123, -239, -106, -497]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2090563879120, -8081155886348, 202047675145, -8259898431602, 11791723716867]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, -23, 28, 11, 67]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-4, -23, 28, 11, 67]] 
 ![![31, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-4, -23, 28, 11, 67], ![4, 83, -96, -36, -236], ![-80, -352, 439, 176, 1040], ![-34, 546, -600, -215, -1514], ![33, 31, -52, -25, -108]]]
  hmulB := by decide  
  f := ![![![-254, -205, 124, 79, 377]], ![![-160, -123, 72, 46, 218]], ![![-146, -131, 75, 49, 231]], ![![-210, -162, 104, 65, 314]], ![![-221, -172, 104, 66, 315]]]
  g := ![![![-69, -23, 28, 11, 67], ![238, 83, -96, -36, -236], ![-1081, -352, 439, 176, 1040], ![1496, 546, -600, -215, -1514], ![125, 31, -52, -25, -108]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-254, -205, 124, 79, 377]] ![![-4, -23, 28, 11, 67]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, -13, 20, 11, 41]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-22, -13, 20, 11, 41]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![2, 20, 10, 1, 0], ![26, 25, 33, 0, 1]] where
  M :=![![![-22, -13, 20, 11, 41], ![-100, -47, 96, 52, 180], ![-528, -272, 565, 304, 1072], ![-1454, -702, 1536, 827, 2886], ![415, 207, -444, -239, -838]]]
  hmulB := by decide  
  f := ![![![-4, 3, -4, -3, -15]], ![![12, -11, 0, 4, 12]], ![![-48, -16, 49, 16, 112]], ![![-6, -8, 10, 5, 28]], ![![-37, -20, 41, 15, 98]]]
  g := ![![![-30, -34, -39, 11, 41], ![-132, -151, -172, 52, 180], ![-784, -896, -1023, 304, 1072], ![-2112, -2416, -2756, 827, 2886], ![613, 701, 800, -239, -838]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [36, 2, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 22, 5], [24, 14, 32], [0, 1]]
 g := ![![[24, 5, 36], [7, 12], [23, 35, 27], [11, 1], []], ![[0, 15, 33, 24], [35, 28], [2, 31, 8, 23], [5, 11], [14, 25]], ![[14, 16, 35, 17], [33, 10], [20, 34, 16, 22], [25, 3], [24, 25]]]
 h' := ![![[24, 22, 5], [18, 26, 6], [23, 36, 7], [11, 16, 8], [0, 0, 1], [0, 1]], ![[24, 14, 32], [1, 8, 29], [22, 23, 19], [9, 7, 7], [35, 17, 14], [24, 22, 5]], ![[0, 1], [24, 3, 2], [18, 15, 11], [15, 14, 22], [8, 20, 22], [24, 14, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 27], []]
 b := ![[], [17, 14, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [36, 2, 26, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-367048303164, -192359103780, 405543655904, 215495240408, 771022435532]
  a := ![-995, -783, 1516, 663, 3151]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-563368165076, -642643913520, -734949976236, 215495240408, 771022435532]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 3, -4, -3, -15]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-4, 3, -4, -3, -15]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![3, 17, 1, 0, 0], ![30, 24, 0, 1, 0], ![28, 25, 0, 0, 1]] where
  M :=![![![-4, 3, -4, -3, -15], ![12, -11, 0, 4, 12], ![-48, -16, 49, 16, 112], ![26, 78, -112, -49, -294], ![19, -15, 4, 5, 20]]]
  hmulB := by decide  
  f := ![![![-22, -13, 20, 11, 41]], ![![-100, -47, 96, 52, 180]], ![![-62, -30, 61, 33, 115]], ![![-122, -60, 120, 65, 228]], ![![-73, -36, 68, 37, 130]]]
  g := ![![![14, 14, -4, -3, -15], ![-12, -11, 0, 4, 12], ![-103, -109, 49, 16, 112], ![272, 284, -112, -49, -294], ![-19, -19, 4, 5, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [14, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 36], [0, 1]]
 g := ![![[1, 26], [11], [17, 34], [11], [1]], ![[7, 11], [11], [22, 3], [11], [1]]]
 h' := ![![[23, 36], [28, 27], [21, 14], [5, 16], [23, 23], [0, 1]], ![[0, 1], [20, 10], [10, 23], [3, 21], [34, 14], [23, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [11, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [14, 14, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-678135, -513964, 926309, 466969, 1863746]
  a := ![221, 177, -336, -143, -700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1882460, -2001679, 926309, 466969, 1863746]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-22, -13, 20, 11, 41]] ![![-4, 3, -4, -3, -15]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![120, 90, -39, -27, -119]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![120, 90, -39, -27, -119]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![36, 3, 1, 0, 0], ![28, 14, 0, 1, 0], ![37, 13, 0, 0, 1]] where
  M :=![![![120, 90, -39, -27, -119], ![172, 118, -49, -34, -148], ![224, 177, -70, -50, -216], ![82, 61, -31, -21, -98], ![-41, -38, 15, 11, 48]]]
  hmulB := by decide  
  f := ![![![-2, 6, -5, -1, -11]], ![![-20, -32, 47, 18, 100]], ![![-4, 5, -3, 0, -8]], ![![-14, -15, 25, 11, 54]], ![![-7, -4, 9, 4, 19]]]
  g := ![![![163, 52, -39, -27, -119], ![204, 65, -49, -34, -148], ![296, 95, -70, -50, -216], ![132, 42, -31, -21, -98], ![-65, -21, 15, 11, 48]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [24, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 40], [0, 1]]
 g := ![![[40, 39], [10], [20], [3, 2], [1]], ![[33, 2], [10], [20], [10, 39], [1]]]
 h' := ![![[24, 40], [4, 11], [30, 16], [10, 26], [17, 24], [0, 1]], ![[0, 1], [22, 30], [4, 25], [19, 15], [19, 17], [24, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [39, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [24, 17, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-165104, -323166, 449044, 199986, 1015132]
  a := ![-168, -142, 256, 94, 532]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1450980, -430898, 449044, 199986, 1015132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![978, 712, -295, -207, -903]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![978, 712, -295, -207, -903]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![6, 16, 1, 0, 0], ![34, 19, 0, 1, 0], ![13, 24, 0, 0, 1]] where
  M :=![![![978, 712, -295, -207, -903], ![1356, 1004, -419, -290, -1284], ![1824, 1311, -448, -342, -1496], ![434, 443, -55, -47, -386], ![-313, -242, 45, 43, 218]]]
  hmulB := by decide  
  f := ![![![-140, 644, -677, -417, -2171]], ![![1324, -1578, 829, 658, 3044]], ![![408, -477, 244, 196, 902]], ![![542, -151, -272, -91, -672]], ![![771, -758, 284, 266, 1149]]]
  g := ![![![525, 757, -295, -207, -903], ![742, 1074, -419, -290, -1284], ![868, 1241, -448, -342, -1496], ![180, 280, -55, -47, -386], ![-119, -171, 45, 43, 218]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [34, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 40], [0, 1]]
 g := ![![[39, 5], [10], [37], [12, 32], [1]], ![[10, 36], [10], [37], [15, 9], [1]]]
 h' := ![![[27, 40], [31, 13], [17, 25], [2, 23], [7, 27], [0, 1]], ![[0, 1], [13, 28], [36, 16], [8, 18], [39, 14], [27, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [23, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [34, 14, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-87134, -48356, 100095, 52800, 193190]
  a := ![-23, -11, 37, 27, 75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-121814, -177796, 100095, 52800, 193190]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52, -24, 3, 3, 7]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-52, -24, 3, 3, 7]] 
 ![![41, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![-52, -24, 3, 3, 7], ![-44, -78, 35, 26, 116], ![-160, -39, 46, 22, 120], ![-2, 13, -61, -31, -182], ![49, -14, 3, 5, 20]]]
  hmulB := by decide  
  f := ![![![-2, -308, 349, 129, 867]], ![![8, -132, 145, 52, 366]], ![![16, -163, 176, 62, 448]], ![![110, 73, -139, -71, -274]], ![![-25, -194, 232, 90, 561]]]
  g := ![![![5, -24, 3, 3, 7], ![-52, -78, 35, 26, 116], ![-78, -39, 46, 22, 120], ![134, 13, -61, -31, -182], ![-7, -14, 3, 5, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![120, 90, -39, -27, -119]] ![![978, 712, -295, -207, -903]]
  ![![193793, 141508, -59508, -41450, -181096]] where
 M := ![![![193793, 141508, -59508, -41450, -181096]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![193793, 141508, -59508, -41450, -181096]] ![![-52, -24, 3, 3, 7]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-15573112, -11371350, 4781953, 3330881, 14552499]]]
 hmul := by decide  
 g := ![![![![-379832, -277350, 116633, 81241, 354939]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![606, 445, -184, -129, -561]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![606, 445, -184, -129, -561]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![18, 29, 29, 1, 0], ![41, 14, 6, 0, 1]] where
  M :=![![![606, 445, -184, -129, -561], ![852, 629, -272, -188, -828], ![1200, 840, -343, -240, -1040], ![374, 314, -124, -89, -386], ![-235, -161, 60, 43, 182]]]
  hmulB := by decide  
  f := ![![![-4, -5, 8, 3, 17]], ![![-4, 15, -16, -4, -44]], ![![-80, -120, 179, 80, 400]], ![![-62, -71, 113, 53, 244]], ![![-15, -16, 26, 12, 55]]]
  g := ![![![603, 280, 161, -129, -561], ![888, 411, 236, -188, -828], ![1120, 520, 299, -240, -1040], ![414, 193, 111, -89, -386], ![-197, -92, -53, 43, 182]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [36, 2, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 28, 39], [9, 14, 4], [0, 1]]
 g := ![![[36, 18, 25], [15, 26, 17], [40, 11], [7, 3, 1], []], ![[1, 16, 38, 18], [8, 35, 31, 26], [35, 11], [38, 24, 23, 33], [39, 16]], ![[0, 37, 38, 10], [21, 27, 31, 24], [21, 1], [38, 30, 11, 40], [31, 16]]]
 h' := ![![[37, 28, 39], [19, 33, 5], [15, 38, 24], [6, 7, 22], [0, 0, 1], [0, 1]], ![[9, 14, 4], [33, 16, 24], [22, 8, 12], [11, 2, 22], [8, 42, 14], [37, 28, 39]], ![[0, 1], [0, 37, 14], [27, 40, 7], [3, 34, 42], [40, 1, 28], [9, 14, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 19], []]
 b := ![[], [19, 21, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [36, 2, 40, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![104555080, 52342512, -112748948, -60366552, -212750604]
  a := ![59, 45, -90, -41, -187]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![230556460, 111197232, 67776388, -60366552, -212750604]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-321, -233, 97, 68, 296]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-321, -233, 97, 68, 296]] 
 ![![43, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-321, -233, 97, 68, 296], ![-448, -332, 143, 98, 432], ![-624, -439, 172, 126, 536], ![-216, -185, 101, 59, 284], ![124, 89, -37, -26, -113]]]
  hmulB := by decide  
  f := ![![![-59, -27, 69, 36, 160]], ![![-45, -19, 50, 26, 112]], ![![-51, -30, 63, 34, 136]], ![![-99, -44, 104, 55, 204]], ![![15, 10, -18, -10, -33]]]
  g := ![![![55, -233, 97, 68, 296], ![75, -332, 143, 98, 432], ![111, -439, 172, 126, 536], ![27, -185, 101, 59, 284], ![-21, 89, -37, -26, -113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, -24, 12, 8, 34]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-33, -24, 12, 8, 34]] 
 ![![43, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-33, -24, 12, 8, 34], ![-56, -37, 26, 16, 64], ![-128, -78, 91, 52, 192], ![-212, -110, 212, 115, 408], ![66, 36, -62, -34, -121]]]
  hmulB := by decide  
  f := ![![![41, 216, -272, -108, -670]], ![![38, 191, -242, -96, -596]], ![![46, 286, -353, -140, -868]], ![![-12, -130, 152, 59, 368]], ![![5, 20, -26, -10, -63]]]
  g := ![![![7, -24, 12, 8, 34], ![2, -37, 26, 16, 64], ![-38, -78, 91, 52, 192], ![-152, -110, 212, 115, 408], ![41, 36, -62, -34, -121]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![606, 445, -184, -129, -561]] ![![-321, -233, 97, 68, 296]]
  ![![-320770, -234226, 98497, 68609, 299749]] where
 M := ![![![-320770, -234226, 98497, 68609, 299749]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-320770, -234226, 98497, 68609, 299749]] ![![-33, -24, 12, 8, 34]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![16332776, 11926050, -5015219, -3493363, -15262377]]]
 hmul := by decide  
 g := ![![![![379832, 277350, -116633, -81241, -354939]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [15, 1, 21, 37, 24, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 35, 29, 10, 16], [8, 33, 36, 12, 13], [20, 10, 3, 46, 43], [4, 15, 26, 26, 22], [0, 1]]
 g := ![![[10, 19, 33, 8, 2], [25, 44, 15, 29, 9], [3, 8, 14, 31, 12], [1], []], ![[14, 8, 25, 8, 30, 31, 31, 9], [5, 34, 37, 2, 12, 17, 3, 16], [3, 10, 18, 15, 24, 5, 46, 32], [13, 44, 11, 29, 6, 45, 45, 7], [23, 14, 4, 21]], ![[45, 29, 27, 39, 25, 10, 32, 23], [23, 38, 16, 37, 43, 2, 29, 46], [10, 27, 26, 43, 18, 31, 32, 15], [29, 8, 10, 19, 6, 22, 10, 19], [7, 36, 16, 28]], ![[14, 3, 11, 23, 36, 4, 10, 41], [39, 43, 31, 31, 20, 15, 46, 30], [10, 15, 22, 32, 33, 2, 41, 23], [25, 32, 3, 42, 39, 10, 20, 19], [3, 43, 0, 16]], ![[19, 37, 23, 41, 35, 24, 39, 23], [28, 20, 19, 13, 11, 46, 26, 46], [19, 27, 32, 6, 31, 23, 9, 13], [44, 10, 40, 7, 26, 29, 43, 29], [43, 5, 9, 14]]]
 h' := ![![[38, 35, 29, 10, 16], [1, 24, 37, 4, 7], [2, 8, 31, 14, 44], [32, 46, 26, 10, 23], [0, 0, 1], [0, 1]], ![[8, 33, 36, 12, 13], [34, 14, 24, 1, 36], [25, 9, 33, 25, 1], [38, 7, 5, 38, 40], [18, 30, 5, 10, 31], [38, 35, 29, 10, 16]], ![[20, 10, 3, 46, 43], [9, 40, 39, 29, 3], [44, 40, 33, 17, 26], [41, 14, 22, 1, 24], [6, 28, 20, 36, 9], [8, 33, 36, 12, 13]], ![[4, 15, 26, 26, 22], [10, 28, 22, 18, 5], [26, 26, 41, 2, 4], [32, 20, 46, 21, 37], [26, 34, 20, 35, 30], [20, 10, 3, 46, 43]], ![[0, 1], [6, 35, 19, 42, 43], [6, 11, 3, 36, 19], [25, 7, 42, 24, 17], [29, 2, 1, 13, 24], [4, 15, 26, 26, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 34, 21, 43], [], [], []]
 b := ![[], [42, 19, 3, 6, 12], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [15, 1, 21, 37, 24, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-532468690318429501, -261184831266288547, 568087779133540971, 305200888115694212, 1068208701119000166]
  a := ![-303, -239, 463, 203, 960]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11329121070604883, -5557124069495501, 12086974024117893, 6493635917355196, 22727844704659578]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 229345007 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -10, 15, 15, 69]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-2, -10, 15, 15, 69]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![33, 6, 44, 44, 1]] where
  M :=![![![-2, -10, 15, 15, 69], ![-84, 4, 47, -6, 36], ![288, 221, -464, -146, -1032], ![-270, -767, 1071, 435, 2690], ![-97, 98, -41, -41, -178]]]
  hmulB := by decide  
  f := ![![![-8, -6, 1, 1, 5]], ![![-4, -6, -5, -2, -4]], ![![32, 13, -50, -26, -88]], ![![138, 65, -151, -81, -282]], ![![135, 60, -166, -88, -303]]]
  g := ![![![-43, -8, -57, -57, 69], ![-24, -4, -29, -30, 36], ![648, 121, 848, 854, -1032], ![-1680, -319, -2213, -2225, 2690], ![109, 22, 147, 147, -178]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [24, 39, 26, 47, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 33, 47, 7], [7, 12, 10, 33], [48, 7, 49, 13], [0, 1]]
 g := ![![[44, 43, 27, 16], [19, 43, 38], [48, 52, 4, 46], [10, 6, 1], []], ![[18, 31, 42, 51, 4, 37], [50, 8, 13], [19, 9, 13, 24, 11, 6], [35, 43, 49], [30, 27, 41, 35, 10, 25]], ![[36, 10, 35, 48, 25, 35], [14, 27, 13], [33, 20, 12, 9, 7, 41], [24, 27, 13], [0, 4, 6, 29, 40, 3]], ![[12, 15, 23, 16, 16, 47], [26, 49, 38], [44, 19, 24, 12, 28, 4], [52, 9, 17], [17, 1, 21, 36, 24, 24]]]
 h' := ![![[4, 33, 47, 7], [5, 23, 2, 49], [14, 49, 32, 41], [25, 49, 12, 24], [0, 0, 0, 1], [0, 1]], ![[7, 12, 10, 33], [32, 24, 24, 9], [38, 2, 20, 38], [37, 20, 47, 49], [33, 31, 52, 46], [4, 33, 47, 7]], ![[48, 7, 49, 13], [10, 46, 47, 12], [9, 10, 46, 15], [49, 37, 46, 19], [25, 25, 7, 38], [7, 12, 10, 33]], ![[0, 1], [18, 13, 33, 36], [18, 45, 8, 12], [33, 0, 1, 14], [50, 50, 47, 21], [48, 7, 49, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [39, 25, 15], []]
 b := ![[], [], [33, 1, 17, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [24, 39, 26, 47, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5106680827183, -2564797207477, 5515984902314, 2952004777185, 10413030233697]
  a := ![-167, -133, 254, 109, 529]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6579937330928, -1227226011503, -8540704629818, -8589081613311, 10413030233697]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 6, -1, -1, -5]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![8, 6, -1, -1, -5]] 
 ![![53, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![8, 6, -1, -1, -5], ![4, 6, 5, 2, 4], ![-32, -13, 50, 26, 88], ![-138, -65, 151, 81, 282], ![37, 18, -43, -23, -80]]]
  hmulB := by decide  
  f := ![![![2, 10, -15, -15, -69]], ![![2, 2, -4, -3, -15]], ![![-4, 3, -2, -8, -30]], ![![6, 19, -27, -15, -82]], ![![3, 4, -8, -8, -37]]]
  g := ![![![3, 6, -1, -1, -5], ![-8, 6, 5, 2, 4], ![-97, -13, 50, 26, 88], ![-299, -65, 151, 81, 282], ![85, 18, -43, -23, -80]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-2, -10, 15, 15, 69]] ![![8, 6, -1, -1, -5]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18641, 13614, -5722, -3986, -17418]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![18641, 13614, -5722, -3986, -17418]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![32, 42, 9, 57, 1]] where
  M :=![![![18641, 13614, -5722, -3986, -17418], ![25992, 18981, -7956, -5548, -24248], ![36160, 26456, -11011, -7688, -33680], ![11900, 8760, -3298, -2381, -10580], ![-7054, -5180, 2076, 1466, 6465]]]
  hmulB := by decide  
  f := ![![![-41, 46, -22, -18, -82]], ![![104, -49, -28, -4, -56]], ![![-128, -72, 199, 104, 592]], ![![-116, 256, -222, -151, -756]], ![![-78, 226, -217, -143, -727]]]
  g := ![![![9763, 12630, 2560, 16760, -17418], ![13592, 17583, 3564, 23332, -24248], ![18880, 24424, 4951, 32408, -33680], ![5940, 7680, 1558, 10181, -10580], ![-3626, -4690, -951, -6221, 6465]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [56, 0, 16, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 36, 34, 34], [15, 55, 23, 18], [32, 26, 2, 7], [0, 1]]
 g := ![![[3, 45, 28, 4], [44, 38, 50, 19], [13, 40, 27], [10, 52, 56, 1], []], ![[7, 11, 18, 33, 57, 32], [16, 28, 37, 18, 38, 6], [45, 25, 17], [14, 32, 37, 29, 7, 23], [45, 8, 43, 51, 0, 10]], ![[35, 50, 39, 1, 58, 39], [15, 47, 9, 14, 21, 23], [11, 14, 15], [19, 44, 31, 1, 17, 2], [17, 4, 11, 35, 22, 50]], ![[35, 35, 2, 3, 6, 25], [39, 2, 27, 50, 53, 45], [0, 26, 21], [23, 11, 39, 22, 17, 9], [37, 22, 31, 33, 32, 48]]]
 h' := ![![[9, 36, 34, 34], [14, 21, 49, 57], [54, 40, 27, 14], [30, 38, 8, 26], [0, 0, 0, 1], [0, 1]], ![[15, 55, 23, 18], [14, 25, 22, 17], [18, 23, 35, 32], [58, 26, 45, 31], [38, 40, 6, 13], [9, 36, 34, 34]], ![[32, 26, 2, 7], [48, 15, 29, 22], [37, 50, 50, 36], [2, 2, 0, 29], [4, 26, 17, 20], [15, 55, 23, 18]], ![[0, 1], [31, 57, 18, 22], [1, 5, 6, 36], [1, 52, 6, 32], [16, 52, 36, 25], [32, 26, 2, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [33, 25, 8], []]
 b := ![[], [], [46, 40, 39, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [56, 0, 16, 3, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41001967272, -20058989339, 43684663629, 23479412960, 82106443292]
  a := ![-32, -23, 49, 25, 102]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-45227256824, -58788637417, -11784293661, -78925217876, 82106443292]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 46, -22, -18, -82]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-41, 46, -22, -18, -82]] 
 ![![59, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![-41, 46, -22, -18, -82], ![104, -49, -28, -4, -56], ![-128, -72, 199, 104, 592], ![-116, 256, -222, -151, -756], ![106, -24, -60, -22, -153]]]
  hmulB := by decide  
  f := ![![![18641, 13614, -5722, -3986, -17418]], ![![16238, 11859, -4984, -3472, -15172]], ![![12303, 8986, -3775, -2630, -11494]], ![![16947, 12378, -5196, -3621, -15826]], ![![15046, 10988, -4620, -3218, -14061]]]
  g := ![![![57, 46, -22, -18, -82], ![110, -49, -28, -4, -56], ![-641, -72, 199, 104, 592], ![671, 256, -222, -151, -756], ![204, -24, -60, -22, -153]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![18641, 13614, -5722, -3986, -17418]] ![![-41, 46, -22, -18, -82]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 24, -22, -10, -56]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![15, 24, -22, -10, -56]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![2, 59, 36, 1, 0], ![7, 13, 31, 0, 1]] where
  M :=![![![15, 24, -22, -10, -56], ![16, -41, 56, 20, 136], ![64, 236, -273, -112, -656], ![24, -332, 370, 133, 924], ![-20, -24, 32, 16, 71]]]
  hmulB := by decide  
  f := ![![![3, -8, 10, 6, 32]], ![![-16, 27, -16, -12, -56]], ![![64, -28, -13, 0, -16]], ![![22, 9, -22, -11, -60]], ![![29, -9, -9, -2, -17]]]
  g := ![![![7, 22, 34, -10, -56], ![-16, -49, -80, 20, 136], ![80, 252, 395, -112, -656], ![-110, -331, -542, 133, 924], ![-9, -31, -45, 16, 71]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [51, 10, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 46, 12], [4, 14, 49], [0, 1]]
 g := ![![[6, 17, 36], [19, 48], [22, 36, 60], [32, 28, 9], [1]], ![[4, 19, 9, 39], [23, 20], [28, 37, 47, 42], [43, 7, 2, 52], [11, 42, 46, 20]], ![[43, 40, 55, 49], [48, 34], [22, 0, 43, 58], [1, 54, 55, 27], [15, 26, 10, 41]]]
 h' := ![![[60, 46, 12], [34, 33, 55], [37, 60, 32], [15, 60, 11], [10, 51, 3], [0, 1]], ![[4, 14, 49], [6, 7, 7], [52, 42, 9], [17, 30, 20], [48, 21, 44], [60, 46, 12]], ![[0, 1], [44, 21, 60], [33, 20, 20], [11, 32, 30], [31, 50, 14], [4, 14, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 24], []]
 b := ![[], [53, 17, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [51, 10, 58, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![149624601232, 75144871899, -161617141390, -86490283539, -305105473178]
  a := ![649, 505, -992, -453, -2054]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![40300712796, 149908897574, 203447585812, -86490283539, -305105473178]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -14, 16, 6, 38]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-1, -14, 16, 6, 38]] 
 ![![61, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![-1, -14, 16, 6, 38], ![8, 53, -64, -24, -152], ![-32, -208, 253, 96, 608], ![60, 388, -472, -183, -1140], ![2, 6, -8, -2, -17]]]
  hmulB := by decide  
  f := ![![![-1073, -794, 336, 234, 1026]], ![![-359, -265, 112, 78, 342]], ![![-121, -90, 37, 26, 114]], ![![-80, -60, 24, 17, 76]], ![![-944, -698, 296, 206, 903]]]
  g := ![![![-31, -14, 16, 6, 38], ![125, 53, -64, -24, -152], ![-501, -208, 253, 96, 608], ![940, 388, -472, -183, -1140], ![14, 6, -8, -2, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-376, -276, 117, 81, 355]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-376, -276, 117, 81, 355]] 
 ![![61, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-376, -276, 117, 81, 355], ![-524, -378, 155, 110, 476], ![-736, -555, 250, 166, 744], ![-242, -143, 29, 35, 118], ![145, 106, -45, -31, -136]]]
  hmulB := by decide  
  f := ![![![-70, -88, 131, 75, 291]], ![![-46, -48, 76, 43, 165]], ![![-66, -47, 85, 47, 169]], ![![-208, -155, 278, 154, 569]], ![![37, 18, -39, -21, -72]]]
  g := ![![![18, -276, 117, 81, 355], ![27, -378, 155, 110, 476], ![29, -555, 250, 166, 744], ![25, -143, 29, 35, 118], ![-7, 106, -45, -31, -136]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![15, 24, -22, -10, -56]] ![![-1, -14, 16, 6, 38]]
  ![![169, 1422, -1694, -656, -4102]] where
 M := ![![![169, 1422, -1694, -656, -4102]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![169, 1422, -1694, -656, -4102]] ![![-376, -276, 117, 81, 355]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![2074, 15006, -17751, -6893, -43005]]]
 hmul := by decide  
 g := ![![![![34, 246, -291, -113, -705]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)


lemma PB547I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB547I1 : PrimesBelowBoundCertificateInterval O 23 61 547 where
  m := 9
  g := ![3, 2, 2, 3, 3, 1, 2, 2, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB547I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![841, 841, 29]
    · exact ![923521, 31]
    · exact ![50653, 1369]
    · exact ![1681, 1681, 41]
    · exact ![79507, 43, 43]
    · exact ![229345007]
    · exact ![7890481, 53]
    · exact ![12117361, 59]
    · exact ![226981, 61, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I29N2, I31N1, I41N2, I43N1, I43N2, I53N1, I59N1, I61N1, I61N2]
  Il := ![[I29N2], [I31N1], [], [I41N2], [I43N1, I43N2], [], [I53N1], [I59N1], [I61N1, I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
