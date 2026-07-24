
import IdealArithmetic.Examples.NF5_1_25312500_2.RI5_1_25312500_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![244, -145, -157, 127, -21]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![244, -145, -157, 127, -21]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![244, -145, -157, 127, -21], ![180, 87, -301, -187, 275], ![-1709, 609, 1488, -301, -462], ![2017, -1185, -1311, 1030, -153], ![-416, 1112, -558, -1468, 1331]]]
  hmulB := by decide  
  f := ![![![1953, -1011, 52, -50, 252]], ![![-1259, 722, -29, 27, -176]], ![![2485, -1310, 73, -54, 329]], ![![-393, 252, 6, 19, -54]], ![![479, -263, 30, 6, 73]]]
  g := ![![![137, -145, -157, 127, -21], ![334, 87, -301, -187, 275], ![-1448, 609, 1488, -301, -462], ![1149, -1185, -1311, 1030, -153], ![805, 1112, -558, -1468, 1331]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 2, -4, -1, -1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![8, 2, -4, -1, -1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![8, 2, -4, -1, -1], ![5, 13, 0, -9, -1], ![-2, 6, 9, 0, -8], ![42, -2, -24, 5, 0], ![-32, 36, 24, -28, 5]]]
  hmulB := by decide  
  f := ![![![14367, -7772, 380, -325, 1927]], ![![-2424, 1311, -64, 55, -325]], ![![11228, -6074, 297, -254, 1506]], ![![-10290, 5566, -272, 233, -1380]], ![![3630, -1964, 96, -82, 487]]]
  g := ![![![3, 2, -4, -1, -1], ![-4, 13, 0, -9, -1], ![-4, 6, 9, 0, -8], ![22, -2, -24, 5, 0], ![-34, 36, 24, -28, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![212, -29, -229, -30, 127]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![212, -29, -229, -30, 127]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![212, -29, -229, -30, 127], ![-1529, 696, 1187, -488, -187], ![2049, -1301, -1239, 1187, -301], ![1633, -189, -1797, -281, 1030], ![-7876, 3248, 6436, -2026, -1468]]]
  hmulB := by decide  
  f := ![![![-11374, 6184, -302, 252, -1533]], ![![1953, -1011, 52, -50, 252]], ![![-14586, 7917, -383, 329, -1961]], ![![2485, -1310, 73, -54, 329]], ![![-2878, 1562, -67, 73, -383]]]
  g := ![![![250, -29, -229, -30, 127], ![-1462, 696, 1187, -488, -187], ![1701, -1301, -1239, 1187, -301], ![1950, -189, -1797, -281, 1030], ![-7767, 3248, 6436, -2026, -1468]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![244, -145, -157, 127, -21]] ![![8, 2, -4, -1, -1]]
  ![![7547, -3349, -5941, 2284, 1052]] where
 M := ![![![7547, -3349, -5941, 2284, 1052]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![7547, -3349, -5941, 2284, 1052]] ![![212, -29, -229, -30, 127]]
  ![![-10008304, 8164694, 4323697, -8417221, 4181157]] where
 M := ![![![-10008304, 8164694, 4323697, -8417221, 4181157]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-10008304, 8164694, 4323697, -8417221, 4181157]] ![![212, -29, -229, -30, 127]]
  ![![-52422436846, 15518990748, 48662005400, -4657678194, -18906961289]] where
 M := ![![![-52422436846, 15518990748, 48662005400, -4657678194, -18906961289]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-52422436846, 15518990748, 48662005400, -4657678194, -18906961289]] ![![212, -29, -229, -30, 127]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![206171594220918, -111517309884264, -143181799776376, 91375517174184, -1248953742286]]]
 hmul := by decide  
 g := ![![![![103085797110459, -55758654942132, -71590899888188, 45687758587092, -624476871143]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N2, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 4, 0, 0, -1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-7, 4, 0, 0, -1]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-7, 4, 0, 0, -1], ![10, -5, 0, 0, 1], ![-10, 6, -1, 0, -1], ![8, -4, 2, -1, 1], ![0, 0, -2, 2, -1]]]
  hmulB := by decide  
  f := ![![![-1, 0, 2, 2, 1]], ![![-2, -1, 2, 2, 1]], ![![-2, -2, 1, 2, 1]], ![![-6, -4, 4, 5, 3]], ![![-7, -4, 4, 4, 2]]]
  g := ![![![-2, 4, 0, 0, -1], ![3, -5, 0, 0, 1], ![-3, 6, -1, 0, -1], ![3, -4, 2, -1, 1], ![-1, 0, -2, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-7, 4, 0, 0, -1]] ![![-7, 4, 0, 0, -1]]
  ![![89, -48, 2, -2, 12]] where
 M := ![![![89, -48, 2, -2, 12]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![89, -48, 2, -2, 12]] ![![-7, 4, 0, 0, -1]]
  ![![-1139, 616, -30, 26, -153]] where
 M := ![![![-1139, 616, -30, 26, -153]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-1139, 616, -30, 26, -153]] ![![-7, 4, 0, 0, -1]]
  ![![14641, -7920, 388, -332, 1964]] where
 M := ![![![14641, -7920, 388, -332, 1964]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N3 : IdealMulLeCertificate' Table 
  ![![14641, -7920, 388, -332, 1964]] ![![-7, 4, 0, 0, -1]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-188223, 101820, -4980, 4260, -25245]]]
 hmul := by decide  
 g := ![![![![-62741, 33940, -1660, 1420, -8415]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 4, 2, -4, 2]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-5, 4, 2, -4, 2]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-5, 4, 2, -4, 2], ![-22, 5, 22, 0, -10], ![72, -32, -57, 22, 10], ![-40, 32, 18, -33, 16], ![-76, 4, 88, 20, -55]]]
  hmulB := by decide  
  f := ![![![31, 28, -26, -32, -18]], ![![43, 33, -28, -36, -20]], ![![44, 40, -29, -38, -22]], ![![65, 52, -32, -45, -26]], ![![47, 40, -18, -28, -17]]]
  g := ![![![-3, 4, 2, -4, 2], ![-23, 5, 22, 0, -10], ![64, -32, -57, 22, 10], ![-25, 32, 18, -33, 16], ![-89, 4, 88, 20, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-5, 4, 2, -4, 2]] ![![-5, 4, 2, -4, 2]]
  ![![89, -184, 68, 236, -204]] where
 M := ![![![89, -184, 68, 236, -204]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![89, -184, 68, 236, -204]] ![![-5, 4, 2, -4, 2]]
  ![![14563, 3996, -21450, -10728, 17694]] where
 M := ![![![14563, 3996, -21450, -10728, 17694]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![14563, 3996, -21450, -10728, 17694]] ![![-5, 4, 2, -4, 2]]
  ![![-2620751, 492112, 2703656, 177752, -1370152]] where
 M := ![![![-2620751, 492112, 2703656, 177752, -1370152]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-2620751, 492112, 2703656, 177752, -1370152]] ![![-5, 4, 2, -4, 2]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![293961995, -94331980, -265897270, 36694580, 95076330]]]
 hmul := by decide  
 g := ![![![![58792399, -18866396, -53179454, 7338916, 19015266]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![289, -154, -204, 124, 3]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![289, -154, -204, 124, 3]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![3, 6, 6, 1, 0], ![5, 4, 6, 0, 1]] where
  M :=![![![289, -154, -204, 124, 3], ![-110, 221, -80, -284, 245], ![-1352, 372, 1281, -80, -529], ![2370, -1246, -1682, 997, 41], ![-1932, 1756, 662, -1886, 1077]]]
  hmulB := by decide  
  f := ![![![-51021, 27598, -1350, 1154, -6843]], ![![68234, -36913, 1802, -1546, 9151]], ![![-79744, 43140, -2111, 1802, -10697]], ![![-21291, 11518, -568, 477, -2858]], ![![-69487, 37590, -1842, 1568, -9322]]]
  g := ![![![-14, -130, -138, 124, 3], ![-69, 135, 22, -284, 245], ![219, 424, 705, -80, -529], ![-118, -1056, -1130, 997, 41], ![-237, 1252, 788, -1886, 1077]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [2, 3, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 2], [4, 4], [0, 1]]
 g := ![![[4, 2, 2], [1]], ![[4, 3, 1], [1]], ![[2, 2, 4], [1]]]
 h' := ![![[6, 2], [5, 4, 3], [0, 1]], ![[4, 4], [4, 3, 5], [6, 2]], ![[0, 1], [6, 0, 6], [4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [2, 3, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [2, 3, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4408212, 5201066, 2156060, -4893568, 1946907]
  a := ![-16, 11, 7, -17, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![76851, 3824978, 2833718, -4893568, 1946907]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51021, -27598, 1350, -1154, 6843]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![51021, -27598, 1350, -1154, 6843]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![6, 5, 1, 0, 0], ![5, 0, 0, 1, 0], ![5, 2, 0, 0, 1]] where
  M :=![![![51021, -27598, 1350, -1154, 6843], ![-68234, 36913, -1802, 1546, -9151], ![79744, -43140, 2111, -1802, 10697], ![-73086, 39530, -1928, 1659, -9799], ![25776, -13952, 686, -578, 3461]]]
  hmulB := by decide  
  f := ![![![-289, 154, 204, -124, -3]], ![![110, -221, 80, 284, -245]], ![![24, -79, 49, 108, -102]], ![![-545, 288, 386, -231, -8]], ![![101, -204, 74, 262, -226]]]
  g := ![![![2068, -6862, 1350, -1154, 6843], ![-2771, 9175, -1802, 1546, -9151], ![3229, -10727, 2111, -1802, 10697], ![-2974, 9824, -1928, 1659, -9799], ![1035, -3472, 686, -578, 3461]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 6], [0, 1]]
 g := ![![[6, 4], [6, 1]], ![[2, 3], [5, 6]]]
 h' := ![![[6, 6], [6, 2], [0, 1]], ![[0, 1], [4, 5], [6, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [4, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [6, 1, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2506494, 561432, 1802506, -347748, -109437]
  a := ![-121, 61, 62, -122, -243]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1576515, -1176032, 1802506, -347748, -109437]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![289, -154, -204, 124, 3]] ![![51021, -27598, 1350, -1154, 6843]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-520343, 281482, -13760, 11774, -69790]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-520343, 281482, -13760, 11774, -69790]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![2, 2, 5, 1, 0], ![3, 10, 5, 0, 1]] where
  M :=![![![-520343, 281482, -13760, 11774, -69790], ![695914, -376455, 18404, -15746, 93338], ![-813318, 439966, -21507, 18404, -109084], ![745338, -403194, 19712, -16863, 99968], ![-262956, 142244, -6952, 5952, -35267]]]
  hmulB := by decide  
  f := ![![![-53, 46, 24, -46, 22]], ![![-242, 59, 244, 2, -114]], ![![814, -358, -641, 244, 116]], ![![274, -110, -223, 69, 52]], ![![61, -94, 25, 122, -101]]]
  g := ![![![-30411, 86894, 25120, 11774, -69790], ![40672, -116213, -33596, -15746, 93338], ![-47534, 135818, 39263, 18404, -109084], ![43560, -124468, -35983, -16863, 99968], ![-15369, 43910, 12693, 5952, -35267]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [10, 4, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 10, 10], [0, 0, 1], [0, 1]]
 g := ![![[6, 0, 5], [10, 6, 1], []], ![[3, 8, 5, 10], [4, 10], [8, 1]], ![[0, 1, 3, 3], [1, 0, 8, 1], [6, 1]]]
 h' := ![![[6, 10, 10], [10, 10, 4], [0, 0, 1], [0, 1]], ![[0, 0, 1], [4, 5, 1], [0, 1], [6, 10, 10]], ![[0, 1], [1, 7, 6], [6, 10, 10], [0, 0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 9], []]
 b := ![[], [0, 4, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [10, 4, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2032366, 2390104, 958970, -2271324, 942918]
  a := ![-12, 8, 6, -13, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28952, -226948, 691000, -2271324, 942918]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53, 122, -53, -159, 141]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-53, 122, -53, -159, 141]] 
 ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-53, 122, -53, -159, 141], ![-1622, 563, 1425, -265, -459], ![3686, -1850, -2698, 1425, 194], ![-548, 1044, -335, -1326, 1125], ![-6966, 1902, 6618, -388, -2751]]]
  hmulB := by decide  
  f := ![![![-2884877, 1560584, -76293, 65273, -386930]], ![![-960555, 519617, -25404, 21732, -128834]], ![![-2245755, 1214850, -59391, 50812, -301209]], ![![375666, -203214, 9933, -8502, 50384]], ![![-919315, 497310, -24313, 20799, -123303]]]
  g := ![![![-65, 122, -53, -159, 141], ![-1185, 563, 1425, -265, -459], ![2840, -1850, -2698, 1425, 194], ![-618, 1044, -335, -1326, 1125], ![-4959, 1902, 6618, -388, -2751]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -2, -1, -1, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![3, -2, -1, -1, 0]] 
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![3, -2, -1, -1, 0], ![-2, 3, -3, -3, -2], ![8, 0, -2, -3, -1], ![4, 8, -5, -6, -4], ![10, 6, -4, -6, -3]]]
  hmulB := by decide  
  f := ![![![3, -4, -1, 3, -1]], ![![3, -3, -2, 2, 0]], ![![-3, 0, 3, 0, -1]], ![![2, -2, -1, 2, -1]], ![![6, -2, -6, 0, 3]]]
  g := ![![![2, -2, -1, -1, 0], ![0, 3, -3, -3, -2], ![2, 0, -2, -3, -1], ![-1, 8, -5, -6, -4], ![0, 6, -4, -6, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-520343, 281482, -13760, 11774, -69790]] ![![-53, 122, -53, -159, 141]]
  ![![3, -4, -1, 3, -1]] where
 M := ![![![3, -4, -1, 3, -1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![3, -4, -1, 3, -1]] ![![3, -2, -1, -1, 0]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, -68, 61, 59, 43]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![63, -68, 61, 59, 43]] 
 ![![13, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![63, -68, 61, 59, 43], ![-310, -39, 147, 181, 75], ![-56, -244, 114, 147, 106], ![-614, -282, 223, 322, 163], ![-422, -402, 190, 284, 175]]]
  hmulB := by decide  
  f := ![![![837, -34, -981, -235, 622]], ![![-572, 251, 453, -169, -84]], ![![848, -512, -538, 453, -85]], ![![939, -22, -1116, -287, 722]], ![![-2228, 1106, 1642, -844, -135]]]
  g := ![![![-60, -68, 61, 59, 43], ![-179, -39, 147, 181, 75], ![-165, -244, 114, 147, 106], ![-346, -282, 223, 322, 163], ![-320, -402, 190, 284, 175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![161, 152, 1, -39, -33]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![161, 152, 1, -39, -33]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![1, 9, 1, 0, 0], ![5, 6, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![161, 152, 1, -39, -33], ![292, 285, 39, -37, -45], ![80, 100, 66, 39, 8], ![118, 162, 151, 106, 33], ![-30, 30, 162, 152, 67]]]
  hmulB := by decide  
  f := ![![![-65, 34, 43, -25, -2]], ![![38, -53, 9, 61, -48]], ![![41, -39, -10, 41, -25]], ![![-45, 8, 48, 3, -24]], ![![9, -16, 3, 21, -17]]]
  g := ![![![40, 29, 1, -39, -33], ![51, 12, 39, -37, -45], ![-17, -56, 66, 39, 8], ![-56, -141, 151, 106, 33], ![-99, -180, 162, 152, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [2, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 12], [0, 1]]
 g := ![![[2, 1], [1], [9, 1]], ![[11, 12], [1], [5, 12]]]
 h' := ![![[9, 12], [10, 12], [8, 1], [0, 1]], ![[0, 1], [1, 1], [4, 12], [9, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [6, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [2, 4, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-443573, 99052, 320480, -60843, -21804]
  a := ![51, -28, -25, 50, 103]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26986, -186170, 320480, -60843, -21804]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89, 52, -5, -1, -14]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-89, 52, -5, -1, -14]] 
 ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-89, 52, -5, -1, -14], ![134, -59, -3, -11, 12], ![-134, 86, -8, -3, -23], ![154, -54, -5, -16, 10], ![-26, 42, -8, -10, -13]]]
  hmulB := by decide  
  f := ![![![65, -22, -59, 9, 21]], ![![-10, 7, 5, -7, 3]], ![![64, -30, -50, 21, 8]], ![![55, -18, -50, 7, 18]], ![![-64, 38, 40, -34, 7]]]
  g := ![![![0, 52, -5, -1, -14], ![15, -59, -3, -11, 12], ![1, 86, -8, -3, -23], ![20, -54, -5, -16, 10], ![10, 42, -8, -10, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2

def I13N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3139, 1698, -83, 71, -421]] i)))

def SI13N3: IdealEqSpanCertificate' Table ![![-3139, 1698, -83, 71, -421]] 
 ![![13, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-3139, 1698, -83, 71, -421], ![4198, -2271, 111, -95, 563], ![-4906, 2654, -130, 111, -658], ![4496, -2432, 119, -102, 603], ![-1586, 858, -42, 36, -213]]]
  hmulB := by decide  
  f := ![![![-45, -36, 3, 9, 10]], ![![-31, -25, 2, 6, 6]], ![![-37, -34, -1, 8, 9]], ![![-40, -30, 1, 4, 8]], ![![-13, -10, 1, 1, -1]]]
  g := ![![![-1043, 1698, -83, 71, -421], ![1395, -2271, 111, -95, 563], ![-1630, 2654, -130, 111, -658], ![1494, -2432, 119, -102, 603], ![-527, 858, -42, 36, -213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N3 : Nat.card (O ⧸ I13N3) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N3)

lemma isPrimeI13N3 : Ideal.IsPrime I13N3 := prime_ideal_of_norm_prime hp13.out _ NI13N3
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![63, -68, 61, 59, 43]] ![![161, 152, 1, -39, -33]]
  ![![839, 7144, 17312, 15228, 6297]] where
 M := ![![![839, 7144, 17312, 15228, 6297]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![839, 7144, 17312, 15228, 6297]] ![![-89, 52, -5, -1, -14]]
  ![![744207, 553126, -290639, -437977, -253775]] where
 M := ![![![744207, 553126, -290639, -437977, -253775]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N2 : IdealMulLeCertificate' Table 
  ![![744207, 553126, -290639, -437977, -253775]] ![![-3139, 1698, -83, 71, -421]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-154825333, 83579548, -4049838, 3568552, -20706803]]]
 hmul := by decide  
 g := ![![![![-11909641, 6429196, -311526, 274504, -1592831]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2, I13N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
    exact isPrimeI13N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1 ⊙ MulI13N2)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1159, 480, 945, -301, -213]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-1159, 480, 945, -301, -213]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![10, 14, 0, 1, 0], ![4, 13, 14, 0, 1]] where
  M :=![![![-1159, 480, 945, -301, -213], ![2774, -1749, -1689, 1589, -389], ![508, 1048, -1616, -1689, 1978], ![-9322, 3818, 7643, -2360, -1777], ![18154, -10194, -12250, 8588, -671]]]
  hmulB := by decide  
  f := ![![![-341, -318, -101, -11, 24]], ![![-352, -499, -343, -213, -46]], ![![128, 56, -340, -343, -167]], ![![-458, -586, -385, -228, -46]], ![![-194, -377, -607, -497, -193]]]
  g := ![![![159, 439, 231, -301, -213], ![-680, -1114, 221, 1589, -389], ![558, -60, -1724, -1689, 1978], ![1258, 3527, 1913, -2360, -1777], ![-3826, -7159, -168, 8588, -671]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [13, 10, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 8, 11], [13, 8, 6], [0, 1]]
 g := ![![[4, 12, 8], [2, 4], [12, 1], []], ![[0, 10, 9, 10], [], [5, 13], [13, 2]], ![[1, 13, 14, 5], [9, 4], [1, 13], [1, 2]]]
 h' := ![![[16, 8, 11], [0, 12, 5], [14, 3, 15], [0, 0, 1], [0, 1]], ![[13, 8, 6], [15, 1, 2], [7, 11], [2, 15, 8], [16, 8, 11]], ![[0, 1], [1, 4, 10], [13, 3, 2], [3, 2, 8], [13, 8, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 14], []]
 b := ![[], [15, 9, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [13, 10, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6952635, 5088840, 4280084, -4536688, 1125895]
  a := ![-12, 9, 7, -10, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1994745, 3174461, -675438, -4536688, 1125895]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-341, -318, -101, -11, 24]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-341, -318, -101, -11, 24]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![14, 9, 1, 0, 0], ![9, 11, 0, 1, 0], ![12, 7, 0, 0, 1]] where
  M :=![![![-341, -318, -101, -11, 24], ![-352, -499, -343, -213, -46], ![128, 56, -340, -343, -167], ![552, 204, -733, -784, -378], ![850, 566, -696, -834, -441]]]
  hmulB := by decide  
  f := ![![![-1159, 480, 945, -301, -213]], ![![2774, -1749, -1689, 1589, -389]], ![![544, -469, -211, 494, -265]], ![![633, -653, -143, 730, -469]], ![![1392, -981, -749, 947, -350]]]
  g := ![![![52, 32, -101, -11, 24], ![407, 309, -343, -213, -46], ![587, 474, -340, -343, -167], ![1318, 1063, -733, -784, -378], ![1376, 1123, -696, -834, -441]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [6, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 16], [0, 1]]
 g := ![![[], [], [], [1]], ![[], [], [], [1]]]
 h' := ![![[0, 16], [4], [2], [11], [0, 1]], ![[0, 1], [4], [2], [11], [0, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [0, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [6, 0, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2594, -3972, -128, 2884, 3332]
  a := ![-16, 10, 4, -26, -12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3926, -3404, -128, 2884, 3332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-1159, 480, 945, -301, -213]] ![![-341, -318, -101, -11, 24]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 16, -3, -21, 17]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-9, 16, -3, -21, 17]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![16, 8, 1, 0, 0], ![4, 18, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-9, 16, -3, -21, 17], ![-194, 65, 171, -27, -59], ![464, -228, -342, 171, 32], ![-106, 146, -13, -174, 133], ![-798, 198, 778, -16, -345]]]
  hmulB := by decide  
  f := ![![![-533, -482, 57, 183, 132]], ![![-1080, -991, 35, 297, 234]], ![![-928, -848, 58, 281, 213]], ![![-1180, -1086, 33, 320, 254]], ![![-161, -152, -1, 39, 33]]]
  g := ![![![2, 22, -3, -21, 17], ![-133, -43, 171, -27, -59], ![268, -30, -342, 171, 32], ![7, 178, -13, -174, 133], ![-603, -302, 778, -16, -345]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [11, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 18], [0, 1]]
 g := ![![[2, 7], [3, 1], [9], [1]], ![[0, 12], [0, 18], [9], [1]]]
 h' := ![![[16, 18], [5, 8], [3, 1], [8, 16], [0, 1]], ![[0, 1], [0, 11], [0, 18], [17, 3], [16, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [18, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [11, 3, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6847, 2692, 6057, -1413, -1921]
  a := ![1, 9, 7, 2, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4658, -1070, 6057, -1413, -1921]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![489, -454, 40, 40, 120]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![489, -454, 40, 40, 120]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![2, 16, 1, 0, 0], ![17, 17, 0, 1, 0], ![15, 2, 0, 0, 1]] where
  M :=![![![489, -454, 40, 40, 120], ![-1120, 195, 12, 120, -40], ![826, -666, 23, 12, 160], ![-1174, 214, -40, 75, -68], ![140, -348, -32, 0, 63]]]
  hmulB := by decide  
  f := ![![![-597, 422, 320, -408, 152]], ![![-1608, 217, 1740, 232, -968]], ![![-1068, 82, 1215, 244, -736]], ![![-2237, 755, 1988, -333, -668]], ![![-861, 296, 760, -136, -249]]]
  g := ![![![-109, -106, 40, 40, 120], ![-136, -103, 12, 120, -40], ![-96, -82, 23, 12, 160], ![-71, -15, -40, 75, -68], ![-39, 2, -32, 0, 63]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [17, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 18], [0, 1]]
 g := ![![[7, 9], [17, 11], [6], [1]], ![[0, 10], [0, 8], [6], [1]]]
 h' := ![![[14, 18], [15, 3], [16, 7], [2, 14], [0, 1]], ![[0, 1], [0, 16], [0, 12], [8, 5], [14, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [1, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [17, 5, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-385, -12, 229, 1, 101]
  a := ![-3, 0, 1, -4, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-125, -205, 229, 1, 101]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, -1, 1, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![3, 0, -1, 1, 0]] 
 ![![19, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![3, 0, -1, 1, 0], ![0, 3, 1, -1, 2], ![-10, 2, 10, 1, -3], ![14, -10, -9, 10, 2], ![-18, 10, 8, -10, 9]]]
  hmulB := by decide  
  f := ![![![2235, -1206, 59, -51, 299]], ![![1137, -613, 30, -26, 152]], ![![1360, -734, 36, -31, 182]], ![![1361, -734, 36, -31, 182]], ![![530, -286, 14, -12, 71]]]
  g := ![![![0, 0, -1, 1, 0], ![-2, 3, 1, -1, 2], ![-7, 2, 10, 1, -3], ![4, -10, -9, 10, 2], ![-6, 10, 8, -10, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-9, 16, -3, -21, 17]] ![![489, -454, 40, 40, 120]]
  ![![2235, -1206, 59, -51, 299]] where
 M := ![![![2235, -1206, 59, -51, 299]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![2235, -1206, 59, -51, 299]] ![![3, 0, -1, 1, 0]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1257, -680, 34, -28, 169]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![1257, -680, 34, -28, 169]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![22, 7, 10, 8, 1]] where
  M :=![![![1257, -680, 34, -28, 169], ![-1684, 909, -42, 40, -225], ![1966, -1066, 51, -42, 265], ![-1808, 972, -44, 43, -239], ![628, -348, 22, -10, 85]]]
  hmulB := by decide  
  f := ![![![3, 4, 0, -2, -1]], ![![8, 7, 0, -2, -3]], ![![10, 2, -5, 0, 1]], ![![0, 12, 6, -5, -1]], ![![10, 11, 0, -4, -2]]]
  g := ![![![-107, -81, -72, -60, 169], ![142, 108, 96, 80, -225], ![-168, -127, -113, -94, 265], ![150, 115, 102, 85, -239], ![-54, -41, -36, -30, 85]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [11, 3, 18, 16, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 15, 15, 16], [3, 16, 1, 4], [22, 14, 7, 3], [0, 1]]
 g := ![![[10, 13, 20, 12], [4, 8, 17, 18], [7, 1], []], ![[14, 5, 14, 17, 7, 1], [19, 19, 11, 14, 5, 8], [20, 21, 14, 12, 2, 4], [18, 18, 3]], ![[18, 18, 22, 3, 8, 8], [17, 10, 9, 17, 3, 6], [1, 22, 12, 5, 11, 12], [14, 5, 16]], ![[1, 20, 4, 8, 1, 4], [8, 14, 11, 15, 0, 18], [17, 10, 14, 5, 16, 6], [16, 13, 9]]]
 h' := ![![[5, 15, 15, 16], [2, 10, 22, 9], [15, 14, 9, 8], [0, 0, 1], [0, 1]], ![[3, 16, 1, 4], [17, 19, 13, 6], [17, 10, 21, 9], [11, 13, 10, 12], [5, 15, 15, 16]], ![[22, 14, 7, 3], [9, 15, 16, 5], [21, 6, 3, 17], [16, 22, 3, 16], [3, 16, 1, 4]], ![[0, 1], [9, 2, 18, 3], [8, 16, 13, 12], [9, 11, 9, 18], [22, 14, 7, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 10, 12], []]
 b := ![[], [], [21, 18, 2, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [11, 3, 18, 16, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12156467, 988144830, -1051761099, -1499226603, 1595101956]
  a := ![12, -6, -3, 8, 29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1525221155, -442502994, -739251333, -620001837, 1595101956]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 4, 0, -2, -1]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![3, 4, 0, -2, -1]] 
 ![![23, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![3, 4, 0, -2, -1], ![8, 7, 0, -2, -3], ![10, 2, -5, 0, 1], ![0, 12, 6, -5, -1], ![8, 0, 2, 6, -5]]]
  hmulB := by decide  
  f := ![![![1257, -680, 34, -28, 169]], ![![364, -197, 10, -8, 49]], ![![632, -342, 17, -14, 85]], ![![140, -76, 4, -3, 19]], ![![1175, -636, 32, -26, 158]]]
  g := ![![![0, 4, 0, -2, -1], ![1, 7, 0, -2, -3], ![1, 2, -5, 0, 1], ![-5, 12, 6, -5, -1], ![3, 0, 2, 6, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![1257, -680, 34, -28, 169]] ![![3, 4, 0, -2, -1]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB314I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB314I0 : PrimesBelowBoundCertificateInterval O 1 23 314 where
  m := 9
  g := ![5, 5, 5, 2, 3, 4, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB314I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N2, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1, I13N2, I13N3]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
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
    · exact ![343, 49]
    · exact ![1331, 11, 11]
    · exact ![13, 169, 13, 13]
    · exact ![4913, 289]
    · exact ![361, 361, 19]
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
      exact NI2N2
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
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
      exact NI13N3
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I5N0, I7N1, I11N1, I11N2, I13N0, I13N1, I13N2, I13N3, I17N1, I19N2, I23N1]
  Il := ![[I2N0, I2N1, I2N2, I2N2, I2N2], [I3N0, I3N0, I3N0, I3N0, I3N0], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1, I11N2], [I13N0, I13N1, I13N2, I13N3], [I17N1], [I19N2], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
