
import IdealArithmetic.Examples.NF5_3_40500000_1.RI5_3_40500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 6, 11, 2, -33]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![29, 6, 11, 2, -33]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![29, 6, 11, 2, -33], ![137, 29, 42, 8, -135], ![563, 132, 179, 28, -561], ![1138, 230, 396, 77, -1224], ![424, 94, 139, 24, -434]]]
  hmulB := by decide  
  f := ![![![-915, -82, 333, 130, -702]], ![![845, 73, -314, -122, 663]], ![![-1607, -148, 577, 226, -1215]], ![![1033, 84, -397, -153, 840]], ![![-1179, -108, 424, 166, -893]]]
  g := ![![![31, 6, 11, 2, -33], ![136, 29, 42, 8, -135], ![562, 132, 179, 28, -561], ![1181, 230, 396, 77, -1224], ![429, 94, 139, 24, -434]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -1, -3, -1, 7]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![0, -1, -3, -1, 7]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![0, -1, -3, -1, 7], ![-21, -7, 0, 1, 1], ![-19, -9, -24, -7, 55], ![-78, -29, -7, 0, 24], ![-15, -7, -11, -3, 26]]]
  hmulB := by decide  
  f := ![![![-32, -7, -11, -2, 34]], ![![-87, -19, -28, -5, 88]], ![![-315, -70, -103, -18, 322]], ![![-624, -135, -205, -37, 641]], ![![-241, -53, -79, -14, 247]]]
  g := ![![![-1, -1, -3, -1, 7], ![-8, -7, 0, 1, 1], ![-17, -9, -24, -7, 55], ![-33, -29, -7, 0, 24], ![-10, -7, -11, -3, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 0, -3, -1, 7]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![4, 0, -3, -1, 7]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![4, 0, -3, -1, 7], ![-21, -3, 1, 1, 1], ![-19, -8, -20, -5, 55], ![-92, -18, -22, -3, 72], ![-20, -6, -13, -3, 37]]]
  hmulB := by decide  
  f := ![![![-5, -2, 0, 0, 1]], ![![-5, -3, -2, 0, 4]], ![![-20, -2, -9, -4, 25]], ![![-32, -22, 6, 5, -12]], ![![-13, -4, -3, -1, 9]]]
  g := ![![![0, 0, -3, -1, 7], ![-10, -3, 1, 1, 1], ![-23, -8, -20, -5, 55], ![-62, -18, -22, -3, 72], ![-19, -6, -13, -3, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![29, 6, 11, 2, -33]] ![![0, -1, -3, -1, 7]]
  ![![4, 3, -2, -1, 4]] where
 M := ![![![4, 3, -2, -1, 4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![4, 3, -2, -1, 4]] ![![0, -1, -3, -1, 7]]
  ![![-7, -6, -1, 1, 1]] where
 M := ![![![-7, -6, -1, 1, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-7, -6, -1, 1, 1]] ![![4, 0, -3, -1, 7]]
  ![![5, 2, 0, 0, -1]] where
 M := ![![![5, 2, 0, 0, -1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![5, 2, 0, 0, -1]] ![![4, 0, -3, -1, 7]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-2, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -3, -1, 0, 3]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-10, -3, -1, 0, 3]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 1, 0, 1, 0], ![1, 2, 0, 0, 1]] where
  M :=![![![-10, -3, -1, 0, 3], ![-15, -8, -9, -2, 21], ![-77, -25, -20, -4, 51], ![-92, -41, -29, -5, 72], ![-43, -15, -11, -2, 28]]]
  hmulB := by decide  
  f := ![![![-4, -1, -1, 0, 3]], ![![-15, -2, -7, -2, 21]], ![![-27, -8, -5, 0, 18]], ![![-45, -7, -22, -5, 63]], ![![-29, -6, -10, -2, 31]]]
  g := ![![![-4, -3, -1, 0, 3], ![-9, -16, -9, -2, 21], ![-36, -41, -20, -4, 51], ![-45, -60, -29, -5, 72], ![-20, -23, -11, -2, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]], ![[1, 2]]]
 h' := ![![[2, 2], [0, 1]], ![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-192836, -39736, -74756, -9346, 229560]
  a := ![77, -62, 79, 36, -264]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-115880, -163170, -74756, -9346, 229560]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![243, 53, 79, 14, -248]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![243, 53, 79, 14, -248]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![243, 53, 79, 14, -248], ![1044, 228, 339, 60, -1064], ![4480, 979, 1456, 258, -4568], ![9092, 1989, 2953, 523, -9264], ![3370, 737, 1095, 194, -3435]]]
  hmulB := by decide  
  f := ![![![-35, -5, 13, 4, -24]], ![![-2, -4, 3, 2, -8]], ![![-54, 13, 2, -4, 8]], ![![-24, -43, 37, 17, -80]], ![![-18, 1, 3, 0, -3]]]
  g := ![![![-7, 53, 79, 14, -248], ![-30, 228, 339, 60, -1064], ![-130, 979, 1456, 258, -4568], ![-264, 1989, 2953, 523, -9264], ![-98, 737, 1095, 194, -3435]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-10, -3, -1, 0, 3]] ![![243, 53, 79, 14, -248]]
  ![![68, 18, 22, 4, -65]] where
 M := ![![![68, 18, 22, 4, -65]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![68, 18, 22, 4, -65]] ![![243, 53, 79, 14, -248]]
  ![![-48806, -10703, -15857, -2810, 49707]] where
 M := ![![![-48806, -10703, -15857, -2810, 49707]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-48806, -10703, -15857, -2810, 49707]] ![![243, 53, 79, 14, -248]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![47890920, 10493964, 15559452, 2756958, -48785049]]]
 hmul := by decide  
 g := ![![![![15963640, 3497988, 5186484, 918986, -16261683]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-867, -190, -282, -50, 884]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-867, -190, -282, -50, 884]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-867, -190, -282, -50, 884], ![-3720, -815, -1208, -214, 3788], ![-15944, -3494, -5181, -918, 16244], ![-32324, -7082, -10502, -1861, 32928], ![-11984, -2626, -3894, -690, 12209]]]
  hmulB := by decide  
  f := ![![![33, 14, 2, -2, -4]], ![![36, 13, 12, 2, -28]], ![![100, 46, -1, -6, -4]], ![![28, 10, 46, 11, -96]], ![![60, 26, 6, -2, -15]]]
  g := ![![![-503, -190, -282, -50, 884], ![-2156, -815, -1208, -214, 3788], ![-9244, -3494, -5181, -918, 16244], ![-18740, -7082, -10502, -1861, 32928], ![-6948, -2626, -3894, -690, 12209]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-867, -190, -282, -50, 884]] ![![-867, -190, -282, -50, 884]]
  ![![-3022959, -662396, -982140, -174024, 3079400]] where
 M := ![![![-3022959, -662396, -982140, -174024, 3079400]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-3022959, -662396, -982140, -174024, 3079400]] ![![-867, -190, -282, -50, 884]]
  ![![-10534119091, -2308254322, -3422467406, -606422122, 10730798364]] where
 M := ![![![-10534119091, -2308254322, -3422467406, -606422122, 10730798364]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-10534119091, -2308254322, -3422467406, -606422122, 10730798364]] ![![-867, -190, -282, -50, 884]]
  ![![-36708291271647, -8043584019576, -11926287269048, -2113201843952, 37393660401616]] where
 M := ![![![-36708291271647, -8043584019576, -11926287269048, -2113201843952, 37393660401616]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-36708291271647, -8043584019576, -11926287269048, -2113201843952, 37393660401616]] ![![-867, -190, -282, -50, 884]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-127917544546019715, -28029512720154470, -41559585863518850, -7363883788762690, 130305853376972740]]]
 hmul := by decide  
 g := ![![![![-25583508909203943, -5605902544030894, -8311917172703770, -1472776757752538, 26061170675394548]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![656, 57, -241, -94, 509]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![656, 57, -241, -94, 509]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![1, 3, 5, 5, 1]] where
  M :=![![![656, 57, -241, -94, 509], ![-1229, -110, 449, 176, -949], ![2281, 207, -852, -334, 1805], ![-1560, -165, 579, 229, -1224], ![1019, 89, -379, -148, 802]]]
  hmulB := by decide  
  f := ![![![34, 7, 11, 2, -35]], ![![147, 32, 47, 8, -149]], ![![633, 133, 210, 38, -659]], ![![1308, 285, 417, 73, -1320]], ![![1523, 328, 492, 87, -1553]]]
  g := ![![![21, -210, -398, -377, 509], ![-40, 391, 742, 703, -949], ![68, -744, -1411, -1337, 1805], ![-48, 501, 957, 907, -1224], ![31, -331, -627, -594, 802]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [5, 4, 3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 2, 6], [5, 1, 4, 6], [0, 3, 4, 1], [0, 1]]
 g := ![![[0, 1, 5, 1], []], ![[6, 1, 4, 0, 5], [3, 1, 6]], ![[1, 2, 6, 1, 1, 6], [1, 1, 3, 0, 0, 6]], ![[0, 5, 2, 4, 2, 4], [6, 5, 6, 6, 3, 1]]]
 h' := ![![[0, 2, 6], [0, 0, 0, 1], [0, 1]], ![[5, 1, 4, 6], [6, 4, 6, 3], [0, 2, 6]], ![[0, 3, 4, 1], [1, 3, 6, 1], [5, 1, 4, 6]], ![[0, 1], [5, 0, 2, 2], [0, 3, 4, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 0, 2], []]
 b := ![[], [], [5, 3, 5, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [5, 4, 3, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-327436950493265, -69977788250732, -107502120656454, -19103989693186, 337792132899546]
  a := ![379, -328, 378, 160, -1299]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-95032726198973, -154764883849910, -256637540736312, -244009236312988, 337792132899546]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34, -7, -11, -2, 35]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-34, -7, -11, -2, 35]] 
 ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-34, -7, -11, -2, 35], ![-147, -32, -47, -8, 149], ![-633, -133, -210, -38, 659], ![-1308, -285, -417, -73, 1320], ![-481, -103, -157, -28, 494]]]
  hmulB := by decide  
  f := ![![![-656, -57, 241, 94, -509]], ![![-293, -25, 108, 42, -228]], ![![-607, -54, 225, 88, -476]], ![![-152, -9, 55, 21, -116]], ![![-333, -29, 123, 48, -260]]]
  g := ![![![-4, -7, -11, -2, 35], ![-16, -32, -47, -8, 149], ![-72, -133, -210, -38, 659], ![-140, -285, -417, -73, 1320], ![-53, -103, -157, -28, 494]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![656, 57, -241, -94, 509]] ![![-34, -7, -11, -2, 35]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [3, 9, 2, 3, 10, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 8, 5, 6, 2], [6, 8, 6, 9, 6], [4, 4, 8, 2, 8], [2, 1, 3, 5, 6], [0, 1]]
 g := ![![[0, 4, 8, 6, 1], [1], []], ![[9, 7, 4, 3, 2, 8, 3, 7], [0, 0, 3, 0, 2, 2, 3, 6], [6, 6, 6, 4]], ![[3, 9, 0, 1, 10, 7, 0, 7], [3, 7, 7, 9, 3, 9, 6, 8], [10, 2, 1, 3]], ![[4, 4, 4, 8, 3, 7, 2, 6], [4, 5, 2, 6, 4, 2, 10, 7], [2, 3, 8, 9]], ![[7, 0, 2, 10, 1, 8, 1, 7], [1, 6, 9, 7, 6, 9, 10, 2], [6, 5, 8, 3]]]
 h' := ![![[0, 8, 5, 6, 2], [8, 2, 9, 8, 1], [0, 0, 1], [0, 1]], ![[6, 8, 6, 9, 6], [0, 7, 6, 3, 8], [4, 5, 2, 6, 6], [0, 8, 5, 6, 2]], ![[4, 4, 8, 2, 8], [9, 9, 3, 2, 5], [6, 0, 7, 9, 7], [6, 8, 6, 9, 6]], ![[2, 1, 3, 5, 6], [3, 1, 7, 0, 3], [10, 5, 3, 2, 7], [4, 4, 8, 2, 8]], ![[0, 1], [4, 3, 8, 9, 5], [8, 1, 9, 5, 2], [2, 1, 3, 5, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 8, 9, 7], [], [], []]
 b := ![[], [4, 7, 6, 4, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [3, 9, 2, 3, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14637086557445, 3210806966631, 4726037348395, 830681955774, -14858135741823]
  a := ![40, -33, 41, 18, -137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1330644232495, 291891542421, 429639758945, 75516541434, -1350739612893]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, 12, 0, 2, -11]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![26, 12, 0, 2, -11]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![11, 11, 5, 1, 0], ![2, 8, 8, 0, 1]] where
  M :=![![![26, 12, 0, 2, -11], ![27, 37, 4, -14, 19], ![101, -104, 209, 106, -539], ![592, 450, -310, -155, 648], ![97, 12, 50, 24, -142]]]
  hmulB := by decide  
  f := ![![![5348, 1172, 1738, 308, -5449]], ![![22933, 5025, 7450, 1320, -23359]], ![![98315, 21544, 31943, 5660, -100153]], ![![77074, 16889, 25041, 4437, -78513]], ![![81121, 17776, 26356, 4670, -82636]]]
  g := ![![![2, 6, 6, 2, -11], ![11, 3, -6, -14, 19], ![1, 234, 307, 106, -539], ![77, -233, -363, -155, 648], ![9, 68, 82, 24, -142]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [7, 6, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 12, 5], [12, 0, 8], [0, 1]]
 g := ![![[2, 12, 12], [3, 4], [1]], ![[9, 10, 2, 8], [0, 3], [7, 9, 0, 8]], ![[8, 5, 8, 7], [9, 10], [0, 6, 3, 5]]]
 h' := ![![[12, 12, 5], [2, 12, 8], [6, 7, 11], [0, 1]], ![[12, 0, 8], [4, 2, 8], [2, 9, 9], [12, 12, 5]], ![[0, 1], [3, 12, 10], [12, 10, 6], [12, 0, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 3], []]
 b := ![[], [10, 3, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [7, 6, 2, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9313791320, -2002577944, -2731108349, -467369705, 8977567068]
  a := ![-240, 198, -243, -111, 823]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1702142977, -5283234441, -5554984336, -467369705, 8977567068]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5348, 1172, 1738, 308, -5449]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![5348, 1172, 1738, 308, -5449]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![7, 3, 1, 0, 0], ![9, 6, 0, 1, 0], ![11, 7, 0, 0, 1]] where
  M :=![![![5348, 1172, 1738, 308, -5449], ![22933, 5025, 7450, 1320, -23359], ![98315, 21544, 31943, 5660, -100153], ![199296, 43670, 64750, 11473, -203016], ![73893, 16192, 24008, 4254, -75274]]]
  hmulB := by decide  
  f := ![![![26, 12, 0, 2, -11]], ![![27, 37, 4, -14, 19]], ![![28, 7, 17, 6, -43]], ![![76, 60, -22, -17, 51]], ![![44, 31, 6, -4, -10]]]
  g := ![![![3873, 2481, 1738, 308, -5449], ![16604, 10636, 7450, 1320, -23359], ![71189, 45602, 31943, 5660, -100153], ![144305, 92438, 64750, 11473, -203016], ![53505, 34274, 24008, 4254, -75274]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [4, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 12], [0, 1]]
 g := ![![[4, 10], [12], [10, 1]], ![[0, 3], [12], [7, 12]]]
 h' := ![![[10, 12], [5, 6], [12, 5], [0, 1]], ![[0, 1], [0, 7], [10, 8], [10, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [6, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [4, 3, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-355715, -73371, -196325, -24488, 544895]
  a := ![135, -105, 140, 70, -463]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-365761, -242441, -196325, -24488, 544895]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![26, 12, 0, 2, -11]] ![![5348, 1172, 1738, 308, -5449]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
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


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [6, 4, 6, 2, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 12, 3, 0, 14], [13, 11, 15, 1, 14], [10, 6, 7, 8, 13], [8, 4, 9, 8, 10], [0, 1]]
 g := ![![[9, 4, 1, 9, 16], [6, 0, 11, 1], [], []], ![[11, 16, 5, 13, 11, 2, 14, 11], [12, 15, 13, 16], [10, 12, 8, 4], [5, 16, 14, 9]], ![[9, 11, 7, 0, 2, 5], [14, 7, 14, 4], [16, 2, 13, 15], [8, 15, 8, 9]], ![[11, 9, 12, 9, 4, 12, 16, 16], [4, 9, 1, 15], [15, 1, 5, 4], [10, 1, 10, 16]], ![[10, 3, 7, 16, 16, 0, 15, 3], [10, 9, 2, 9], [16, 11, 14, 9], [6, 15, 2, 15]]]
 h' := ![![[14, 12, 3, 0, 14], [15, 10, 0, 6, 13], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[13, 11, 15, 1, 14], [11, 4, 14, 11, 6], [7, 15, 6, 3, 4], [13, 16, 16, 9, 15], [14, 12, 3, 0, 14]], ![[10, 6, 7, 8, 13], [16, 10, 9, 2], [10, 2, 16, 1, 2], [2, 11, 15, 11, 7], [13, 11, 15, 1, 14]], ![[8, 4, 9, 8, 10], [2, 13, 1, 15, 9], [14, 6, 9, 15, 7], [6, 6, 1, 14, 15], [10, 6, 7, 8, 13]], ![[0, 1], [4, 14, 10, 0, 6], [8, 11, 3, 15, 3], [11, 1, 1, 0, 14], [8, 4, 9, 8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 0, 12, 6], [], [], []]
 b := ![[], [9, 9, 13, 16, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [6, 4, 6, 2, 6, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![75605046350118, 34917213615904, -44835180790912, -11965947340848, 75682088157696]
  a := ![-84, 56, -86, -62, 288]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4447355667654, 2053953742112, -2637363575936, -703879255344, 4451887538688]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-184, -41, -59, -10, 185]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-184, -41, -59, -10, 185]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![9, 5, 6, 1, 0], ![15, 2, 15, 0, 1]] where
  M :=![![![-184, -41, -59, -10, 185], ![-785, -168, -261, -48, 815], ![-3403, -759, -1078, -186, 3401], ![-6808, -1479, -2255, -403, 7032], ![-2545, -561, -821, -144, 2578]]]
  hmulB := by decide  
  f := ![![![42, 21, 25, 6, -59]], ![![211, 74, 49, 8, -125]], ![![513, 223, 204, 42, -491]], ![![281, 116, 103, 21, -250]], ![![476, 207, 192, 40, -462]]]
  g := ![![![-151, -19, -146, -10, 185], ![-662, -82, -642, -48, 815], ![-2776, -349, -2683, -186, 3401], ![-5719, -712, -5543, -403, 7032], ![-2101, -263, -2033, -144, 2578]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [1, 1, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 5, 3], [5, 13, 16], [0, 1]]
 g := ![![[15, 0, 16], [18, 7, 16], [9, 1], []], ![[12, 3, 13, 12], [12, 6, 12, 8], [11, 17], [16, 9]], ![[7, 18, 7, 7], [3, 15, 17, 5], [18, 6], [3, 9]]]
 h' := ![![[4, 5, 3], [1, 18, 15], [10, 9, 4], [0, 0, 1], [0, 1]], ![[5, 13, 16], [16, 11, 2], [8, 10, 3], [0, 15, 13], [4, 5, 3]], ![[0, 1], [3, 9, 2], [10, 0, 12], [3, 4, 5], [5, 13, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 16], []]
 b := ![[], [6, 10, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [1, 1, 10, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-284855403, -50687890, -93494744, -18106206, 303723848]
  a := ![-12, 22, -8, 15, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-246197751, -29873924, -238985012, -18106206, 303723848]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![835, 183, 271, 48, -850]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![835, 183, 271, 48, -850]] 
 ![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![835, 183, 271, 48, -850], ![3578, 784, 1163, 206, -3646], ![15346, 3361, 4986, 884, -15634], ![31108, 6819, 10103, 1789, -31680], ![11534, 2527, 3747, 664, -11749]]]
  hmulB := by decide  
  f := ![![![801, 65, -315, -122, 670]], ![![293, 21, -120, -46, 256]], ![![732, 59, -296, -114, 630]], ![![630, 41, -263, -101, 564]], ![![398, 31, -161, -62, 343]]]
  g := ![![![70, 183, 271, 48, -850], ![300, 784, 1163, 206, -3646], ![1287, 3361, 4986, 884, -15634], ![2607, 6819, 10103, 1789, -31680], ![967, 2527, 3747, 664, -11749]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -4, -2, 0, 8]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-13, -4, -2, 0, 8]] 
 ![![19, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![-13, -4, -2, 0, 8], ![-40, -7, -20, -4, 56], ![-224, -48, -59, -12, 200], ![-396, -104, -124, -15, 384], ![-158, -36, -46, -8, 149]]]
  hmulB := by decide  
  f := ![![![-975, -92, 346, 136, -728]], ![![-781, -75, 274, 108, -576]], ![![-955, -92, 335, 132, -704]], ![![-716, -72, 244, 97, -512]], ![![-751, -72, 264, 104, -555]]]
  g := ![![![-1, -4, -2, 0, 8], ![-15, -7, -20, -4, 56], ![-49, -48, -59, -12, 200], ![-80, -104, -124, -15, 384], ![-35, -36, -46, -8, 149]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-184, -41, -59, -10, 185]] ![![835, 183, 271, 48, -850]]
  ![![616958, 135190, 200444, 35516, -628473]] where
 M := ![![![616958, 135190, 200444, 35516, -628473]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![616958, 135190, 200444, 35516, -628473]] ![![-13, -4, -2, 0, 8]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![26906888, 5895890, 8741862, 1548956, -27409229]]]
 hmul := by decide  
 g := ![![![![1416152, 310310, 460098, 81524, -1442591]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![254, 123, -157, -44, 271]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![254, 123, -157, -44, 271]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![9, 3, 13, 18, 1]] where
  M :=![![![254, 123, -157, -44, 271], ![-739, -116, 241, -6, -215], ![1159, -779, 404, 524, -1793], ![1184, 2825, -2647, -1427, 6408], ![527, 7, -123, 42, 10]]]
  hmulB := by decide  
  f := ![![![104, 21, 27, 4, -89]], ![![389, 86, 139, 26, -431]], ![![1791, 383, 558, 96, -1769]], ![![3556, 775, 1171, 209, -3672]], ![![3945, 855, 1279, 226, -4023]]]
  g := ![![![-95, -30, -160, -214, 271], ![52, 23, 132, 168, -215], ![752, 200, 1031, 1426, -1793], ![-2456, -713, -3737, -5077, 6408], ![19, -1, -11, -6, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [20, 14, 10, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3, 20, 12], [1, 5, 20, 1], [14, 14, 6, 10], [0, 1]]
 g := ![![[17, 16, 8, 12], [22, 8, 11, 1], [20, 1], []], ![[14, 20, 3, 7, 9, 12], [21, 14, 8, 18, 1, 2], [2, 10, 18, 10, 4, 12], [15, 2, 6]], ![[8, 17, 0, 19, 16, 12], [3, 2, 4, 8, 10, 13], [22, 16, 1, 14, 22, 12], [13, 14, 1]], ![[18, 16, 14, 20, 14, 15], [14, 3, 20, 21, 9, 7], [12, 8, 8, 9, 6, 19], [17, 4, 8]]]
 h' := ![![[5, 3, 20, 12], [20, 4, 18, 14], [14, 22, 16, 22], [0, 0, 1], [0, 1]], ![[1, 5, 20, 1], [1, 0, 2, 1], [11, 13, 21, 2], [1, 10, 3, 22], [5, 3, 20, 12]], ![[14, 14, 6, 10], [17, 3, 13, 14], [10, 8, 15, 6], [17, 8, 18, 9], [1, 5, 20, 1]], ![[0, 1], [11, 16, 13, 17], [11, 3, 17, 16], [17, 5, 1, 15], [14, 14, 6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [17, 3, 11], []]
 b := ![[], [], [6, 0, 0, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [20, 14, 10, 3, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-92720856, 6447164, 11228916, -12160356, 24110344]
  a := ![-12, 6, -13, -11, 41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13465824, -2864516, -13139372, -19397676, 24110344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-104, -21, -27, -4, 89]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-104, -21, -27, -4, 89]] 
 ![![23, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-104, -21, -27, -4, 89], ![-389, -86, -139, -26, 431], ![-1791, -383, -558, -96, 1769], ![-3556, -775, -1171, -209, 3672], ![-1341, -289, -425, -74, 1342]]]
  hmulB := by decide  
  f := ![![![-254, -123, 157, 44, -271]], ![![-1, -11, 10, 6, -26]], ![![-205, -41, 78, 4, -87]], ![![-184, -187, 197, 85, -420]], ![![-45, -11, 19, 2, -24]]]
  g := ![![![9, -21, -27, -4, 89], ![55, -86, -139, -26, 431], ![208, -383, -558, -96, 1769], ![449, -775, -1171, -209, 3672], ![160, -289, -425, -74, 1342]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![254, 123, -157, -44, 271]] ![![-104, -21, -27, -4, 89]]
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


lemma PB312I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB312I0 : PrimesBelowBoundCertificateInterval O 1 23 312 where
  m := 9
  g := ![5, 4, 5, 2, 1, 2, 1, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB312I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
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
    · exact ![9, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![2401, 7]
    · exact ![161051]
    · exact ![2197, 169]
    · exact ![1419857]
    · exact ![6859, 19, 19]
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
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I13N1, I19N1, I19N2, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [], [I13N1], [], [I19N1, I19N2], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
