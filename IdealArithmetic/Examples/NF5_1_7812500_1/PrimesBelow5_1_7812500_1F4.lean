
import IdealArithmetic.Examples.NF5_1_7812500_1.RI5_1_7812500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 37, -49, -10, 46]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-13, 37, -49, -10, 46]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![126, 52, 16, 109, 1]] where
  M :=![![![-13, 37, -49, -10, 46], ![20, -69, 15, -45, 50], ![90, -75, 146, 190, -560], ![-380, 840, -285, -244, 620], ![-46, 143, 44, 25, -115]]]
  hmulB := by decide  
  f := ![![![125, 6, -37, -25, 98]], ![![50, 2, -15, -10, 40]], ![![20, 0, -8, -5, 20]], ![![10, -5, -5, -3, 10]], ![![126, 2, -39, -26, 101]]]
  g := ![![![-37, -15, -5, -32, 46], ![-40, -17, -5, -35, 50], ![450, 185, 58, 390, -560], ![-500, -200, -65, -432, 620], ![92, 39, 12, 80, -115]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 4 2 7 [46, 154, 26, 101, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 89, 32, 39], [125, 42, 131, 58], [30, 25, 151, 60], [0, 1]]
 g := ![![[67, 108, 105, 12], [106, 41, 47], [42, 67, 104, 48], [17, 141, 23, 56], [65, 84, 4, 153], [1], []], ![[146, 113, 101, 102, 18, 86], [147, 20, 12], [128, 12, 86, 126, 90, 57], [6, 118, 32, 58, 48, 148], [71, 22, 40, 72, 32, 30], [145, 40, 90], [62, 66, 108]], ![[116, 54, 147, 156, 70, 67], [32, 139, 42], [146, 10, 22, 27, 12, 11], [97, 38, 155, 17, 53, 146], [18, 60, 155, 21, 131, 110], [31, 54, 153], [120, 108, 67]], ![[3, 89, 80, 122, 47, 41], [48, 2, 46], [119, 47, 57, 139, 69, 69], [148, 16, 41, 135, 129, 96], [156, 142, 150, 15, 128, 69], [96, 6, 4], [98, 77, 146]]]
 h' := ![![[58, 89, 32, 39], [97, 0, 105, 13], [109, 36, 126, 19], [3, 51, 98, 131], [150, 17, 143, 128], [111, 3, 131, 56], [0, 0, 1], [0, 1]], ![[125, 42, 131, 58], [16, 3, 98, 136], [59, 44, 13, 144], [51, 38, 74, 137], [117, 98, 114, 151], [35, 105, 67, 115], [41, 95, 70, 54], [58, 89, 32, 39]], ![[30, 25, 151, 60], [134, 155, 24, 134], [151, 51, 150, 102], [153, 78, 138, 43], [48, 61, 7, 105], [96, 6, 152, 146], [57, 83, 62, 101], [125, 42, 131, 58]], ![[0, 1], [151, 156, 87, 31], [2, 26, 25, 49], [151, 147, 4, 3], [65, 138, 50, 87], [146, 43, 121, 154], [3, 136, 24, 2], [30, 25, 151, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [0, 114, 70], []]
 b := ![[], [], [103, 26, 69, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 4
  hpos := by decide
  P := [46, 154, 26, 101, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4367210, -3421949, 7590317, 5815766, -26935146]
  a := ![5, -3, 16, 11, -45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![21644558, 8899399, 2793329, 18737240, -26935146]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 607573201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-125, -6, 37, 25, -98]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-125, -6, 37, 25, -98]] 
 ![![157, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  M :=![![![-125, -6, 37, 25, -98], ![-50, -2, 15, 10, -40], ![-20, 0, 8, 5, -20], ![-10, 5, 5, 3, -10], ![-22, 1, 8, 5, -19]]]
  hmulB := by decide  
  f := ![![![13, -37, 49, 10, -46]], ![![6, -17, 23, 5, -22]], ![![1, -4, 5, 0, -2]], ![![3, -7, 4, 2, -6]], ![![7, -20, 25, 5, -23]]]
  g := ![![![47, -6, 37, 25, -98], ![19, -2, 15, 10, -40], ![9, 0, 8, 5, -20], ![2, 5, 5, 3, -10], ![8, 1, 8, 5, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-13, 37, -49, -10, 46]] ![![-125, -6, 37, 25, -98]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![-157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -10, 7, 11, -26]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![13, -10, 7, 11, -26]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![119, 137, 1, 0, 0], ![160, 95, 0, 1, 0], ![24, 90, 0, 0, 1]] where
  M :=![![![13, -10, 7, 11, -26], ![-22, 50, -35, -22, 68], ![44, -112, 68, 7, -56], ![-14, 107, -49, 89, -154], ![6, -5, 4, 11, -25]]]
  hmulB := by decide  
  f := ![![![45, -45, -43, -18, 38]], ![![36, -11, 5, 9, -134]], ![![63, -41, -26, -5, -88]], ![![64, -47, -36, -11, -46]], ![![26, -11, -2, 3, -71]]]
  g := ![![![-12, 2, 7, 11, -26], ![37, 5, -35, -22, 68], ![-48, -31, 68, 7, -56], ![-29, 75, -49, 89, -154], ![-10, 4, 4, 11, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [120, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 162], [0, 1]]
 g := ![![[135, 77], [35, 119], [155], [131], [57], [119, 57], [1]], ![[11, 86], [36, 44], [155], [131], [57], [114, 106], [1]]]
 h' := ![![[100, 162], [38, 27], [7, 49], [5, 36], [27, 72], [64, 63], [43, 100], [0, 1]], ![[0, 1], [130, 136], [17, 114], [19, 127], [55, 91], [7, 100], [100, 63], [100, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [158]]
 b := ![[], [125, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [120, 63, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![76900, -85043, 96926, 66887, -372510]
  a := ![59, -60, 177, 116, -528]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-81098, 84710, 96926, 66887, -372510]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -8, -7, -3, 10]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![3, -8, -7, -3, 10]] 
 ![![163, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![138, 0, 1, 0, 0], ![125, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![3, -8, -7, -3, 10], ![6, -10, -7, -2, -4], ![4, 8, 12, 7, -56], ![-14, 67, 71, 33, -154], ![-6, 31, 32, 15, -73]]]
  hmulB := by decide  
  f := ![![![759, 57, -237, -140, 578]], ![![25, 2, -8, -5, 20]], ![![644, 47, -200, -118, 488]], ![![581, 47, -184, -108, 446]], ![![38, 3, -12, -7, 29]]]
  g := ![![![8, -8, -7, -3, 10], ![8, -10, -7, -2, -4], ![-13, 8, 12, 7, -56], ![-80, 67, 71, 33, -154], ![-36, 31, 32, 15, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-81, -3, 23, 14, -58]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![-81, -3, 23, 14, -58]] 
 ![![163, 0, 0, 0, 0], ![87, 1, 0, 0, 0], ![92, 0, 1, 0, 0], ![146, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![-81, -3, 23, 14, -58], ![-28, -9, 15, 11, -38], ![-22, 21, -10, -2, 8], ![4, -32, 19, -8, 4], ![-14, -1, 4, 1, -7]]]
  hmulB := by decide  
  f := ![![![-121, 454, 437, 197, -850]], ![![-67, 248, 238, 107, -458]], ![![-72, 260, 248, 111, -468]], ![![-108, 391, 373, 167, -706]], ![![-47, 169, 161, 72, -303]]]
  g := ![![![-2, -3, 23, 14, -58], ![1, -9, 15, 11, -38], ![-7, 21, -10, -2, 8], ![12, -32, 19, -8, 4], ![0, -1, 4, 1, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2

def I163N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -21, -19, -8, 26]] i)))

def SI163N3: IdealEqSpanCertificate' Table ![![9, -21, -19, -8, 26]] 
 ![![163, 0, 0, 0, 0], ![97, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![154, 0, 0, 0, 1]] where
  M :=![![![9, -21, -19, -8, 26], ![16, -25, -17, -5, -14], ![10, 25, 38, 22, -160], ![-44, 192, 191, 88, -404], ![-18, 87, 88, 41, -195]]]
  hmulB := by decide  
  f := ![![![253, -300, 183, 127, -358]], ![![149, -174, 106, 75, -210]], ![![71, -88, 53, 32, -94]], ![![62, -73, 47, 41, -110]], ![![240, -285, 174, 121, -341]]]
  g := ![![![-5, -21, -19, -8, 26], ![34, -25, -17, -5, -14], ![121, 25, 38, 22, -160], ![195, 192, 191, 88, -404], ![99, 87, 88, 41, -195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N3 : Nat.card (O ⧸ I163N3) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N3)

lemma isPrimeI163N3 : Ideal.IsPrime I163N3 := prime_ideal_of_norm_prime hp163.out _ NI163N3
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![13, -10, 7, 11, -26]] ![![3, -8, -7, -3, 10]]
  ![![9, -17, 12, 3, -18]] where
 M := ![![![9, -17, 12, 3, -18]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![9, -17, 12, 3, -18]] ![![-81, -3, 23, 14, -58]]
  ![![-253, 300, -183, -127, 358]] where
 M := ![![![-253, 300, -183, -127, 358]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N2 : IdealMulLeCertificate' Table 
  ![![-253, 300, -183, -127, 358]] ![![9, -21, -19, -8, 26]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![-163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2, I163N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
    exact isPrimeI163N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1 ⊙ MulI163N2)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, 27, -60, -67, 190]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-29, 27, -60, -67, 190]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![0, 0, 0, 167, 0], ![6, 52, 70, 106, 1]] where
  M :=![![![-29, 27, -60, -67, 190], ![134, -286, 116, 85, -256], ![-170, 475, -369, -53, 250], ![106, -473, 346, -354, 296], ![-8, 42, 18, -30, -57]]]
  hmulB := by decide  
  f := ![![![585, 27, -174, -117, 458]], ![![234, 10, -70, -47, 184]], ![![94, 3, -29, -19, 74]], ![![38, 1, -12, -8, 28]], ![![158, 6, -48, -32, 123]]]
  g := ![![![-7, -59, -80, -121, 190], ![10, 78, 108, 163, -256], ![-10, -75, -107, -159, 250], ![-10, -95, -122, -190, 296], ![2, 18, 24, 36, -57]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 4 2 7 [95, 105, 51, 79, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 53, 159, 64], [106, 11, 45, 6], [135, 102, 130, 97], [0, 1]]
 g := ![![[144, 22, 95, 7], [94, 9, 113, 94], [74, 54, 26, 108], [148, 97, 7], [111, 116, 121], [88, 1], []], ![[28, 72, 24, 152, 80, 132], [65, 142, 52, 28, 127, 49], [111, 166, 2, 133, 43, 7], [110, 164, 114], [159, 120, 63], [34, 9, 76, 105, 15, 115], [35, 40, 88]], ![[66, 81, 146, 154, 17, 89], [54, 132, 96, 162, 120, 128], [27, 49, 12, 153, 57, 14], [145, 108, 65], [15, 28, 36], [50, 70, 148, 75, 93, 137], [140, 34, 36]], ![[87, 2, 93, 163, 71, 137], [90, 112, 163, 26, 108, 127], [121, 8, 5, 41, 83, 84], [119, 50, 100], [10, 150, 14], [29, 112, 81, 83, 142, 4], [4, 9, 57]]]
 h' := ![![[14, 53, 159, 64], [88, 52, 88, 72], [151, 140, 48, 42], [66, 164, 117, 38], [76, 31, 21, 95], [157, 17, 83, 11], [0, 0, 1], [0, 1]], ![[106, 11, 45, 6], [136, 17, 106, 51], [9, 116, 58, 20], [79, 58, 83, 158], [141, 158, 117, 92], [160, 141, 6, 49], [44, 21, 97, 92], [14, 53, 159, 64]], ![[135, 102, 130, 97], [88, 24, 30, 133], [63, 52, 4, 54], [102, 109, 30, 15], [163, 99, 49, 137], [98, 17, 128, 6], [107, 100, 40, 50], [106, 11, 45, 6]], ![[0, 1], [34, 74, 110, 78], [58, 26, 57, 51], [107, 3, 104, 123], [35, 46, 147, 10], [22, 159, 117, 101], [143, 46, 29, 25], [135, 102, 130, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [119, 56, 103], []]
 b := ![[], [], [32, 29, 141, 122], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 4
  hpos := by decide
  P := [95, 105, 51, 79, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1794511, -1789742, 2716206, 1445578, -9434482]
  a := ![4, -3, 13, 8, -35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![349709, 2926966, 3970838, 5997010, -9434482]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 777796321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-585, -27, 174, 117, -458]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-585, -27, 174, 117, -458]] 
 ![![167, 0, 0, 0, 0], ![91, 1, 0, 0, 0], ![69, 0, 1, 0, 0], ![67, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-585, -27, 174, 117, -458], ![-234, -10, 70, 47, -184], ![-94, -3, 29, 19, -74], ![-38, -1, 12, 8, -28], ![-100, -4, 30, 20, -77]]]
  hmulB := by decide  
  f := ![![![29, -27, 60, 67, -190]], ![![15, -13, 32, 36, -102]], ![![13, -14, 27, 28, -80]], ![![11, -8, 22, 29, -78]], ![![3, -3, 6, 7, -19]]]
  g := ![![![-61, -27, 174, 117, -458], ![-25, -10, 70, 47, -184], ![-11, -3, 29, 19, -74], ![-5, -1, 12, 8, -28], ![-11, -4, 30, 20, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-29, 27, -60, -67, 190]] ![![-585, -27, 174, 117, -458]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![-167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 131, 81, 52, -280]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-21, 131, 81, 52, -280]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![39, 78, 72, 27, 1]] where
  M :=![![![-21, 131, 81, 52, -280], ![-104, 311, 327, 101, -464], ![-202, 461, 532, 286, -502], ![-572, 586, -537, -396, 2638], ![-190, 139, -58, -65, 869]]]
  hmulB := by decide  
  f := ![![![-3679, -170, 1093, 735, -2876]], ![![-1470, -68, 437, 294, -1150]], ![![-588, -26, 174, 117, -458]], ![![-234, -13, 71, 47, -184]], ![![-1777, -82, 528, 355, -1389]]]
  g := ![![![63, 127, 117, 44, -280], ![104, 211, 195, 73, -464], ![112, 229, 212, 80, -502], ![-598, -1186, -1101, -414, 2638], ![-197, -391, -362, -136, 869]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 4 2 7 [17, 123, 87, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 130, 172, 124], [127, 16, 166, 85], [146, 26, 8, 137], [0, 1]]
 g := ![![[169, 166, 9, 84], [123, 118, 167], [78, 95, 93, 151], [72, 159, 9, 139], [102, 47, 38], [168, 1], []], ![[50, 162, 107, 52, 59, 33], [126, 91, 144], [116, 42, 12, 101, 95, 139], [0, 127, 99, 45, 130, 136], [39, 120, 95], [130, 90, 149, 21, 91, 118], [10, 30, 152]], ![[143, 167, 69, 132, 164, 73], [32, 9, 90], [133, 11, 148, 19, 158, 31], [131, 134, 71, 61, 22, 25], [161, 119, 51], [73, 118, 15, 106, 33, 88], [16, 53, 132]], ![[64, 4, 163, 49, 53, 157], [38, 81, 81], [115, 92, 89, 132, 151, 22], [6, 83, 43, 19, 103, 96], [101, 95, 113], [75, 123, 5, 108, 104, 6], [127, 37, 85]]]
 h' := ![![[68, 130, 172, 124], [62, 71, 125, 55], [58, 32, 164, 72], [160, 154, 111, 155], [128, 85, 38, 73], [85, 79, 139, 111], [0, 0, 1], [0, 1]], ![[127, 16, 166, 85], [56, 131, 102, 58], [45, 14, 132, 161], [123, 52, 22, 167], [147, 5, 10, 95], [34, 65, 43, 21], [129, 24, 105, 92], [68, 130, 172, 124]], ![[146, 26, 8, 137], [111, 79, 88, 3], [89, 107, 23, 104], [124, 90, 104, 27], [65, 44, 31, 53], [42, 75, 52, 140], [114, 157, 87, 93], [127, 16, 166, 85]], ![[0, 1], [40, 65, 31, 57], [101, 20, 27, 9], [158, 50, 109, 170], [4, 39, 94, 125], [67, 127, 112, 74], [127, 165, 153, 161], [146, 26, 8, 137]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [167, 70, 123], []]
 b := ![[], [], [167, 53, 74, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 4
  hpos := by decide
  P := [17, 123, 87, 5, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1828943531, -2651654412, 657583356, 949892302, -5495015666]
  a := ![-26, 23, -80, -56, 235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1249332685, 2462194032, 2290743996, 863094308, -5495015666]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 895745041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3679, -170, 1093, 735, -2876]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-3679, -170, 1093, 735, -2876]] 
 ![![173, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![81, 0, 1, 0, 0], ![154, 0, 0, 1, 0], ![131, 0, 0, 0, 1]] where
  M :=![![![-3679, -170, 1093, 735, -2876], ![-1470, -68, 437, 294, -1150], ![-588, -26, 174, 117, -458], ![-234, -13, 71, 47, -184], ![-626, -29, 186, 125, -489]]]
  hmulB := by decide  
  f := ![![![-21, 131, 81, 52, -280]], ![![-4, 23, 15, 9, -48]], ![![-11, 64, 41, 26, -134]], ![![-22, 120, 69, 44, -234]], ![![-17, 100, 61, 39, -207]]]
  g := ![![![1018, -170, 1093, 735, -2876], ![407, -68, 437, 294, -1150], ![162, -26, 174, 117, -458], ![65, -13, 71, 47, -184], ![173, -29, 186, 125, -489]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-21, 131, 81, 52, -280]] ![![-3679, -170, 1093, 735, -2876]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)


lemma PB175I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 174 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 174 (by omega)

def PB175I4 : PrimesBelowBoundCertificateInterval O 151 174 175 where
  m := 4
  g := ![2, 4, 2, 2]
  P := ![157, 163, 167, 173]
  hP := PB175I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2, I163N3]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![607573201, 157]
    · exact ![26569, 163, 163, 163]
    · exact ![777796321, 167]
    · exact ![895745041, 173]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
      exact NI163N3
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
  β := ![I157N1, I163N1, I163N2, I163N3, I167N1, I173N1]
  Il := ![[I157N1], [I163N1, I163N2, I163N3], [I167N1], [I173N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
