
import IdealArithmetic.Examples.NF3_1_866700_5.RI3_1_866700_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![13, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![13, 1, 0]] 
 ![![197, 0, 0], ![13, 1, 0], ![26, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![13, 1, 0], ![-6, 19, 13], ![182, 0, 7]]]
  hmulB := by decide  
  f := ![![![78365, -248996, -170352], ![3940, 2581488, 0]], ![![5158, -16418, -11232], ![395, 170208, 0]], ![![10335, -32863, -22483], ![635, 340704, 0]]]
  g := ![![![1, 0, 0], ![-13, 197, 0], ![-26, 0, 197]], ![![0, 1, 0], ![-3, 19, 13], ![0, 0, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![39, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![39, 1, 0]] 
 ![![197, 0, 0], ![39, 1, 0], ![107, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![39, 1, 0], ![-6, 45, 13], ![182, 0, 33]]]
  hmulB := by decide  
  f := ![![![84325, -652388, -188448], ![13396, 2855712, 0]], ![![16668, -129119, -37297], ![2759, 565193, 0]], ![![45790, -354343, -102355], ![7331, 1551072, 0]]]
  g := ![![![1, 0, 0], ![-39, 197, 0], ![-107, 0, 197]], ![![0, 1, 0], ![-16, 45, 13], ![-17, 0, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![777, 97, 63]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![777, 97, 63]] 
 ![![197, 0, 0], ![145, 1, 0], ![58, 0, 1]] where
  M :=![![![777, 97, 63], ![10884, 1359, 883], ![7070, 882, 573]]]
  hmulB := by decide  
  f := ![![![-99, -15, 34]], ![![-41, -12, 23]], ![![-72, -2, 11]]]
  g := ![![![-86, 97, 63], ![-1205, 1359, 883], ![-782, 882, 573]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![13, 1, 0]] ![![197, 0, 0], ![39, 1, 0]]
  ![![99, 15, -34]] where
 M := ![![![38809, 0, 0], ![7683, 197, 0]], ![![2561, 197, 0], ![501, 58, 13]]]
 hmul := by decide  
 g := ![![![![-153069, -19109, -12411]], ![![-41187, -5142, -3340]]], ![![![-20985, -2620, -1702]], ![![-5647, -705, -458]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![99, 15, -34]] ![![777, 97, 63]]
  ![![197, 0, 0]] where
 M := ![![![-197, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0]] 
 ![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [71, 49, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [181, 27, 144], [157, 171, 55], [0, 1]]
 g := ![![[146, 42, 57], [117, 181, 132], [92, 157, 172], [94, 157], [65, 172], [24, 18], [1]], ![[178, 135, 76, 91], [183, 38, 171, 90], [76, 111, 98, 104], [35, 23], [198, 23], [33, 9], [160, 105, 119, 188]], ![[150, 82, 8, 41], [74, 18, 7, 134], [23, 180, 116, 194], [76, 45], [89, 70], [161, 188], [48, 15, 159, 11]]]
 h' := ![![[181, 27, 144], [51, 153, 183], [35, 119, 172], [75, 34, 157], [88, 75, 82], [153, 126, 42], [128, 150, 139], [0, 1]], ![[157, 171, 55], [98, 14, 192], [70, 59, 181], [174, 36, 102], [79, 165, 146], [159, 105, 53], [121, 4, 196], [181, 27, 144]], ![[0, 1], [64, 32, 23], [194, 21, 45], [102, 129, 139], [181, 158, 170], [172, 167, 104], [114, 45, 63], [157, 171, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [193, 122], []]
 b := ![[], [120, 196, 118], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [71, 49, 60, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5324245, -43183, -80197]
  a := ![6, -7, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26755, -217, -403]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def PBC199 : ContainsPrimesAboveP 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![199, 0, 0]]) timesTableT_eq_Table B_one_repr 199 (by decide) 𝕀

instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![51, 37, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![51, 37, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![51, 37, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![51, 37, 1], ![-40, 273, 475], ![6566, 14, -165]]]
  hmulB := by decide  
  f := ![![![-50, -37, -1], ![211, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -37, 211]], ![![0, 0, 1], ![-115, -82, 475], ![71, 29, -165]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [83, 199, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 210], [0, 1]]
 g := ![![[99, 150], [193, 107], [1], [180], [50, 182], [134], [12, 1]], ![[0, 61], [0, 104], [1], [180], [124, 29], [134], [24, 210]]]
 h' := ![![[12, 210], [17, 192], [65, 188], [88, 1], [70, 179], [166, 155], [59, 61], [0, 1]], ![[0, 1], [0, 19], [0, 23], [100, 210], [108, 32], [127, 56], [158, 150], [12, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [184, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [83, 199, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-32727, 13306, 7488]
  a := ![-13, 10, 28]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1965, -1250, 7488]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-53, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-53, 1, 0]] 
 ![![211, 0, 0], ![158, 1, 0], ![165, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-53, 1, 0], ![-6, -47, 13], ![182, 0, -59]]]
  hmulB := by decide  
  f := ![![![126217, 1041129, -287937], ![-26586, 4673439, 0]], ![![94529, 779589, -215605], ![-19833, 3499435, 0]], ![![98701, 814153, -225164], ![-20788, 3654585, 0]]]
  g := ![![![1, 0, 0], ![-158, 211, 0], ![-165, 0, 211]], ![![-1, 1, 0], ![25, -47, 13], ![47, 0, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![51, 37, 1]] ![![211, 0, 0], ![-53, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-11183, 211, 0]], ![![10761, 7807, 211], ![-2743, -1688, 422]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-53, 1, 0]]], ![![![51, 37, 1]], ![![-13, -8, 2]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0]] 
 ![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [2, 97, 202, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [196, 214, 40], [48, 8, 183], [0, 1]]
 g := ![![[125, 151, 100], [142, 25, 128], [57, 197, 68], [164, 128, 63], [78, 213, 166], [58, 218], [1]], ![[115, 48, 37, 170], [100, 68, 155, 75], [76, 118, 172, 77], [212, 77, 150, 77], [182, 179, 76, 97], [123, 220], [111, 160, 41, 222]], ![[70, 88, 216, 36], [91, 204, 138, 17], [105, 60, 193, 131], [139, 160, 159, 120], [88, 128, 72, 175], [66, 188], [174, 96, 65, 1]]]
 h' := ![![[196, 214, 40], [162, 64, 213], [109, 196, 103], [118, 144, 108], [67, 92, 145], [111, 124, 101], [221, 126, 21], [0, 1]], ![[48, 8, 183], [37, 167, 27], [4, 16, 190], [58, 1, 157], [96, 106, 157], [219, 99, 193], [165, 4, 79], [196, 214, 40]], ![[0, 1], [53, 215, 206], [112, 11, 153], [219, 78, 181], [98, 25, 144], [125, 0, 152], [82, 93, 123], [48, 8, 183]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 15], []]
 b := ![[], [174, 48, 139], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [2, 97, 202, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-937233817290, -32183991313, -18002708159]
  a := ![326, -389, -717]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4202842230, -144322831, -80729633]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def PBC223 : ContainsPrimesAboveP 223 ![I223N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![223, 0, 0]]) timesTableT_eq_Table B_one_repr 223 (by decide) 𝕀

instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0]] 
 ![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [132, 82, 129, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [143, 111, 112], [182, 115, 115], [0, 1]]
 g := ![![[207, 6, 25], [60, 18, 25], [143, 173], [114, 25], [127, 81], [85, 95, 70], [1]], ![[150, 113, 66, 59], [60, 49, 198, 113], [127, 159], [187, 103], [8, 182], [3, 135, 207, 64], [141, 90, 78, 25]], ![[47, 81, 200, 142], [151, 195, 173, 61], [169, 76], [7, 75], [218, 78], [101, 209, 191, 198], [168, 119, 199, 202]]]
 h' := ![![[143, 111, 112], [25, 199, 222], [225, 107, 222], [43, 221, 20], [136, 175, 5], [130, 184, 9], [95, 145, 98], [0, 1]], ![[182, 115, 115], [218, 92, 148], [201, 95, 59], [103, 154, 39], [80, 108, 199], [1, 136, 78], [222, 137, 43], [143, 111, 112]], ![[0, 1], [55, 163, 84], [82, 25, 173], [12, 79, 168], [74, 171, 23], [193, 134, 140], [199, 172, 86], [182, 115, 115]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [221, 192], []]
 b := ![[], [150, 168, 128], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [132, 82, 129, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-55276770, 362065, 921620]
  a := ![13, -11, -28]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-243510, 1595, 4060]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def PBC227 : ContainsPrimesAboveP 227 ![I227N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![227, 0, 0]]) timesTableT_eq_Table B_one_repr 227 (by decide) 𝕀

instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![90, 75, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![90, 75, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![90, 75, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![90, 75, 1], ![-268, 540, 969], ![13482, 14, -354]]]
  hmulB := by decide  
  f := ![![![-89, -75, -1], ![229, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-90, -75, 229]], ![![0, 0, 1], ![-382, -315, 969], ![198, 116, -354]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [36, 175, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 228], [0, 1]]
 g := ![![[113, 70], [181], [115, 57], [46], [196], [137, 20], [54, 1]], ![[0, 159], [181], [216, 172], [46], [196], [72, 209], [108, 228]]]
 h' := ![![[54, 228], [220, 191], [211, 69], [105, 168], [58, 59], [106, 215], [117, 132], [0, 1]], ![[0, 1], [0, 38], [44, 160], [17, 61], [38, 170], [37, 14], [146, 97], [54, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [174, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [36, 175, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5560, 1351, -1872]
  a := ![6, -7, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![760, 619, -1872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-53, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-53, 1, 0]] 
 ![![229, 0, 0], ![176, 1, 0], ![125, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-53, 1, 0], ![-6, -47, 13], ![182, 0, -59]]]
  hmulB := by decide  
  f := ![![![4973, 40612, -11232], ![-916, 197856, 0]], ![![3826, 31211, -8632], ![-686, 152056, 0]], ![![2721, 22168, -6131], ![-472, 108000, 0]]]
  g := ![![![1, 0, 0], ![-176, 229, 0], ![-125, 0, 229]], ![![-1, 1, 0], ![29, -47, 13], ![33, 0, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![90, 75, 1]] ![![229, 0, 0], ![-53, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-12137, 229, 0]], ![![20610, 17175, 229], ![-5038, -3435, 916]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-53, 1, 0]]], ![![![90, 75, 1]], ![![-22, -15, 4]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![0, 1, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![0, 1, 0]] 
 ![![233, 0, 0], ![0, 1, 0], ![125, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![0, 1, 0], ![-6, 6, 13], ![182, 0, -6]]]
  hmulB := by decide  
  f := ![![![-233, 233, 507], ![233, -9087, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-125, 125, 272], ![125, -4875, 0]]]
  g := ![![![1, 0, 0], ![0, 233, 0], ![-125, 0, 233]], ![![0, 1, 0], ![-7, 6, 13], ![4, 0, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N0 : Nat.card (O ⧸ I233N0) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N0)

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := prime_ideal_of_norm_prime hp233.out _ NI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![27, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![27, 1, 0]] 
 ![![233, 0, 0], ![27, 1, 0], ![164, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![27, 1, 0], ![-6, 33, 13], ![182, 0, 21]]]
  hmulB := by decide  
  f := ![![![72034, -400517, -157768], ![6757, 2827688, 0]], ![![8328, -46402, -18278], ![933, 327598, 0]], ![![50701, -281909, -111047], ![4765, 1990304, 0]]]
  g := ![![![1, 0, 0], ![-27, 233, 0], ![-164, 0, 233]], ![![0, 1, 0], ![-13, 33, 13], ![-14, 0, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2355, 294, 191]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![2355, 294, 191]] 
 ![![233, 0, 0], ![206, 1, 0], ![171, 0, 1]] where
  M :=![![![2355, 294, 191], ![32998, 4119, 2676], ![21420, 2674, 1737]]]
  hmulB := by decide  
  f := ![![![-921, 56, 15]], ![![-804, 47, 16]], ![![-643, 42, 6]]]
  g := ![![![-390, 294, 191], ![-5464, 4119, 2676], ![-3547, 2674, 1737]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![0, 1, 0]] ![![233, 0, 0], ![27, 1, 0]]
  ![![921, -56, -15]] where
 M := ![![![54289, 0, 0], ![6291, 233, 0]], ![![0, 233, 0], ![-6, 33, 13]]]
 hmul := by decide  
 g := ![![![![-548715, -68502, -44503]], ![![-96583, -12057, -7833]]], ![![![-32998, -4119, -2676]], ![![-5808, -725, -471]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![921, -56, -15]] ![![2355, 294, 191]]
  ![![233, 0, 0]] where
 M := ![![![-233, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1, I233N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
    exact isPrimeI233N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0 ⊙ MulI233N1)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0]] 
 ![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [228, 84, 128, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 54, 84], [108, 184, 155], [0, 1]]
 g := ![![[22, 132, 1], [135, 216, 12], [41, 93, 102], [120, 19, 2], [82, 197], [111, 67, 132], [1]], ![[3, 95, 152, 172], [165, 130, 213, 151], [78, 68, 151, 59], [227, 89, 177, 227], [141, 134], [145, 6, 143, 233], [117, 219, 71, 223]], ![[209, 158, 34, 145], [111, 176, 209, 183], [201, 199, 191, 58], [127, 212, 103, 201], [79, 15], [93, 146, 74, 8], [176, 37, 32, 16]]]
 h' := ![![[3, 54, 84], [51, 130, 1], [212, 59, 27], [125, 110, 113], [144, 65, 140], [26, 138, 83], [11, 155, 111], [0, 1]], ![[108, 184, 155], [5, 102, 110], [89, 191, 125], [182, 0, 157], [5, 72, 150], [102, 166, 96], [119, 14, 223], [3, 54, 84]], ![[0, 1], [151, 7, 128], [176, 228, 87], [84, 129, 208], [68, 102, 188], [91, 174, 60], [206, 70, 144], [108, 184, 155]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [161, 64], []]
 b := ![[], [33, 83, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [228, 84, 128, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![85141121, 11388589, 7935995]
  a := ![-11, 31, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![356239, 47651, 33205]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def PBC239 : ContainsPrimesAboveP 239 ![I239N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![239, 0, 0]]) timesTableT_eq_Table B_one_repr 239 (by decide) 𝕀

instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0]] 
 ![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [236, 114, 111, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [216, 152, 229], [155, 88, 12], [0, 1]]
 g := ![![[236, 8, 75], [204, 113], [145, 125], [71, 141], [149, 206, 3], [116, 47, 30], [1]], ![[166, 106, 106, 6], [188, 64], [87, 29], [236, 36], [141, 55, 134, 5], [226, 211, 150, 1], [214, 162, 84, 200]], ![[130, 41, 207, 221], [16, 133], [2, 201], [16, 209], [223, 78, 60, 87], [236, 225, 111, 145], [18, 214, 207, 41]]]
 h' := ![![[216, 152, 229], [54, 147, 39], [203, 61, 63], [116, 154, 33], [22, 155, 158], [98, 50, 56], [5, 127, 130], [0, 1]], ![[155, 88, 12], [73, 23, 222], [196, 207, 233], [22, 183, 92], [218, 49, 235], [117, 51, 231], [146, 170, 35], [216, 152, 229]], ![[0, 1], [96, 71, 221], [4, 214, 186], [200, 145, 116], [19, 37, 89], [70, 140, 195], [33, 185, 76], [155, 88, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [211, 6], []]
 b := ![[], [112, 230, 121], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [236, 114, 111, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34961870, 266787, 711432]
  a := ![11, -9, -24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-145070, 1107, 2952]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 13997521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0]] 
 ![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [249, 132, 131, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [248, 128, 1], [123, 122, 250], [0, 1]]
 g := ![![[124, 238, 105], [156, 56, 85], [238, 197], [124, 7, 155], [155, 116, 125], [16, 62, 93], [1]], ![[184, 155, 216, 211], [140, 247, 161, 233], [203, 211], [130, 223, 27, 89], [148, 25, 42, 48], [137, 0, 183, 241], [65, 55, 2, 1]], ![[20, 168, 65, 231], [15, 245, 121, 130], [1, 225], [166, 157, 243, 107], [93, 12, 173, 24], [218, 211, 81, 120], [117, 178, 246, 250]]]
 h' := ![![[248, 128, 1], [61, 140, 119], [234, 32, 218], [248, 179, 166], [59, 123, 54], [32, 24, 171], [2, 119, 120], [0, 1]], ![[123, 122, 250], [91, 131, 100], [125, 88, 22], [35, 84, 100], [122, 32, 185], [73, 87, 53], [103, 6, 201], [248, 128, 1]], ![[0, 1], [247, 231, 32], [37, 131, 11], [81, 239, 236], [0, 96, 12], [236, 140, 27], [187, 126, 181], [123, 122, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 239], []]
 b := ![[], [192, 211, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [249, 132, 131, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![45184769, 2688712, 668915]
  a := ![-12, 13, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![180019, 10712, 2665]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def PBC251 : ContainsPrimesAboveP 251 ![I251N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![251, 0, 0]]) timesTableT_eq_Table B_one_repr 251 (by decide) 𝕀

instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-50, -7, 1]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-50, -7, 1]] 
 ![![257, 0, 0], ![0, 257, 0], ![207, 250, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-50, -7, 1], ![224, -92, -97], ![-1442, 14, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-207, -250, 257]], ![![-1, -1, 1], ![79, 94, -97], ![-4, 2, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [22, 216, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 256], [0, 1]]
 g := ![![[150, 222], [198], [67], [49], [4], [58], [139], [1]], ![[0, 35], [198], [67], [49], [4], [58], [139], [1]]]
 h' := ![![[41, 256], [77, 42], [8, 202], [222, 18], [23, 7], [25, 2], [253, 40], [235, 41], [0, 1]], ![[0, 1], [0, 215], [66, 55], [189, 239], [53, 250], [107, 255], [94, 217], [117, 216], [41, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [26, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [22, 216, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![93047, 39770, -4580]
  a := ![25, -30, -55]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4051, 4610, -4580]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![97, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![97, 1, 0]] 
 ![![257, 0, 0], ![97, 1, 0], ![2, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![97, 1, 0], ![-6, 103, 13], ![182, 0, 91]]]
  hmulB := by decide  
  f := ![![![43293, -829820, -104728], ![13364, 2070392, 0]], ![![16300, -313140, -39520], ![5141, 781280, 0]], ![![312, -6458, -815], ![170, 16112, 0]]]
  g := ![![![1, 0, 0], ![-97, 257, 0], ![-2, 0, 257]], ![![0, 1, 0], ![-39, 103, 13], ![0, 0, 91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![-50, -7, 1]] ![![257, 0, 0], ![97, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![24929, 257, 0]], ![![-12850, -1799, 257], ![-4626, -771, 0]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![97, 1, 0]]], ![![![-50, -7, 1]], ![![-18, -3, 0]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0)


lemma PB264I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB264I4 : PrimesBelowBoundCertificateInterval O 193 257 264 where
  m := 11
  g := ![3, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB264I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0]
    · exact ![I241N0]
    · exact ![I251N0]
    · exact ![I257N0, I257N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
    · exact PBC257
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![197, 197, 197]
    · exact ![7880599]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![11697083]
    · exact ![52441, 229]
    · exact ![233, 233, 233]
    · exact ![13651919]
    · exact ![13997521]
    · exact ![15813251]
    · exact ![66049, 257]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
      exact NI233N2
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
  β := ![I197N0, I197N1, I197N2, I211N1, I229N1, I233N0, I233N1, I233N2, I257N1]
  Il := ![[I197N0, I197N1, I197N2], [], [I211N1], [], [], [I229N1], [I233N0, I233N1, I233N2], [], [], [], [I257N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
