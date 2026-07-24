
import IdealArithmetic.Examples.NF3_1_959175_2.RI3_1_959175_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-64, 93, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-64, 93, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![133, 93, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-64, 93, 1], ![-280, -258, 1211], ![17265, -731, 115]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-133, -93, 197]], ![![-1, 0, 1], ![-819, -573, 1211], ![10, -58, 115]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [52, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 196], [0, 1]]
 g := ![![[55, 154], [157], [64, 193], [39], [156], [41], [95, 1]], ![[107, 43], [157], [78, 4], [39], [156], [41], [190, 196]]]
 h' := ![![[95, 196], [157, 96], [21, 74], [175, 169], [191, 32], [63, 64], [182, 108], [0, 1]], ![[0, 1], [18, 101], [156, 123], [76, 28], [79, 165], [36, 133], [1, 89], [95, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115]]
 b := ![[], [76, 156]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [52, 102, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5912, 2515, -2678]
  a := ![5, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1838, 1277, -2678]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-29, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-29, 1, 0]] 
 ![![197, 0, 0], ![168, 1, 0], ![82, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-29, 1, 0], ![-5, -31, 13], ![185, -8, -27]]]
  hmulB := by decide  
  f := ![![![118620, 747913, -313612], ![-13593, 4752428, 0]], ![![101150, 637791, -267436], ![-11622, 4052684, 0]], ![![49376, 311314, -130539], ![-5650, 1978168, 0]]]
  g := ![![![1, 0, 0], ![-168, 197, 0], ![-82, 0, 197]], ![![-1, 1, 0], ![21, -31, 13], ![19, -8, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-64, 93, 1]] ![![197, 0, 0], ![-29, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-5713, 197, 0]], ![![-12608, 18321, 197], ![1576, -2955, 1182]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-29, 1, 0]]], ![![![-64, 93, 1]], ![![8, -15, 6]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [53, 143, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [109, 100, 43], [186, 98, 156], [0, 1]]
 g := ![![[43, 168, 58], [82, 61, 5], [109, 134, 158], [152, 178], [72, 151], [187, 62], [1]], ![[189, 138, 70, 126], [174, 181, 119, 81], [176, 39, 1, 20], [73, 157], [129, 116], [20, 53], [146, 108, 114, 106]], ![[163, 140, 123, 60], [14, 179, 158, 174], [137, 29, 39, 189], [15, 92], [116, 64], [69, 187], [189, 32, 110, 93]]]
 h' := ![![[109, 100, 43], [32, 2, 43], [193, 119, 76], [91, 197, 77], [28, 187, 175], [62, 56, 56], [146, 56, 96], [0, 1]], ![[186, 98, 156], [173, 49, 121], [42, 105, 28], [147, 159, 97], [193, 32, 117], [142, 72, 135], [159, 75, 75], [109, 100, 43]], ![[0, 1], [3, 148, 35], [117, 174, 95], [107, 42, 25], [107, 179, 106], [177, 71, 8], [124, 68, 28], [186, 98, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 88], []]
 b := ![[], [140, 16, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [53, 143, 103, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![86100136, -5670107, -86963]
  a := ![-12, -7, 31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![432664, -28493, -437]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-40, -21, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-40, -21, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![171, 190, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-40, -21, 1], ![290, -6, -271], ![-3825, 181, -89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-171, -190, 211]], ![![-1, -1, 1], ![221, 244, -271], ![54, 81, -89]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [7, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [168, 210], [0, 1]]
 g := ![![[187, 208], [30, 173], [81], [53], [158, 173], [84], [168, 1]], ![[105, 3], [187, 38], [81], [53], [104, 38], [84], [125, 210]]]
 h' := ![![[168, 210], [1, 29], [118, 54], [120, 202], [160, 106], [127, 54], [90, 154], [0, 1]], ![[0, 1], [20, 182], [117, 157], [85, 9], [33, 105], [126, 157], [9, 57], [168, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [184]]
 b := ![[], [79, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [7, 43, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3547592, 4166226, -2241143]
  a := ![197, 67, -525]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1833095, 2037836, -2241143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![60, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![60, 1, 0]] 
 ![![211, 0, 0], ![60, 1, 0], ![89, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![60, 1, 0], ![-5, 58, 13], ![185, -8, 62]]]
  hmulB := by decide  
  f := ![![![6211, -76915, -17238], ![1477, 279786, 0]], ![![1765, -21868, -4901], ![423, 79547, 0]], ![![2609, -32443, -7271], ![661, 118014, 0]]]
  g := ![![![1, 0, 0], ![-60, 211, 0], ![-89, 0, 211]], ![![0, 1, 0], ![-22, 58, 13], ![-23, -8, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-40, -21, 1]] ![![211, 0, 0], ![60, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![12660, 211, 0]], ![![-8440, -4431, 211], ![-2110, -1266, -211]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![60, 1, 0]]], ![![![-40, -21, 1]], ![![-10, -6, -1]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![4, 1, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![4, 1, 0]] 
 ![![223, 0, 0], ![4, 1, 0], ![222, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![4, 1, 0], ![-5, 2, 13], ![185, -8, 6]]]
  hmulB := by decide  
  f := ![![![9517, -3809, -24752], ![223, 424592, 0]], ![![166, -69, -442], ![224, 7582, 0]], ![![9474, -3792, -24641], ![240, 422688, 0]]]
  g := ![![![1, 0, 0], ![-4, 223, 0], ![-222, 0, 223]], ![![0, 1, 0], ![-13, 2, 13], ![-5, -8, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N0 : Nat.card (O ⧸ I223N0) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N0)

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := prime_ideal_of_norm_prime hp223.out _ NI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, 1, 2]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-33, 1, 2]] 
 ![![223, 0, 0], ![36, 1, 0], ![77, 0, 1]] where
  M :=![![![-33, 1, 2], ![365, -51, 17], ![305, 18, -45]]]
  hmulB := by decide  
  f := ![![![1989, 81, 119]], ![![418, 17, 25]], ![![786, 32, 47]]]
  g := ![![![-1, 1, 2], ![4, -51, 17], ![14, 18, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-40, 1, 0]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-40, 1, 0]] 
 ![![223, 0, 0], ![183, 1, 0], ![162, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-40, 1, 0], ![-5, -42, 13], ![185, -8, -38]]]
  hmulB := by decide  
  f := ![![![-16329, -140879, 43602], ![2453, -747942, 0]], ![![-13399, -115593, 35776], ![2008, -613696, 0]], ![![-11846, -102343, 31675], ![1873, -543348, 0]]]
  g := ![![![1, 0, 0], ![-183, 223, 0], ![-162, 0, 223]], ![![-1, 1, 0], ![25, -42, 13], ![35, -8, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![4, 1, 0]] ![![-33, 1, 2]]
  ![![223, 0, 0], ![45, -100, 1]] where
 M := ![![![-7359, 223, 446]], ![![233, -47, 25]]]
 hmul := by decide  
 g := ![![![![-33, 1, 2], ![0, 0, 0]]], ![![![-4, 11, 0], ![25, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![45, -100, 1]] ![![223, 0, 0], ![-40, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![-8920, 223, 0]], ![![10035, -22300, 223], ![-1115, 4237, -1338]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![-40, 1, 0]]], ![![![45, -100, 1]], ![![-5, 19, -6]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-108, -109, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-108, -109, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![119, 118, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-108, -109, 1], ![730, 102, -1415], ![-20105, 885, -333]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-119, -118, 227]], ![![-1, -1, 1], ![745, 736, -1415], ![86, 177, -333]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [134, 209, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 226], [0, 1]]
 g := ![![[132, 144], [5, 221], [172], [30], [97], [192, 7], [18, 1]], ![[0, 83], [124, 6], [172], [30], [97], [91, 220], [36, 226]]]
 h' := ![![[18, 226], [11, 12], [88, 69], [182, 132], [195, 205], [150, 209], [85, 190], [0, 1]], ![[0, 1], [0, 215], [195, 158], [61, 95], [26, 22], [53, 18], [100, 37], [18, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [92, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [134, 209, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8554, 16795, -14226]
  a := ![12, 6, -31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7420, 7469, -14226]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![53, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![53, 1, 0]] 
 ![![227, 0, 0], ![53, 1, 0], ![106, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![53, 1, 0], ![-5, 51, 13], ![185, -8, 55]]]
  hmulB := by decide  
  f := ![![![-13816, 146891, 37440], ![-2497, -653760, 0]], ![![-3254, 34274, 8736], ![-453, -152544, 0]], ![![-6466, 68592, 17483], ![-1104, -305280, 0]]]
  g := ![![![1, 0, 0], ![-53, 227, 0], ![-106, 0, 227]], ![![0, 1, 0], ![-18, 51, 13], ![-23, -8, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-108, -109, 1]] ![![227, 0, 0], ![53, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![12031, 227, 0]], ![![-24516, -24743, 227], ![-4994, -5675, -1362]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![53, 1, 0]]], ![![![-108, -109, 1]], ![![-22, -25, -6]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-44, 8, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-44, 8, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![185, 8, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-44, 8, 1], ![145, -68, 106], ![1540, -51, -35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-185, -8, 229]], ![![-1, 0, 1], ![-85, -4, 106], ![35, 1, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [197, 127, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [102, 228], [0, 1]]
 g := ![![[132, 91], [193], [226, 165], [5], [148], [28, 215], [102, 1]], ![[25, 138], [193], [110, 64], [5], [148], [203, 14], [204, 228]]]
 h' := ![![[102, 228], [49, 159], [133, 184], [146, 169], [98, 163], [209, 47], [58, 131], [0, 1]], ![[0, 1], [8, 70], [123, 45], [209, 60], [7, 66], [194, 182], [138, 98], [102, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [178, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [197, 127, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6182, 2540, -3003]
  a := ![5, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2453, 116, -3003]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-106, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-106, 1, 0]] 
 ![![229, 0, 0], ![123, 1, 0], ![35, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-106, 1, 0], ![-5, -108, 13], ![185, -8, -104]]]
  hmulB := by decide  
  f := ![![![-9479, -239127, 28782], ![3435, -507006, 0]], ![![-5096, -128420, 15457], ![1833, -272281, 0]], ![![-1427, -36548, 4399], ![572, -77490, 0]]]
  g := ![![![1, 0, 0], ![-123, 229, 0], ![-35, 0, 229]], ![![-1, 1, 0], ![56, -108, 13], ![21, -8, -104]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-44, 8, 1]] ![![229, 0, 0], ![-106, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-24274, 229, 0]], ![![-10076, 1832, 229], ![4809, -916, 0]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-106, 1, 0]]], ![![![-44, 8, 1]], ![![21, -4, 0]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-97, 24, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-97, 24, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![136, 24, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-97, 24, 1], ![65, -153, 314], ![4500, -179, -56]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-136, -24, 233]], ![![-1, 0, 1], ![-183, -33, 314], ![52, 5, -56]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [174, 218, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 232], [0, 1]]
 g := ![![[20, 60], [91], [7], [112, 31], [202], [203, 38], [15, 1]], ![[221, 173], [91], [7], [111, 202], [202], [74, 195], [30, 232]]]
 h' := ![![[15, 232], [179, 198], [13, 215], [84, 70], [17, 65], [94, 40], [186, 51], [0, 1]], ![[0, 1], [120, 35], [209, 18], [202, 163], [60, 168], [228, 193], [19, 182], [15, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [230, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [174, 218, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![147994, 3077, 5827]
  a := ![-8, 16, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2766, -587, 5827]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-81, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-81, 1, 0]] 
 ![![233, 0, 0], ![152, 1, 0], ![56, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-81, 1, 0], ![-5, -83, 13], ![185, -8, -79]]]
  hmulB := by decide  
  f := ![![![-5297, -97366, 15249], ![1631, -273309, 0]], ![![-3419, -63500, 9945], ![1166, -178245, 0]], ![![-1214, -23402, 3665], ![562, -65688, 0]]]
  g := ![![![1, 0, 0], ![-152, 233, 0], ![-56, 0, 233]], ![![-1, 1, 0], ![51, -83, 13], ![25, -8, -79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-97, 24, 1]] ![![233, 0, 0], ![-81, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-18873, 233, 0]], ![![-22601, 5592, 233], ![7922, -2097, 233]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-81, 1, 0]]], ![![![-97, 24, 1]], ![![34, -9, 1]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![117, 80, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![117, 80, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![117, 80, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![117, 80, 1], ![-215, -51, 1042], ![14860, -627, 270]]]
  hmulB := by decide  
  f := ![![![-116, -80, -1], ![239, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-117, -80, 239]], ![![0, 0, 1], ![-511, -349, 1042], ![-70, -93, 270]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [180, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [227, 238], [0, 1]]
 g := ![![[16, 81], [144, 12], [46, 9], [167, 9], [108], [52, 101], [227, 1]], ![[0, 158], [0, 227], [177, 230], [59, 230], [108], [35, 138], [215, 238]]]
 h' := ![![[227, 238], [131, 230], [85, 27], [54, 236], [6, 3], [200, 158], [9, 203], [0, 1]], ![[0, 1], [0, 9], [0, 212], [90, 3], [209, 236], [216, 81], [202, 36], [227, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [161]]
 b := ![[], [5, 200]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [180, 12, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20000, 7845, -3711]
  a := ![8, 6, -21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1733, 1275, -3711]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-86, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-86, 1, 0]] 
 ![![239, 0, 0], ![153, 1, 0], ![208, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-86, 1, 0], ![-5, -88, 13], ![185, -8, -84]]]
  hmulB := by decide  
  f := ![![![-9467, -184812, 27300], ![2868, -501900, 0]], ![![-6031, -118280, 17472], ![1913, -321216, 0]], ![![-8288, -160840, 23759], ![2360, -436800, 0]]]
  g := ![![![1, 0, 0], ![-153, 239, 0], ![-208, 0, 239]], ![![-1, 1, 0], ![45, -88, 13], ![79, -8, -84]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![117, 80, 1]] ![![239, 0, 0], ![-86, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-20554, 239, 0]], ![![27963, 19120, 239], ![-10277, -6931, 956]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-86, 1, 0]]], ![![![117, 80, 1]], ![![-43, -29, 4]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [105, 72, 179, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 78, 235], [198, 162, 6], [0, 1]]
 g := ![![[240, 155, 239], [19, 5], [142, 121], [194, 151], [206, 14, 183], [202, 209, 229], [1]], ![[240, 192, 223, 24], [146, 196], [193, 1], [104, 151], [61, 191, 95, 100], [109, 181, 36, 24], [108, 25, 93, 25]], ![[106, 39, 68, 10], [136, 193], [149, 100], [114, 122], [87, 98, 2, 9], [101, 168, 30, 108], [39, 150, 40, 216]]]
 h' := ![![[105, 78, 235], [80, 120, 203], [151, 33, 138], [100, 16, 11], [60, 90, 174], [239, 82, 119], [136, 169, 62], [0, 1]], ![[198, 162, 6], [200, 51, 113], [180, 205, 227], [116, 55, 240], [190, 177, 174], [137, 216, 229], [89, 148, 113], [105, 78, 235]], ![[0, 1], [73, 70, 166], [161, 3, 117], [83, 170, 231], [56, 215, 134], [116, 184, 134], [25, 165, 66], [198, 162, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [229, 182], []]
 b := ![[], [113, 207, 191], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [105, 72, 179, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![45138095, -2339869, 542009]
  a := ![-10, -3, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![187295, -9709, 2249]
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


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [76, 239, 108, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [156, 143, 34], [238, 107, 217], [0, 1]]
 g := ![![[64, 87, 9], [54, 117, 49], [197, 81], [119, 80, 121], [97, 160, 249], [94, 226, 118], [1]], ![[98, 186, 224, 57], [204, 169, 181, 182], [182, 89], [54, 65, 6, 182], [138, 19, 179, 130], [35, 219, 84, 29], [98, 98, 28, 148]], ![[15, 66, 28, 89], [68, 78, 135, 164], [236, 103], [63, 184, 44, 49], [237, 1, 246, 161], [173, 11, 16, 243], [2, 246, 18, 103]]]
 h' := ![![[156, 143, 34], [163, 51, 3], [152, 26, 244], [243, 232, 9], [158, 201, 240], [135, 19, 91], [175, 12, 143], [0, 1]], ![[238, 107, 217], [1, 109, 47], [58, 66, 135], [33, 78, 66], [36, 199, 135], [72, 244, 92], [123, 53, 147], [156, 143, 34]], ![[0, 1], [12, 91, 201], [209, 159, 123], [18, 192, 176], [102, 102, 127], [24, 239, 68], [161, 186, 212], [238, 107, 217]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 17], []]
 b := ![[], [239, 248, 125], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [76, 239, 108, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-157229914, 17756995, -6572435]
  a := ![15, 5, -40]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-626414, 70745, -26185]
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

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![3, 80, 1]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![3, 80, 1]] 
 ![![257, 0, 0], ![0, 257, 0], ![3, 80, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![3, 80, 1], ![-215, -165, 1042], ![14860, -627, 156]]]
  hmulB := by decide  
  f := ![![![-2, -80, -1], ![257, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -80, 257]], ![![0, 0, 1], ![-13, -325, 1042], ![56, -51, 156]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [115, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [206, 256], [0, 1]]
 g := ![![[139, 32], [134], [98], [120], [21], [199], [31], [1]], ![[49, 225], [134], [98], [120], [21], [199], [31], [1]]]
 h' := ![![[206, 256], [105, 17], [98, 52], [46, 94], [15, 190], [173, 147], [151, 126], [142, 206], [0, 1]], ![[0, 1], [9, 240], [16, 205], [135, 163], [91, 67], [129, 110], [150, 131], [173, 51], [206, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [205, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [115, 51, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-144525, 32868, -10910]
  a := ![-16, -16, 42]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-435, 3524, -10910]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-14, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-14, 1, 0]] 
 ![![257, 0, 0], ![243, 1, 0], ![101, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-14, 1, 0], ![-5, -16, 13], ![185, -8, -12]]]
  hmulB := by decide  
  f := ![![![35131, 112645, -91520], ![-1285, 1809280, 0]], ![![33211, 106501, -86528], ![-1284, 1710592, 0]], ![![13807, 44269, -35967], ![-493, 711040, 0]]]
  g := ![![![1, 0, 0], ![-243, 257, 0], ![-101, 0, 257]], ![![-1, 1, 0], ![10, -16, 13], ![13, -8, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![3, 80, 1]] ![![257, 0, 0], ![-14, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![-3598, 257, 0]], ![![771, 20560, 257], ![-257, -1285, 1028]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![-14, 1, 0]]], ![![![3, 80, 1]], ![![-1, -5, 4]]]]
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


lemma PB278I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB278I4 : PrimesBelowBoundCertificateInterval O 193 257 278 where
  m := 11
  g := ![2, 1, 2, 3, 2, 2, 2, 2, 1, 1, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB278I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
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
    · exact ![38809, 197]
    · exact ![7880599]
    · exact ![44521, 211]
    · exact ![223, 223, 223]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![54289, 233]
    · exact ![57121, 239]
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
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
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
  β := ![I197N1, I211N1, I223N0, I223N1, I223N2, I227N1, I229N1, I233N1, I239N1, I257N1]
  Il := ![[I197N1], [], [I211N1], [I223N0, I223N1, I223N2], [I227N1], [I229N1], [I233N1], [I239N1], [], [], [I257N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
