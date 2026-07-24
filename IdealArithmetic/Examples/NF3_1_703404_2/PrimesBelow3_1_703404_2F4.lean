
import IdealArithmetic.Examples.NF3_1_703404_2.RI3_1_703404_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![197, 0, 0], ![1, 1, 0], ![196, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 1, 1], ![262, 66, 1]]]
  hmulB := by decide  
  f := ![![![-65, -1, 1]], ![![1, 0, 0]], ![![-66, 0, 1]]]
  g := ![![![0, 1, 0], ![-1, 1, 1], ![0, 66, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![94, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![94, 1, 0]] 
 ![![197, 0, 0], ![94, 1, 0], ![29, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![94, 1, 0], ![0, 94, 1], ![262, 66, 94]]]
  hmulB := by decide  
  f := ![![![5547, 59, 0], ![-11623, 0, 0]], ![![2538, 27, 0], ![-5318, 0, 0]], ![![703, 7, 0], ![-1473, 1, 0]]]
  g := ![![![1, 0, 0], ![-94, 197, 0], ![-29, 0, 197]], ![![0, 1, 0], ![-45, 94, 1], ![-44, 66, 94]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-95, 1, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-95, 1, 0]] 
 ![![197, 0, 0], ![102, 1, 0], ![37, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-95, 1, 0], ![0, -95, 1], ![262, 66, -95]]]
  hmulB := by decide  
  f := ![![![8361, -88, 0], ![17336, 0, 0]], ![![4466, -47, 0], ![9260, 0, 0]], ![![1661, -17, 0], ![3444, 1, 0]]]
  g := ![![![1, 0, 0], ![-102, 197, 0], ![-37, 0, 197]], ![![-1, 1, 0], ![49, -95, 1], ![-15, 66, -95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![1, 1, 0]] ![![197, 0, 0], ![94, 1, 0]]
  ![![197, 0, 0], ![-103, -102, 1]] where
 M := ![![![197, 197, 0], ![94, 95, 1]]]
 hmul := by decide  
 g := ![![![![1, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-103, -102, 1]] ![![197, 0, 0], ![-95, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-18715, 197, 0]], ![![-20291, -20094, 197], ![10047, 9653, -197]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-95, 1, 0]]], ![![![-103, -102, 1]], ![![51, 49, -1]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [73, 121, 132, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [123, 169, 189], [143, 29, 10], [0, 1]]
 g := ![![[91, 22, 123], [15, 167, 178], [48, 182, 20], [25, 5], [70, 45], [178, 111], [1]], ![[99, 47, 158, 41], [60, 114, 75, 168], [46, 98, 43, 197], [90, 92], [171, 92], [8, 165], [134, 169, 18, 194]], ![[72, 50, 197, 123], [76, 139, 121, 187], [37, 125, 135, 43], [190, 104], [71, 158], [147, 102], [120, 51, 80, 5]]]
 h' := ![![[123, 169, 189], [99, 38, 83], [78, 124, 24], [121, 97, 152], [126, 32, 76], [96, 164, 170], [126, 78, 67], [0, 1]], ![[143, 29, 10], [49, 179, 37], [58, 42, 53], [37, 21, 55], [144, 8, 93], [182, 136, 106], [186, 53, 168], [123, 169, 189]], ![[0, 1], [180, 181, 79], [88, 33, 122], [125, 81, 191], [57, 159, 30], [71, 98, 122], [97, 68, 163], [143, 29, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 21], []]
 b := ![[], [40, 178, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [73, 121, 132, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-51541, 3383, 3383]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-259, 17, 17]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [208, 34, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 39, 112], [118, 171, 99], [0, 1]]
 g := ![![[162, 75, 71], [164, 51, 36], [210, 58], [25, 144], [86, 179, 117], [160, 208], [1]], ![[23, 75, 92, 91], [74, 13, 205, 162], [182, 173], [173, 36], [152, 45, 18, 158], [138, 163], [18, 16, 65, 90]], ![[145, 44, 53, 11], [181, 84, 12, 176], [162, 82], [156, 36], [157, 62, 83, 51], [23, 136], [136, 26, 72, 121]]]
 h' := ![![[64, 39, 112], [70, 146, 55], [100, 67, 205], [174, 96, 67], [47, 203, 199], [67, 44, 31], [3, 177, 182], [0, 1]], ![[118, 171, 99], [80, 114, 15], [20, 191, 148], [23, 54, 54], [83, 119, 6], [131, 163, 101], [136, 120, 95], [64, 39, 112]], ![[0, 1], [150, 162, 141], [140, 164, 69], [169, 61, 90], [40, 100, 6], [113, 4, 79], [172, 125, 145], [118, 171, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 185], []]
 b := ![[], [194, 116, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [208, 34, 29, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![835982, 748206, 121325]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3962, 3546, 575]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀

instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![35, -18, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![35, -18, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![35, 205, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![35, -18, 1], ![262, 101, -18], ![-4716, -926, 101]]]
  hmulB := by decide  
  f := ![![![-34, 18, -1], ![223, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -205, 223]], ![![0, -1, 1], ![4, 17, -18], ![-37, -97, 101]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [206, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 222], [0, 1]]
 g := ![![[136, 188], [6, 39], [159, 196], [77, 126], [13, 64], [148], [82, 1]], ![[165, 35], [82, 184], [175, 27], [151, 97], [132, 159], [148], [164, 222]]]
 h' := ![![[82, 222], [102, 100], [27, 40], [194, 209], [221, 55], [77, 8], [56, 51], [0, 1]], ![[0, 1], [51, 123], [185, 183], [161, 14], [48, 168], [64, 215], [1, 172], [82, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [153]]
 b := ![[], [97, 188]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [206, 141, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5246, 143, 54]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, -49, 54]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![18, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![18, 1, 0]] 
 ![![223, 0, 0], ![18, 1, 0], ![122, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![18, 1, 0], ![0, 18, 1], ![262, 66, 18]]]
  hmulB := by decide  
  f := ![![![1045, 58, 0], ![-12934, 0, 0]], ![![54, 3, 0], ![-668, 0, 0]], ![![578, 32, 0], ![-7154, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 223, 0], ![-122, 0, 223]], ![![0, 1, 0], ![-2, 18, 1], ![-14, 66, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![35, -18, 1]] ![![223, 0, 0], ![18, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![4014, 223, 0]], ![![7805, -4014, 223], ![892, -223, 0]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![18, 1, 0]]], ![![![35, -18, 1]], ![![4, -1, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0)
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [17, 74, 166, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 154, 125], [184, 72, 102], [0, 1]]
 g := ![![[74, 57, 26], [67, 69, 160], [157, 78], [1, 10], [44, 9], [191, 33, 89], [1]], ![[111, 214, 221, 138], [44, 53, 225, 55], [117, 221], [81, 159], [48, 207], [178, 174, 21, 5], [219, 140, 52, 17]], ![[213, 78, 45, 101], [31, 9, 223, 33], [155, 47], [21, 167], [188, 131], [125, 145, 224, 92], [128, 209, 62, 210]]]
 h' := ![![[104, 154, 125], [223, 108, 139], [164, 171, 198], [91, 213, 140], [154, 185, 64], [158, 122, 224], [210, 153, 61], [0, 1]], ![[184, 72, 102], [3, 70, 127], [131, 152, 219], [118, 110, 158], [70, 191, 39], [146, 213, 52], [215, 69, 136], [104, 154, 125]], ![[0, 1], [192, 49, 188], [81, 131, 37], [30, 131, 156], [29, 78, 124], [71, 119, 178], [37, 5, 30], [184, 72, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118, 14], []]
 b := ![[], [223, 151, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [17, 74, 166, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1651652, -486461, -11804]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7276, -2143, -52]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-141, 29, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-141, 29, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![88, 29, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-141, 29, 1], ![262, -75, 29], ![7598, 2176, -75]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-88, -29, 229]], ![![-1, 0, 1], ![-10, -4, 29], ![62, 19, -75]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [13, 178, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 228], [0, 1]]
 g := ![![[137, 19], [174], [77, 204], [99], [130], [177, 181], [51, 1]], ![[190, 210], [174], [176, 25], [99], [130], [19, 48], [102, 228]]]
 h' := ![![[51, 228], [154, 146], [144, 116], [98, 77], [34, 102], [218, 151], [24, 69], [0, 1]], ![[0, 1], [43, 83], [106, 113], [132, 152], [198, 127], [133, 78], [108, 160], [51, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [162, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [13, 178, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![537, 216, -111]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45, 15, -111]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-29, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-29, 1, 0]] 
 ![![229, 0, 0], ![200, 1, 0], ![75, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-29, 1, 0], ![0, -29, 1], ![262, 66, -29]]]
  hmulB := by decide  
  f := ![![![2698, -93, 0], ![21297, 0, 0]], ![![2350, -81, 0], ![18550, 0, 0]], ![![874, -30, 0], ![6899, 1, 0]]]
  g := ![![![1, 0, 0], ![-200, 229, 0], ![-75, 0, 229]], ![![-1, 1, 0], ![25, -29, 1], ![-47, 66, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-141, 29, 1]] ![![229, 0, 0], ![-29, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-6641, 229, 0]], ![![-32289, 6641, 229], ![4351, -916, 0]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-29, 1, 0]]], ![![![-141, 29, 1]], ![![19, -4, 0]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0]] 
 ![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [200, 114, 98, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 121, 38], [31, 111, 195], [0, 1]]
 g := ![![[102, 4, 181], [221, 200], [69, 8], [115, 187, 102], [24, 175], [75, 104, 51], [1]], ![[15, 109], [127, 195], [137, 109], [151, 195, 228, 1], [230, 200], [60, 13, 35, 13], [160, 41, 106, 117]], ![[55, 55, 30, 112], [31, 201], [103, 56], [170, 141, 34, 226], [127, 60], [25, 156, 0, 200], [10, 217, 222, 116]]]
 h' := ![![[104, 121, 38], [151, 133, 114], [9, 199, 82], [67, 53, 63], [148, 95, 175], [145, 165, 117], [33, 119, 135], [0, 1]], ![[31, 111, 195], [11, 230], [125, 144, 121], [65, 228, 153], [148, 10, 201], [108, 24, 151], [94, 47, 168], [104, 121, 38]], ![[0, 1], [165, 103, 119], [128, 123, 30], [34, 185, 17], [172, 128, 90], [117, 44, 198], [64, 67, 163], [31, 111, 195]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 228], []]
 b := ![[], [100, 214, 227], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [200, 114, 98, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3857315, 1305033, 134208]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16555, 5601, 576]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def PBC233 : ContainsPrimesAboveP 233 ![I233N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![233, 0, 0]]) timesTableT_eq_Table B_one_repr 233 (by decide) 𝕀



lemma PB238I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 237 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 237 (by omega)

def PB238I4 : PrimesBelowBoundCertificateInterval O 193 237 238 where
  m := 7
  g := ![3, 1, 1, 2, 1, 2, 1]
  P := ![197, 199, 211, 223, 227, 229, 233]
  hP := PB238I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0]
    · exact ![I211N0]
    · exact ![I223N0, I223N1]
    · exact ![I227N0]
    · exact ![I229N0, I229N1]
    · exact ![I233N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![197, 197, 197]
    · exact ![7880599]
    · exact ![9393931]
    · exact ![49729, 223]
    · exact ![11697083]
    · exact ![52441, 229]
    · exact ![12649337]
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
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
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
  β := ![I197N0, I197N1, I197N2, I223N1, I229N1]
  Il := ![[I197N0, I197N1, I197N2], [], [], [I223N1], [], [I229N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
