
import IdealArithmetic.Examples.NF3_1_817516_2.RI3_1_817516_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![24, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![24, 1, 0]] 
 ![![197, 0, 0], ![24, 1, 0], ![133, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![24, 1, 0], ![3, 27, 7], ![-173, -6, 22]]]
  hmulB := by decide  
  f := ![![![40345, 370621, 96096], ![6895, -2704416, 0]], ![![4896, 45139, 11704], ![986, -329384, 0]], ![![27233, 250216, 64877], ![4696, -1825824, 0]]]
  g := ![![![1, 0, 0], ![-24, 197, 0], ![-133, 0, 197]], ![![0, 1, 0], ![-8, 27, 7], ![-15, -6, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![48, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![48, 1, 0]] 
 ![![197, 0, 0], ![48, 1, 0], ![101, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![48, 1, 0], ![3, 51, 7], ![-173, -6, 46]]]
  hmulB := by decide  
  f := ![![![-3035, -55687, -7644], ![-985, 215124, 0]], ![![-750, -13565, -1862], ![-196, 52402, 0]], ![![-1595, -28551, -3919], ![-345, 110292, 0]]]
  g := ![![![1, 0, 0], ![-48, 197, 0], ![-101, 0, 197]], ![![0, 1, 0], ![-16, 51, 7], ![-23, -6, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-73, 1, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-73, 1, 0]] 
 ![![197, 0, 0], ![124, 1, 0], ![171, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-73, 1, 0], ![3, -70, 7], ![-173, -6, -75]]]
  hmulB := by decide  
  f := ![![![7721, -214180, 21420], ![-3940, -602820, 0]], ![![4903, -134808, 13482], ![-2363, -379422, 0]], ![![6732, -185913, 18593], ![-3339, -523260, 0]]]
  g := ![![![1, 0, 0], ![-124, 197, 0], ![-171, 0, 197]], ![![-1, 1, 0], ![38, -70, 7], ![68, -6, -75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![24, 1, 0]] ![![197, 0, 0], ![48, 1, 0]]
  ![![197, 0, 0], ![-32, 67, 1]] where
 M := ![![![38809, 0, 0], ![9456, 197, 0]], ![![4728, 197, 0], ![1155, 75, 7]]]
 hmul := by decide  
 g := ![![![![197, 0, 0], ![0, 0, 0]], ![![48, 1, 0], ![0, 0, 0]]], ![![![24, 1, 0], ![0, 0, 0]], ![![7, -2, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-32, 67, 1]] ![![197, 0, 0], ![-73, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-14381, 197, 0]], ![![-6304, 13199, 197], ![2364, -4728, 394]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-73, 1, 0]]], ![![![-32, 67, 1]], ![![12, -24, 2]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [134, 16, 135, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 102, 75], [7, 96, 124], [0, 1]]
 g := ![![[7, 49, 182], [88, 92, 132], [36, 181, 111], [78, 18], [124, 23], [3, 116], [1]], ![[143, 82, 108, 75], [183, 122, 181, 19], [12, 20, 115, 77], [99, 116], [192, 79], [191, 165], [194, 37, 177, 194]], ![[42, 23, 46, 72], [69, 119, 190, 172], [184, 55, 159, 86], [57, 53], [96, 132], [155, 94], [177, 6, 62, 5]]]
 h' := ![![[57, 102, 75], [148, 110, 111], [151, 59, 27], [51, 68, 132], [73, 1, 60], [42, 39, 146], [65, 183, 64], [0, 1]], ![[7, 96, 124], [183, 175, 1], [2, 142, 52], [46, 121, 61], [175, 134, 64], [86, 182, 26], [196, 87, 168], [57, 102, 75]], ![[0, 1], [159, 113, 87], [175, 197, 120], [173, 10, 6], [100, 64, 75], [32, 177, 27], [107, 128, 166], [7, 96, 124]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 153], []]
 b := ![[], [153, 11, 189], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [134, 16, 135, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2124922, -248153, 9751]
  a := ![-3, -4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10678, -1247, 49]
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


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [65, 121, 179, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 68, 151], [158, 142, 60], [0, 1]]
 g := ![![[161, 137, 125], [205, 35, 163], [186, 123], [80, 100], [147, 166, 209], [126, 180], [1]], ![[166, 201, 108, 49], [21, 138, 116, 6], [49, 66], [176, 150], [127, 98, 154, 46], [91, 144], [162, 34, 58, 64]], ![[92, 115, 167, 22], [37, 36, 126, 28], [156, 169], [12, 208], [165, 70, 75, 111], [15, 189], [128, 150, 114, 147]]]
 h' := ![![[85, 68, 151], [179, 190, 97], [85, 115, 116], [88, 126, 171], [151, 156, 201], [44, 178, 118], [146, 90, 32], [0, 1]], ![[158, 142, 60], [63, 142, 53], [103, 196, 77], [171, 94, 53], [46, 155, 192], [72, 114, 168], [135, 197, 199], [85, 68, 151]], ![[0, 1], [150, 90, 61], [142, 111, 18], [187, 202, 198], [171, 111, 29], [84, 130, 136], [209, 135, 191], [158, 142, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132, 30], []]
 b := ![[], [120, 196, 106], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [65, 121, 179, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29623134, -27852, -88198]
  a := ![8, 6, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![140394, -132, -418]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0]] 
 ![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [69, 165, 120, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [149, 79, 74], [177, 143, 149], [0, 1]]
 g := ![![[14, 66, 152], [192, 146, 128], [165, 127, 49], [222, 183, 213], [142, 113, 78], [156, 128], [1]], ![[167, 125, 66, 69], [206, 98, 89, 172], [8, 173, 98, 112], [48, 127, 25, 98], [136, 92, 153, 169], [207, 119], [193, 206, 6, 33]], ![[171, 63, 6, 99], [221, 69, 203, 142], [13, 221, 167, 142], [113, 17, 154, 99], [174, 198, 216, 46], [136, 17], [51, 176, 68, 190]]]
 h' := ![![[149, 79, 74], [132, 91, 179], [211, 216, 103], [69, 222, 7], [14, 94, 131], [18, 17, 154], [154, 58, 103], [0, 1]], ![[177, 143, 149], [85, 147, 219], [214, 48, 162], [108, 200, 35], [208, 0, 44], [220, 122, 88], [30, 54, 66], [149, 79, 74]], ![[0, 1], [154, 208, 48], [89, 182, 181], [74, 24, 181], [211, 129, 48], [118, 84, 204], [164, 111, 54], [177, 143, 149]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 204], []]
 b := ![[], [73, 156, 166], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [69, 165, 120, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11336535040, -552246120, 145654011]
  a := ![-67, -66, -135]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50836480, -2476440, 653157]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-2, -43, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-2, -43, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![225, 184, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-2, -43, 1], ![-302, -137, -303], ![7560, 235, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-225, -184, 227]], ![![-1, -1, 1], ![299, 245, -303], ![-45, -63, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [46, 207, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 226], [0, 1]]
 g := ![![[118, 132], [13, 225], [108], [70], [209], [143, 12], [20, 1]], ![[34, 95], [200, 2], [108], [70], [209], [156, 215], [40, 226]]]
 h' := ![![[20, 226], [83, 86], [142, 212], [32, 154], [172, 98], [5, 182], [215, 127], [0, 1]], ![[0, 1], [214, 141], [69, 15], [161, 73], [89, 129], [13, 45], [31, 100], [20, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [122, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [46, 207, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3736, -11089, -5623]
  a := ![-8, -7, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5557, 4509, -5623]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![76, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![76, 1, 0]] 
 ![![227, 0, 0], ![76, 1, 0], ![148, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![76, 1, 0], ![3, 79, 7], ![-173, -6, 74]]]
  hmulB := by decide  
  f := ![![![929, 28438, 2520], ![454, -81720, 0]], ![![284, 9479, 840], ![228, -27240, 0]], ![![600, 18541, 1643], ![313, -53280, 0]]]
  g := ![![![1, 0, 0], ![-76, 227, 0], ![-148, 0, 227]], ![![0, 1, 0], ![-31, 79, 7], ![-47, -6, 74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-2, -43, 1]] ![![227, 0, 0], ![76, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![17252, 227, 0]], ![![-454, -9761, 227], ![-454, -3405, -227]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![76, 1, 0]]], ![![![-2, -43, 1]], ![![-2, -15, -1]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0]] 
 ![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [126, 81, 165, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [159, 52, 121], [134, 176, 108], [0, 1]]
 g := ![![[26, 133, 56], [176, 135], [41, 199, 75], [140, 172], [182, 14], [175, 105, 203], [1]], ![[159, 14, 47, 49], [185, 37], [155, 108, 23, 58], [40, 26], [96, 11], [130, 201, 105, 76], [105, 21, 122, 17]], ![[214, 92, 135, 146], [147, 4], [67, 19, 228, 91], [98, 176], [117, 83], [126, 63, 106, 12], [203, 107, 152, 212]]]
 h' := ![![[159, 52, 121], [162, 210, 133], [101, 81, 140], [35, 19, 126], [202, 105, 114], [163, 150, 48], [103, 148, 64], [0, 1]], ![[134, 176, 108], [49, 149, 41], [228, 178, 91], [98, 197, 201], [219, 88, 22], [117, 18, 34], [94, 68, 89], [159, 52, 121]], ![[0, 1], [161, 99, 55], [135, 199, 227], [171, 13, 131], [129, 36, 93], [98, 61, 147], [71, 13, 76], [134, 176, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130, 27], []]
 b := ![[], [198, 147, 172], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [126, 81, 165, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2236185, -290143, 3206]
  a := ![-3, -4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9765, -1267, 14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def PBC229 : ContainsPrimesAboveP 229 ![I229N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![229, 0, 0]]) timesTableT_eq_Table B_one_repr 229 (by decide) 𝕀

instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![97, 1, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![97, 1, 0]] 
 ![![233, 0, 0], ![97, 1, 0], ![46, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![97, 1, 0], ![3, 100, 7], ![-173, -6, 95]]]
  hmulB := by decide  
  f := ![![![6308, 265183, 18564], ![3961, -617916, 0]], ![![2633, 110393, 7728], ![1632, -257232, 0]], ![![1175, 52353, 3665], ![951, -121992, 0]]]
  g := ![![![1, 0, 0], ![-97, 233, 0], ![-46, 0, 233]], ![![0, 1, 0], ![-43, 100, 7], ![-17, -6, 95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N0 : Nat.card (O ⧸ I233N0) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N0)

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := prime_ideal_of_norm_prime hp233.out _ NI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-77, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-77, 1, 0]] 
 ![![233, 0, 0], ![156, 1, 0], ![185, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-77, 1, 0], ![3, -74, 7], ![-173, -6, -79]]]
  hmulB := by decide  
  f := ![![![28411, -803290, 75992], ![-12582, -2529448, 0]], ![![19033, -537796, 50876], ![-8387, -1693444, 0]], ![![22530, -637805, 60337], ![-10075, -2008360, 0]]]
  g := ![![![1, 0, 0], ![-156, 233, 0], ![-185, 0, 233]], ![![-1, 1, 0], ![44, -74, 7], ![66, -6, -79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-21, 1, 0]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-21, 1, 0]] 
 ![![233, 0, 0], ![212, 1, 0], ![13, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-21, 1, 0], ![3, -18, 7], ![-173, -6, -23]]]
  hmulB := by decide  
  f := ![![![19576, -118575, 46116], ![-2097, -1535004, 0]], ![![17815, -107884, 41958], ![-1863, -1396602, 0]], ![![1097, -6616, 2573], ![-64, -85644, 0]]]
  g := ![![![1, 0, 0], ![-212, 233, 0], ![-13, 0, 233]], ![![-1, 1, 0], ![16, -18, 7], ![6, -6, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![97, 1, 0]] ![![233, 0, 0], ![-77, 1, 0]]
  ![![233, 0, 0], ![-68, -30, 1]] where
 M := ![![![54289, 0, 0], ![-17941, 233, 0]], ![![22601, 233, 0], ![-7466, 23, 7]]]
 hmul := by decide  
 g := ![![![![233, 0, 0], ![0, 0, 0]], ![![-9, 31, -1], ![233, 0, 0]]], ![![![97, 1, 0], ![0, 0, 0]], ![![38, 31, -1], ![240, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-68, -30, 1]] ![![233, 0, 0], ![-21, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-4893, 233, 0]], ![![-15844, -6990, 233], ![1165, 466, -233]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-21, 1, 0]]], ![![![-68, -30, 1]], ![![5, 2, -1]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-84, 113, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-84, 113, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![155, 113, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-84, 113, 1], ![166, 249, 789], ![-19428, -701, -315]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-155, -113, 239]], ![![-1, 0, 1], ![-511, -372, 789], ![123, 146, -315]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [101, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [155, 238], [0, 1]]
 g := ![![[228, 71], [153, 85], [143, 176], [124, 186], [102], [109, 98], [155, 1]], ![[0, 168], [183, 154], [177, 63], [35, 53], [102], [3, 141], [71, 238]]]
 h' := ![![[155, 238], [82, 166], [136, 221], [143, 43], [200, 80], [224, 126], [119, 24], [0, 1]], ![[0, 1], [0, 73], [214, 18], [116, 196], [172, 159], [156, 113], [15, 215], [155, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [26, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [101, 84, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-59781, -644, 3298]
  a := ![4, 23, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2389, -1562, 3298]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-72, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-72, 1, 0]] 
 ![![239, 0, 0], ![167, 1, 0], ![76, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-72, 1, 0], ![3, -69, 7], ![-173, -6, -74]]]
  hmulB := by decide  
  f := ![![![33805, -871827, 88452], ![-13623, -3020004, 0]], ![![23608, -609161, 61803], ![-9559, -2110131, 0]], ![![10772, -277234, 28127], ![-4258, -960336, 0]]]
  g := ![![![1, 0, 0], ![-167, 239, 0], ![-76, 0, 239]], ![![-1, 1, 0], ![46, -69, 7], ![27, -6, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-84, 113, 1]] ![![239, 0, 0], ![-72, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-17208, 239, 0]], ![![-20076, 27007, 239], ![6214, -7887, 717]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-72, 1, 0]]], ![![![-84, 113, 1]], ![![26, -33, 3]]]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![74, -103, 1]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![74, -103, 1]] 
 ![![241, 0, 0], ![0, 241, 0], ![74, 138, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![74, -103, 1], ![-482, -241, -723], ![17940, 595, 275]]]
  hmulB := by decide  
  f := ![![![-73, 103, -1], ![241, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -138, 241]], ![![0, -1, 1], ![220, 413, -723], ![-10, -155, 275]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [190, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [155, 240], [0, 1]]
 g := ![![[107, 232], [134], [237], [12], [75, 36], [4, 94], [155, 1]], ![[158, 9], [134], [237], [12], [112, 205], [114, 147], [69, 240]]]
 h' := ![![[155, 240], [206, 192], [19, 80], [127, 128], [210, 129], [204, 6], [193, 217], [0, 1]], ![[0, 1], [82, 49], [128, 161], [205, 113], [202, 112], [170, 235], [88, 24], [155, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [198]]
 b := ![[], [160, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [190, 86, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6552, -2046, -1136]
  a := ![-4, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![376, 642, -1136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![0, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![0, 1, 0]] 
 ![![241, 0, 0], ![0, 1, 0], ![207, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![0, 1, 0], ![3, 3, 7], ![-173, -6, -2]]]
  hmulB := by decide  
  f := ![![![-482, -483, -1127], ![0, 38801, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-414, -415, -968], ![34, 33327, 0]]]
  g := ![![![1, 0, 0], ![0, 241, 0], ![-207, 0, 241]], ![![0, 1, 0], ![-6, 3, 7], ![1, -6, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![74, -103, 1]] ![![241, 0, 0], ![0, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![0, 241, 0]], ![![17834, -24823, 241], ![-482, -241, -723]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![0, 1, 0]]], ![![![74, -103, 1]], ![![-2, -1, -3]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![112, -43, 1]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0], ![112, -43, 1]] 
 ![![251, 0, 0], ![0, 251, 0], ![112, 208, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![112, -43, 1], ![-302, -23, -303], ![7560, 235, 193]]]
  hmulB := by decide  
  f := ![![![-111, 43, -1], ![251, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-112, -208, 251]], ![![0, -1, 1], ![134, 251, -303], ![-56, -159, 193]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [108, 214, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 250], [0, 1]]
 g := ![![[81, 86], [91, 140], [118], [83, 80], [125, 7], [66, 36], [37, 1]], ![[0, 165], [0, 111], [118], [31, 171], [133, 244], [143, 215], [74, 250]]]
 h' := ![![[37, 250], [212, 191], [221, 89], [72, 108], [54, 64], [151, 209], [20, 6], [0, 1]], ![[0, 1], [0, 60], [0, 162], [52, 143], [163, 187], [103, 42], [242, 245], [37, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [198, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [108, 214, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8617, -3955, 2135]
  a := ![6, 7, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-987, -1785, 2135]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![52, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![52, 1, 0]] 
 ![![251, 0, 0], ![52, 1, 0], ![58, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![52, 1, 0], ![3, 55, 7], ![-173, -6, 50]]]
  hmulB := by decide  
  f := ![![![4361, 84695, 10780], ![1255, -386540, 0]], ![![853, 17543, 2233], ![503, -80069, 0]], ![![958, 19570, 2491], ![530, -89320, 0]]]
  g := ![![![1, 0, 0], ![-52, 251, 0], ![-58, 0, 251]], ![![0, 1, 0], ![-13, 55, 7], ![-11, -6, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![112, -43, 1]] ![![251, 0, 0], ![52, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![13052, 251, 0]], ![![28112, -10793, 251], ![5522, -2259, -251]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![52, 1, 0]]], ![![![112, -43, 1]], ![![22, -9, -1]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0)


lemma PB256I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 255 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 255 (by omega)

def PB256I4 : PrimesBelowBoundCertificateInterval O 193 255 256 where
  m := 10
  g := ![3, 1, 1, 1, 2, 1, 3, 2, 2, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB256I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0]
    · exact ![I211N0]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1]
    · exact ![I251N0, I251N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![197, 197, 197]
    · exact ![7880599]
    · exact ![9393931]
    · exact ![11089567]
    · exact ![51529, 227]
    · exact ![12008989]
    · exact ![233, 233, 233]
    · exact ![57121, 239]
    · exact ![58081, 241]
    · exact ![63001, 251]
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
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
      exact NI233N2
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
  β := ![I197N0, I197N1, I197N2, I227N1, I233N0, I233N1, I233N2, I239N1, I241N1, I251N1]
  Il := ![[I197N0, I197N1, I197N2], [], [], [], [I227N1], [], [I233N0, I233N1, I233N2], [I239N1], [I241N1], [I251N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
