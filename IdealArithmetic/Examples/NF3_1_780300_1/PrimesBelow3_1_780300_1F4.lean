
import IdealArithmetic.Examples.NF3_1_780300_1.RI3_1_780300_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-72, 5, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-72, 5, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![125, 5, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-72, 5, 1], ![170, -72, 25], ![850, 34, -72]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-125, -5, 197]], ![![-1, 0, 1], ![-15, -1, 25], ![50, 2, -72]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [123, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [150, 196], [0, 1]]
 g := ![![[18, 6], [112], [136, 83], [146], [146], [60], [150, 1]], ![[130, 191], [112], [175, 114], [146], [146], [60], [103, 196]]]
 h' := ![![[150, 196], [106, 20], [17, 167], [107, 110], [170, 46], [2, 151], [68, 116], [0, 1]], ![[0, 1], [151, 177], [48, 30], [59, 87], [175, 151], [194, 46], [132, 81], [150, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [183]]
 b := ![[], [131, 190]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [123, 47, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![463, -13, -42]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, 1, -42]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-25, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-25, 1, 0]] 
 ![![197, 0, 0], ![172, 1, 0], ![72, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-25, 1, 0], ![0, -25, 5], ![170, 0, -25]]]
  hmulB := by decide  
  f := ![![![3651, -146, 0], ![28762, 0, 0]], ![![3176, -127, 0], ![25020, 0, 0]], ![![1326, -43, -2], ![10446, 79, 0]]]
  g := ![![![1, 0, 0], ![-172, 197, 0], ![-72, 0, 197]], ![![-1, 1, 0], ![20, -25, 5], ![10, 0, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-72, 5, 1]] ![![197, 0, 0], ![-25, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-4925, 197, 0]], ![![-14184, 985, 197], ![1970, -197, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-25, 1, 0]]], ![![![-72, 5, 1]], ![![10, -1, 0]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [66, 78, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [154, 33, 169], [42, 165, 30], [0, 1]]
 g := ![![[64, 14, 157], [127, 40, 157], [106, 141, 64], [177, 114], [28, 158], [43, 9], [1]], ![[62, 172, 30, 32], [126, 150, 24, 62], [96, 126, 25, 33], [73, 112], [184, 187], [149, 130], [126, 105, 154, 64]], ![[60, 130, 163, 118], [188, 154, 85, 170], [44, 61, 118, 74], [169, 187], [130, 13], [62, 14], [78, 154, 131, 135]]]
 h' := ![![[154, 33, 169], [175, 156, 117], [168, 134, 117], [185, 116, 191], [46, 99, 78], [125, 179, 77], [133, 121, 196], [0, 1]], ![[42, 165, 30], [198, 115, 98], [186, 185, 161], [1, 119, 175], [21, 177, 149], [15, 40, 171], [59, 40, 54], [154, 33, 169]], ![[0, 1], [196, 127, 183], [61, 79, 120], [3, 163, 32], [49, 122, 171], [120, 179, 150], [86, 38, 148], [42, 165, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [152, 78], []]
 b := ![[], [161, 143, 122], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [66, 78, 3, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![149250, 5970, -8955]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![750, 30, -45]
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


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [94, 138, 192, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [132, 138, 136], [98, 72, 75], [0, 1]]
 g := ![![[39, 80, 119], [47, 125, 170], [2, 6], [196, 125], [46, 71, 201], [138, 150], [1]], ![[47, 62, 30, 137], [190, 62, 146, 1], [30, 87], [179, 13], [1, 120, 91, 122], [11, 109], [73, 56, 208, 125]], ![[193, 106, 140, 88], [181, 89, 188, 67], [81, 73], [42, 103], [95, 150, 150, 17], [104, 122], [191, 24, 8, 86]]]
 h' := ![![[132, 138, 136], [13, 158, 142], [167, 180, 176], [199, 63, 46], [107, 153, 97], [84, 185, 137], [117, 73, 19], [0, 1]], ![[98, 72, 75], [70, 96, 62], [148, 77, 16], [15, 167, 64], [159, 92, 151], [97, 194, 209], [169, 144, 113], [132, 138, 136]], ![[0, 1], [47, 168, 7], [209, 165, 19], [4, 192, 101], [24, 177, 174], [39, 43, 76], [113, 205, 79], [98, 72, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [197, 7], []]
 b := ![[], [197, 5, 107], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [94, 138, 192, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![510620, -12660, 12660]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2420, -60, 60]
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


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [32, 195, 220, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 207, 165], [216, 15, 58], [0, 1]]
 g := ![![[153, 131, 8], [27, 132, 18], [68, 77, 179], [52, 42, 4], [36, 216, 30], [195, 9], [1]], ![[152, 94, 158, 134], [13, 131, 94, 167], [221, 117, 177, 20], [55, 30, 179, 176], [177, 5, 180, 187], [180, 101], [206, 155, 19, 13]], ![[180, 135, 82, 175], [61, 187, 47, 164], [154, 207, 37, 76], [109, 7, 135, 202], [200, 23, 145, 69], [67, 2], [212, 26, 147, 210]]]
 h' := ![![[10, 207, 165], [28, 117, 30], [54, 14, 178], [120, 143, 198], [186, 104, 221], [136, 35, 91], [191, 28, 3], [0, 1]], ![[216, 15, 58], [109, 152, 131], [155, 85, 74], [116, 188, 28], [139, 104, 182], [104, 168, 4], [206, 22, 205], [10, 207, 165]], ![[0, 1], [18, 177, 62], [192, 124, 194], [43, 115, 220], [192, 15, 43], [167, 20, 128], [9, 173, 15], [216, 15, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [161, 27], []]
 b := ![[], [87, 44, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [32, 195, 220, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-382222, 67346, 3791]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1714, 302, 17]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-78, -47, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-78, -47, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![149, 180, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-78, -47, 1], ![170, -78, -235], ![-7990, 34, -78]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-149, -180, 227]], ![![-1, -1, 1], ![155, 186, -235], ![16, 62, -78]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [76, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [141, 226], [0, 1]]
 g := ![![[31, 3], [188, 133], [36], [87], [27], [164, 185], [141, 1]], ![[0, 224], [100, 94], [36], [87], [27], [144, 42], [55, 226]]]
 h' := ![![[141, 226], [13, 177], [216, 70], [1, 221], [205, 119], [21, 150], [180, 56], [0, 1]], ![[0, 1], [0, 50], [98, 157], [63, 6], [186, 108], [60, 77], [131, 171], [141, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132]]
 b := ![[], [114, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [76, 86, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![416, -52, -81]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![55, 64, -81]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![8, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![8, 1, 0]] 
 ![![227, 0, 0], ![8, 1, 0], ![78, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![8, 1, 0], ![0, 8, 5], ![170, 0, 8]]]
  hmulB := by decide  
  f := ![![![1073, 134, 0], ![-30418, 0, 0]], ![![24, 3, 0], ![-680, 0, 0]], ![![362, 42, -2], ![-10262, 91, 0]]]
  g := ![![![1, 0, 0], ![-8, 227, 0], ![-78, 0, 227]], ![![0, 1, 0], ![-2, 8, 5], ![-2, 0, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-78, -47, 1]] ![![227, 0, 0], ![8, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![1816, 227, 0]], ![![-17706, -10669, 227], ![-454, -454, -227]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![8, 1, 0]]], ![![![-78, -47, 1]], ![![-2, -2, -1]]]]
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


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [206, 160, 226, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 220, 60], [185, 8, 169], [0, 1]]
 g := ![![[12, 53, 19], [162, 51], [20, 209, 19], [147, 185], [170, 5], [202, 212, 9], [1]], ![[66, 96, 191, 100], [45, 42], [121, 99, 114, 27], [105, 5], [42, 130], [148, 217, 107, 42], [135, 218, 55, 53]], ![[198, 54, 176, 187], [112, 75], [164, 82, 6, 168], [102, 196], [165, 126], [222, 85, 161, 99], [180, 94, 137, 176]]]
 h' := ![![[47, 220, 60], [66, 160, 83], [2, 101, 76], [201, 126, 146], [22, 92, 177], [66, 107, 66], [23, 69, 3], [0, 1]], ![[185, 8, 169], [15, 104, 188], [101, 113, 27], [183, 70, 26], [150, 136, 66], [10, 33, 78], [214, 28, 42], [47, 220, 60]], ![[0, 1], [203, 194, 187], [157, 15, 126], [75, 33, 57], [83, 1, 215], [69, 89, 85], [22, 132, 184], [185, 8, 169]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139, 54], []]
 b := ![[], [146, 130, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [206, 160, 226, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7315863, 203581, 423650]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31947, 889, 1850]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-87, 13, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-87, 13, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![146, 13, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-87, 13, 1], ![170, -87, 65], ![2210, 34, -87]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-146, -13, 233]], ![![-1, 0, 1], ![-40, -4, 65], ![64, 5, -87]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [20, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [182, 232], [0, 1]]
 g := ![![[154, 46], [89], [23], [93, 121], [204], [158, 91], [182, 1]], ![[138, 187], [89], [23], [213, 112], [204], [177, 142], [131, 232]]]
 h' := ![![[182, 232], [102, 195], [22, 97], [4, 217], [33, 222], [102, 196], [88, 18], [0, 1]], ![[0, 1], [176, 38], [201, 136], [121, 16], [128, 11], [125, 37], [102, 215], [182, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [222]]
 b := ![[], [151, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [20, 51, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1050, 181, -4]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, 1, -4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-65, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-65, 1, 0]] 
 ![![233, 0, 0], ![168, 1, 0], ![87, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-65, 1, 0], ![0, -65, 5], ![170, 0, -65]]]
  hmulB := by decide  
  f := ![![![13651, -210, 0], ![48930, 0, 0]], ![![9816, -151, 0], ![35184, 0, 0]], ![![5139, -40, -3], ![18420, 140, 0]]]
  g := ![![![1, 0, 0], ![-168, 233, 0], ![-87, 0, 233]], ![![-1, 1, 0], ![45, -65, 5], ![25, 0, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-87, 13, 1]] ![![233, 0, 0], ![-65, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-15145, 233, 0]], ![![-20271, 3029, 233], ![5825, -932, 0]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-65, 1, 0]]], ![![![-87, 13, 1]], ![![25, -4, 0]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![10, 99, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![10, 99, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![10, 99, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![10, 99, 1], ![170, 10, 495], ![16830, 34, 10]]]
  hmulB := by decide  
  f := ![![![-9, -99, -1], ![239, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -99, 239]], ![![0, 0, 1], ![-20, -205, 495], ![70, -4, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [110, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [202, 238], [0, 1]]
 g := ![![[59, 176], [147, 11], [156, 100], [186, 220], [27], [153, 33], [202, 1]], ![[0, 63], [218, 228], [41, 139], [172, 19], [27], [127, 206], [165, 238]]]
 h' := ![![[202, 238], [82, 196], [48, 190], [94, 229], [99, 170], [139, 79], [7, 64], [0, 1]], ![[0, 1], [0, 43], [188, 49], [225, 10], [23, 69], [84, 160], [29, 175], [202, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [143, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [110, 37, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![790, 173, 79]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![0, -32, 79]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-17, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-17, 1, 0]] 
 ![![239, 0, 0], ![222, 1, 0], ![229, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-17, 1, 0], ![0, -17, 5], ![170, 0, -17]]]
  hmulB := by decide  
  f := ![![![3860, -227, 0], ![54253, 0, 0]], ![![3588, -211, 0], ![50430, 0, 0]], ![![3714, -215, -1], ![52201, 48, 0]]]
  g := ![![![1, 0, 0], ![-222, 239, 0], ![-229, 0, 239]], ![![-1, 1, 0], ![11, -17, 5], ![17, 0, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![10, 99, 1]] ![![239, 0, 0], ![-17, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-4063, 239, 0]], ![![2390, 23661, 239], ![0, -1673, 478]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-17, 1, 0]]], ![![![10, 99, 1]], ![![0, -7, 2]]]]
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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [102, 90, 235, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 117, 101], [210, 123, 140], [0, 1]]
 g := ![![[2, 45, 238], [157, 143], [94, 113], [177, 159], [101, 177, 225], [139, 100, 36], [1]], ![[160, 191, 145, 202], [201, 143], [65, 80], [182, 4], [97, 0, 205, 142], [170, 95, 186, 22], [226, 135, 170, 26]], ![[236, 77, 159, 13], [234, 90], [14, 96], [136, 83], [98, 139, 112, 37], [203, 9, 217, 99], [51, 237, 75, 215]]]
 h' := ![![[37, 117, 101], [84, 205, 210], [34, 39, 25], [127, 150, 178], [61, 83, 20], [41, 226, 15], [139, 151, 6], [0, 1]], ![[210, 123, 140], [166, 231, 22], [119, 117, 25], [240, 46, 171], [214, 81, 239], [69, 60, 89], [127, 77, 83], [37, 117, 101]], ![[0, 1], [153, 46, 9], [198, 85, 191], [105, 45, 133], [177, 77, 223], [173, 196, 137], [193, 13, 152], [210, 123, 140]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [177, 81], []]
 b := ![[], [196, 93, 171], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [102, 90, 235, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2441330, 124356, 102184]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10130, 516, 424]
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



lemma PB250I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 249 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 249 (by omega)

def PB250I4 : PrimesBelowBoundCertificateInterval O 193 249 250 where
  m := 9
  g := ![2, 1, 1, 1, 2, 1, 2, 2, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241]
  hP := PB250I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![7880599]
    · exact ![9393931]
    · exact ![11089567]
    · exact ![51529, 227]
    · exact ![12008989]
    · exact ![54289, 233]
    · exact ![57121, 239]
    · exact ![13997521]
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
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
  β := ![I197N1, I227N1, I233N1, I239N1]
  Il := ![[I197N1], [], [], [], [I227N1], [], [I233N1], [I239N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
