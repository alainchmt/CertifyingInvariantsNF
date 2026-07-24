
import IdealArithmetic.Examples.NF3_1_856596_2.RI3_1_856596_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0]] 
 ![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [62, 16, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 78, 127], [95, 118, 70], [0, 1]]
 g := ![![[193, 73, 171], [153, 41], [17, 58, 40], [192, 196], [60, 163], [183, 40], [1]], ![[186, 172, 46, 142], [98, 163], [112, 173, 89, 64], [160, 164], [63, 15], [118, 138], [174, 151, 51, 174]], ![[18, 159, 19, 143], [169, 156], [192, 193, 18, 88], [58, 104], [182, 196], [119, 182], [55, 117, 24, 23]]]
 h' := ![![[51, 78, 127], [3, 143, 163], [128, 87, 108], [139, 76, 146], [82, 2, 183], [181, 122, 153], [135, 181, 146], [0, 1]], ![[95, 118, 70], [145, 16, 162], [36, 135, 153], [85, 56, 88], [67, 66, 178], [69, 143, 58], [117, 169, 27], [51, 78, 127]], ![[0, 1], [176, 38, 69], [193, 172, 133], [46, 65, 160], [80, 129, 33], [23, 129, 183], [167, 44, 24], [95, 118, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89, 44], []]
 b := ![[], [112, 101, 192], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [62, 16, 51, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-563026, -1970, -5910]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2858, -10, -30]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀

instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![30, -92, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![30, -92, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![30, 107, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![30, -92, 1], ![-375, -243, -1107], ![-16371, -262, 310]]]
  hmulB := by decide  
  f := ![![![-29, 92, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -107, 199]], ![![0, -1, 1], ![165, 594, -1107], ![-129, -168, 310]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [151, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 198], [0, 1]]
 g := ![![[39, 29], [54, 132], [141, 13], [25], [31], [172], [81, 1]], ![[0, 170], [0, 67], [0, 186], [25], [31], [172], [162, 198]]]
 h' := ![![[81, 198], [5, 167], [2, 27], [188, 150], [111, 5], [4, 35], [107, 42], [0, 1]], ![[0, 1], [0, 32], [0, 172], [0, 49], [118, 194], [53, 164], [126, 157], [81, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [184]]
 b := ![[], [55, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [151, 118, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1784, 350, 710]
  a := ![2, 0, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-116, -380, 710]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-87, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-87, 1, 0]] 
 ![![199, 0, 0], ![112, 1, 0], ![88, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-87, 1, 0], ![6, -84, 12], ![177, 3, -90]]]
  hmulB := by decide  
  f := ![![![-13868, 239195, -34176], ![7363, 566752, 0]], ![![-7784, 134547, -19224], ![4180, 318798, 0]], ![![-6074, 105774, -15113], ![3390, 250624, 0]]]
  g := ![![![1, 0, 0], ![-112, 199, 0], ![-88, 0, 199]], ![![-1, 1, 0], ![42, -84, 12], ![39, 3, -90]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![30, -92, 1]] ![![199, 0, 0], ![-87, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-17313, 199, 0]], ![![5970, -18308, 199], ![-2985, 7761, -1194]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-87, 1, 0]]], ![![![30, -92, 1]], ![![-15, 39, -6]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
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


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [147, 201, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [198, 188, 42], [167, 22, 169], [0, 1]]
 g := ![![[102, 206, 45], [135, 189, 73], [120, 161], [67, 81], [78, 21, 105], [191, 84], [1]], ![[43, 155, 135, 40], [145, 39, 3, 88], [128, 201], [15, 51], [175, 180, 160, 195], [206, 100], [110, 106, 180, 27]], ![[143, 95, 73, 136], [49, 170, 181, 184], [74, 185], [2, 185], [20, 99, 56, 54], [94, 99], [203, 78, 14, 184]]]
 h' := ![![[198, 188, 42], [200, 131, 195], [191, 9, 101], [188, 71, 168], [139, 68, 202], [73, 126, 59], [64, 10, 154], [0, 1]], ![[167, 22, 169], [160, 104, 86], [34, 96, 68], [55, 137, 137], [19, 97, 126], [202, 22, 49], [201, 21, 10], [198, 188, 42]], ![[0, 1], [182, 187, 141], [0, 106, 42], [31, 3, 117], [89, 46, 94], [164, 63, 103], [181, 180, 47], [167, 22, 169]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 138], []]
 b := ![[], [140, 101, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [147, 201, 57, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20992856310, -1117172416, -457678412]
  a := ![-129, -64, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-99492210, -5294656, -2169092]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![87, 3, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![87, 3, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![87, 3, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![87, 3, 1], ![195, 99, 33], ![444, 23, 82]]]
  hmulB := by decide  
  f := ![![![-86, -3, -1], ![223, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-87, -3, 223]], ![![0, 0, 1], ![-12, 0, 33], ![-30, -1, 82]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [31, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 222], [0, 1]]
 g := ![![[198, 36], [73, 98], [48, 127], [222, 19], [64, 1], [126], [106, 1]], ![[0, 187], [203, 125], [130, 96], [6, 204], [170, 222], [126], [212, 222]]]
 h' := ![![[106, 222], [190, 217], [73, 105], [31, 57], [23, 58], [21, 222], [59, 55], [0, 1]], ![[0, 1], [0, 6], [53, 118], [52, 166], [150, 165], [138, 1], [91, 168], [106, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [185, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [31, 117, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2090, 620, -611]
  a := ![-3, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![229, 11, -611]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-33, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-33, 1, 0]] 
 ![![223, 0, 0], ![190, 1, 0], ![141, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-33, 1, 0], ![6, -30, 12], ![177, 3, -36]]]
  hmulB := by decide  
  f := ![![![-29534, 151447, -60588], ![5129, 1125927, 0]], ![![-25145, 129010, -51612], ![4461, 959123, 0]], ![![-18675, 95758, -38309], ![3236, 711909, 0]]]
  g := ![![![1, 0, 0], ![-190, 223, 0], ![-141, 0, 223]], ![![-1, 1, 0], ![18, -30, 12], ![21, 3, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![87, 3, 1]] ![![223, 0, 0], ![-33, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![-7359, 223, 0]], ![![19401, 669, 223], ![-2676, 0, 0]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![-33, 1, 0]]], ![![![87, 3, 1]], ![![-12, 0, 0]]]]
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [124, 166, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 47, 167], [95, 179, 60], [0, 1]]
 g := ![![[122, 32, 102], [122, 163, 76], [125, 161], [24, 131], [224, 221], [136, 51, 104], [1]], ![[91, 38, 79, 212], [31, 2, 222, 4], [97, 48], [146, 59], [144, 131], [144, 159, 31, 196], [205, 95, 172, 104]], ![[85, 84, 1, 151], [19, 55, 13, 224], [10, 110], [82, 43], [117, 173], [200, 115, 212, 130], [221, 207, 151, 123]]]
 h' := ![![[81, 47, 167], [81, 34, 97], [186, 40, 59], [134, 86, 191], [188, 147, 178], [161, 96, 158], [103, 61, 176], [0, 1]], ![[95, 179, 60], [27, 75, 114], [115, 55, 216], [148, 100, 200], [186, 68, 115], [136, 21, 49], [38, 120, 150], [81, 47, 167]], ![[0, 1], [120, 118, 16], [201, 132, 179], [83, 41, 63], [6, 12, 161], [126, 110, 20], [59, 46, 128], [95, 179, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [214, 202], []]
 b := ![[], [118, 110, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [124, 166, 51, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-563414, -2270, -6810]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2482, -10, -30]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-107, 31, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-107, 31, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![122, 31, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-107, 31, 1], ![363, -11, 369], ![5400, 107, -196]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-122, -31, 229]], ![![-1, 0, 1], ![-195, -50, 369], ![128, 27, -196]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [89, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [113, 228], [0, 1]]
 g := ![![[202, 138], [210], [8, 99], [203], [17], [64, 126], [113, 1]], ![[224, 91], [210], [203, 130], [203], [17], [104, 103], [226, 228]]]
 h' := ![![[113, 228], [26, 162], [204, 50], [20, 127], [15, 64], [29, 43], [19, 85], [0, 1]], ![[0, 1], [12, 67], [129, 179], [173, 102], [148, 165], [79, 186], [6, 144], [113, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [56, 151]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [89, 116, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-461, 125, -92]
  a := ![-1, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![47, 13, -92]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![89, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![89, 1, 0]] 
 ![![229, 0, 0], ![89, 1, 0], ![196, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![89, 1, 0], ![6, 92, 12], ![177, 3, 86]]]
  hmulB := by decide  
  f := ![![![160620, 2911471, 379800], ![75341, -7247850, 0]], ![![62408, 1131472, 147600], ![29313, -2816700, 0]], ![![137470, 2491914, 325069], ![64494, -6203400, 0]]]
  g := ![![![1, 0, 0], ![-89, 229, 0], ![-196, 0, 229]], ![![0, 1, 0], ![-46, 92, 12], ![-74, 3, 86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-107, 31, 1]] ![![229, 0, 0], ![89, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![20381, 229, 0]], ![![-24503, 7099, 229], ![-9160, 2748, 458]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![89, 1, 0]]], ![![![-107, 31, 1]], ![![-40, 12, 2]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-73, 111, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-73, 111, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![160, 111, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-73, 111, 1], ![843, 263, 1329], ![19560, 347, -402]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-160, -111, 233]], ![![-1, 0, 1], ![-909, -632, 1329], ![360, 193, -402]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [183, 120, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [113, 232], [0, 1]]
 g := ![![[184, 219], [66], [56], [5, 187], [105], [175, 16], [113, 1]], ![[0, 14], [66], [56], [166, 46], [105], [119, 217], [226, 232]]]
 h' := ![![[113, 232], [143, 174], [60, 149], [17, 17], [222, 113], [129, 173], [58, 4], [0, 1]], ![[0, 1], [0, 59], [121, 84], [74, 216], [176, 120], [106, 60], [44, 229], [113, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [90, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [183, 120, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2782, 1997, 1628]
  a := ![5, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1106, -767, 1628]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![69, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![69, 1, 0]] 
 ![![233, 0, 0], ![69, 1, 0], ![169, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![69, 1, 0], ![6, 72, 12], ![177, 3, 66]]]
  hmulB := by decide  
  f := ![![![1099, 14830, 2472], ![466, -47998, 0]], ![![297, 4391, 732], ![234, -14213, 0]], ![![761, 10756, 1793], ![460, -34814, 0]]]
  g := ![![![1, 0, 0], ![-69, 233, 0], ![-169, 0, 233]], ![![0, 1, 0], ![-30, 72, 12], ![-48, 3, 66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-73, 111, 1]] ![![233, 0, 0], ![69, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![16077, 233, 0]], ![![-17009, 25863, 233], ![-4194, 7922, 1398]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![69, 1, 0]]], ![![![-73, 111, 1]], ![![-18, 34, 6]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![117, 65, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![117, 65, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![117, 65, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![117, 65, 1], ![567, 315, 777], ![11418, 209, -74]]]
  hmulB := by decide  
  f := ![![![-116, -65, -1], ![239, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-117, -65, 239]], ![![0, 0, 1], ![-378, -210, 777], ![84, 21, -74]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [27, 218, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 238], [0, 1]]
 g := ![![[132, 62], [198, 93], [27, 67], [111, 232], [54], [135, 33], [21, 1]], ![[0, 177], [0, 146], [0, 172], [203, 7], [54], [111, 206], [42, 238]]]
 h' := ![![[21, 238], [151, 118], [227, 103], [110, 211], [230, 145], [179, 66], [150, 175], [0, 1]], ![[0, 1], [0, 121], [0, 136], [0, 28], [168, 94], [131, 173], [1, 64], [21, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [196, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [27, 218, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5072, 2685, -2220]
  a := ![-10, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1108, 615, -2220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-60, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-60, 1, 0]] 
 ![![239, 0, 0], ![179, 1, 0], ![74, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-60, 1, 0], ![6, -57, 12], ![177, 3, -63]]]
  hmulB := by decide  
  f := ![![![275821, -2812612, 592200], ![-80782, -11794650, 0]], ![![206581, -2106467, 443520], ![-60466, -8833440, 0]], ![![85426, -870851, 183359], ![-24911, -3651900, 0]]]
  g := ![![![1, 0, 0], ![-179, 239, 0], ![-74, 0, 239]], ![![-1, 1, 0], ![39, -57, 12], ![18, 3, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![117, 65, 1]] ![![239, 0, 0], ![-60, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-14340, 239, 0]], ![![27963, 15535, 239], ![-6453, -3585, 717]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-60, 1, 0]]], ![![![117, 65, 1]], ![![-27, -15, 3]]]]
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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [123, 2, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 110, 16], [192, 130, 225], [0, 1]]
 g := ![![[96, 76, 79], [37, 97], [26, 226], [204, 75], [140, 238, 162], [66, 219, 135], [1]], ![[195, 11, 179, 133], [109, 2], [232, 193], [77, 217], [148, 108, 54, 4], [235, 101, 44, 94], [3, 169, 178, 240]], ![[45, 47, 41, 194], [194, 151], [84, 116], [134, 162], [173, 187, 159, 20], [161, 103, 200, 98], [98, 68, 18, 1]]]
 h' := ![![[1, 110, 16], [144, 93, 140], [184, 63, 196], [44, 183, 60], [132, 81, 202], [76, 110, 43], [118, 239, 193], [0, 1]], ![[192, 130, 225], [42, 85, 167], [215, 198, 219], [109, 186, 124], [121, 39, 82], [238, 24, 120], [114, 22, 235], [1, 110, 16]], ![[0, 1], [144, 63, 175], [151, 221, 67], [19, 113, 57], [63, 121, 198], [26, 107, 78], [196, 221, 54], [192, 130, 225]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 140], []]
 b := ![[], [215, 197, 172], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [123, 2, 48, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-690465, -89652, -89652]
  a := ![-2, -6, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2865, -372, -372]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91, 10, -4]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![-91, 10, -4]] 
 ![![251, 0, 0], ![19, 1, 0], ![133, 0, 1]] where
  M :=![![![-91, 10, -4], ![-648, -73, 132], ![2118, -26, -137]]]
  hmulB := by decide  
  f := ![![![-13433, -1474, -1028]], ![![-1777, -195, -136]], ![![-7801, -856, -597]]]
  g := ![![![1, 10, -4], ![-67, -73, 132], ![83, -26, -137]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N0 : Nat.card (O ⧸ I251N0) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N0)

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := prime_ideal_of_norm_prime hp251.out _ NI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![76, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![76, 1, 0]] 
 ![![251, 0, 0], ![76, 1, 0], ![44, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![76, 1, 0], ![6, 79, 12], ![177, 3, 73]]]
  hmulB := by decide  
  f := ![![![32399, 473558, 71940], ![11797, -1504745, 0]], ![![9750, 143370, 21780], ![3766, -455565, 0]], ![![5668, 83014, 12611], ![2106, -263780, 0]]]
  g := ![![![1, 0, 0], ![-76, 251, 0], ![-44, 0, 251]], ![![0, 1, 0], ![-26, 79, 12], ![-13, 3, 73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-95, 1, 0]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-95, 1, 0]] 
 ![![251, 0, 0], ![156, 1, 0], ![67, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-95, 1, 0], ![6, -92, 12], ![177, 3, -98]]]
  hmulB := by decide  
  f := ![![![61455, -1102418, 143808], ![-27610, -3007984, 0]], ![![38229, -685148, 89376], ![-17067, -1869448, 0]], ![![16410, -294271, 38387], ![-7355, -802928, 0]]]
  g := ![![![1, 0, 0], ![-156, 251, 0], ![-67, 0, 251]], ![![-1, 1, 0], ![54, -92, 12], ![25, 3, -98]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![-91, 10, -4]] ![![251, 0, 0], ![76, 1, 0]]
  ![![251, 0, 0], ![79, 50, 1]] where
 M := ![![![-22841, 2510, -1004], ![-7564, 687, -172]]]
 hmul := by decide  
 g := ![![![![-91, 10, -4], ![0, 0, 0]], ![![-55, -13, -1], ![79, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![79, 50, 1]] ![![251, 0, 0], ![-95, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![-23845, 251, 0]], ![![19829, 12550, 251], ![-7028, -4518, 502]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![-95, 1, 0]]], ![![![79, 50, 1]], ![![-28, -18, 2]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1, I251N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
    exact isPrimeI251N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0 ⊙ MulI251N1)
instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0]] 
 ![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [173, 214, 146, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 200, 75], [254, 56, 182], [0, 1]]
 g := ![![[240, 91, 244], [201, 249], [173, 187], [201, 129], [180, 190], [244, 13], [111, 1], []], ![[215, 202], [153, 60], [223, 226], [73, 30], [98, 153], [212, 205], [106, 52], [53, 228]], ![[243, 199, 131, 204], [79, 133], [161, 25], [7, 205], [171, 256], [255, 157], [221, 165], [203, 228]]]
 h' := ![![[114, 200, 75], [45, 39, 191], [61, 133, 121], [156, 175, 207], [100, 253, 30], [237, 130, 226], [72, 231, 28], [0, 0, 1], [0, 1]], ![[254, 56, 182], [171, 42], [13, 217, 46], [175, 35, 45], [89, 133, 95], [248, 184, 47], [179, 194, 132], [229, 211, 56], [114, 200, 75]], ![[0, 1], [76, 176, 66], [76, 164, 90], [78, 47, 5], [255, 128, 132], [119, 200, 241], [95, 89, 97], [99, 46, 200], [254, 56, 182]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 62], []]
 b := ![[], [44, 40, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [173, 214, 146, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![202761692, 14699115, 5056989]
  a := ![27, 13, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![788956, 57195, 19677]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def PBC257 : ContainsPrimesAboveP 257 ![I257N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![257, 0, 0]]) timesTableT_eq_Table B_one_repr 257 (by decide) 𝕀



lemma PB262I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 261 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 261 (by omega)

def PB262I4 : PrimesBelowBoundCertificateInterval O 193 261 262 where
  m := 11
  g := ![1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB262I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1]
    · exact ![I211N0]
    · exact ![I223N0, I223N1]
    · exact ![I227N0]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
    · exact ![I251N0, I251N1, I251N2]
    · exact ![I257N0]
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
    · exact ![7645373]
    · exact ![39601, 199]
    · exact ![9393931]
    · exact ![49729, 223]
    · exact ![11697083]
    · exact ![52441, 229]
    · exact ![54289, 233]
    · exact ![57121, 239]
    · exact ![13997521]
    · exact ![251, 251, 251]
    · exact ![16974593]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
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
      exact NI251N1
      exact NI251N2
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
  β := ![I199N1, I223N1, I229N1, I233N1, I239N1, I251N0, I251N1, I251N2]
  Il := ![[], [I199N1], [], [I223N1], [], [I229N1], [I233N1], [I239N1], [], [I251N0, I251N1, I251N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
