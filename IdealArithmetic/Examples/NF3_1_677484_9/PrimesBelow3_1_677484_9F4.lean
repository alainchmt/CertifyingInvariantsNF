
import IdealArithmetic.Examples.NF3_1_677484_9.RI3_1_677484_9
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-92, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-92, 1, 0]] 
 ![![197, 0, 0], ![105, 1, 0], ![34, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-92, 1, 0], ![0, -92, 6], ![258, 36, -92]]]
  hmulB := by decide  
  f := ![![![2485, -27, 0], ![5319, 0, 0]], ![![1289, -14, 0], ![2759, 0, 0]], ![![498, 10, -1], ![1066, 33, 0]]]
  g := ![![![1, 0, 0], ![-105, 197, 0], ![-34, 0, 197]], ![![-1, 1, 0], ![48, -92, 6], ![-2, 36, -92]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![365, 14, -12]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![365, 14, -12]] 
 ![![197, 0, 0], ![116, 1, 0], ![187, 0, 1]] where
  M :=![![![365, 14, -12], ![-3096, -67, 84], ![3612, -12, -67]]]
  hmulB := by decide  
  f := ![![![5497, 1082, 372]], ![![3724, 733, 252]], ![![6635, 1306, 449]]]
  g := ![![![5, 14, -12], ![-56, -67, 84], ![89, -12, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-24, 1, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-24, 1, 0]] 
 ![![197, 0, 0], ![173, 1, 0], ![101, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-24, 1, 0], ![0, -24, 6], ![258, 36, -24]]]
  hmulB := by decide  
  f := ![![![3937, -164, 0], ![32308, 0, 0]], ![![3481, -145, 0], ![28566, 0, 0]], ![![2017, -80, -1], ![16552, 33, 0]]]
  g := ![![![1, 0, 0], ![-173, 197, 0], ![-101, 0, 197]], ![![-1, 1, 0], ![18, -24, 6], ![-18, 36, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-92, 1, 0]] ![![365, 14, -12]]
  ![![197, 0, 0], ![60, 4, 1]] where
 M := ![![![71905, 2758, -2364]], ![![-36676, -1355, 1188]]]
 hmul := by decide  
 g := ![![![![305, 10, -13], ![197, 0, 0]]], ![![![-188, -7, 6], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![60, 4, 1]] ![![197, 0, 0], ![-24, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-4728, 197, 0]], ![![11820, 788, 197], ![-1182, 0, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-24, 1, 0]]], ![![![60, 4, 1]], ![![-6, 0, 0]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [170, 107, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [123, 182, 134], [4, 16, 65], [0, 1]]
 g := ![![[66, 25, 14], [98, 32, 103], [99, 10, 52], [179, 123], [172, 57], [161, 10], [1]], ![[136, 97, 130, 176], [45, 14, 155, 105], [123, 21, 89, 192], [125, 86], [145, 9], [131, 29], [81, 69, 4, 194]], ![[11, 111, 94, 47], [152, 76, 81, 10], [184, 113, 116, 155], [56, 139], [111, 162], [86, 8], [59, 63, 57, 5]]]
 h' := ![![[123, 182, 134], [56, 55, 51], [85, 131, 74], [22, 9, 98], [76, 117, 116], [137, 140, 183], [29, 92, 127], [0, 1]], ![[4, 16, 65], [63, 115, 27], [75, 34, 32], [5, 179, 187], [165, 130, 22], [61, 100, 196], [178, 44, 32], [123, 182, 134]], ![[0, 1], [13, 29, 121], [44, 34, 93], [95, 11, 113], [137, 151, 61], [163, 158, 19], [183, 63, 40], [4, 16, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 146], []]
 b := ![[], [57, 168, 189], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [170, 107, 72, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3184, 199, 199]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16, 1, 1]
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


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [193, 34, 209, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 196, 103], [115, 14, 108], [0, 1]]
 g := ![![[193, 124, 107], [111, 60, 101], [21, 107], [189, 105], [114, 201, 64], [83, 4], [1]], ![[29, 104, 45, 100], [80, 208, 38, 45], [62, 107], [158, 182], [146, 183, 7, 65], [61, 109], [66, 109, 4, 169]], ![[195, 126, 143, 202], [74, 142, 114, 147], [], [176, 9], [182, 201, 45, 57], [46, 143], [24, 201, 30, 42]]]
 h' := ![![[98, 196, 103], [99, 154, 23], [152, 91, 34], [14, 73, 188], [153, 184, 59], [130, 35, 203], [18, 177, 2], [0, 1]], ![[115, 14, 108], [118, 11, 148], [72, 112, 143], [86, 171, 23], [14, 194, 155], [5, 108, 117], [54, 88, 113], [98, 196, 103]], ![[0, 1], [182, 46, 40], [137, 8, 34], [83, 178], [49, 44, 208], [204, 68, 102], [208, 157, 96], [115, 14, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131, 130], []]
 b := ![[], [9, 122, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [193, 34, 209, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-851807, 12660, 99381]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4037, 60, 471]
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


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [124, 166, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 153, 79], [104, 69, 144], [0, 1]]
 g := ![![[190, 54, 171], [79, 168, 188], [4, 135, 2], [54, 8, 60], [202, 110, 17], [218, 120], [1]], ![[34, 158, 136, 103], [21, 77, 86, 117], [205, 90, 101, 123], [64, 129, 47, 185], [40, 45, 73, 107], [2, 58], [218, 119, 89, 209]], ![[165, 156, 77, 39], [70, 34, 160, 202], [112, 172, 82, 197], [167, 210, 196, 188], [65, 198, 144, 58], [219, 55], [217, 43, 143, 14]]]
 h' := ![![[78, 153, 79], [16, 220, 49], [173, 26, 100], [217, 134, 208], [151, 136, 196], [163, 135, 169], [99, 57, 182], [0, 1]], ![[104, 69, 144], [74, 217, 22], [39, 42, 34], [44, 175, 185], [108, 97, 184], [95, 195, 26], [182, 50, 113], [78, 153, 79]], ![[0, 1], [174, 9, 152], [118, 155, 89], [83, 137, 53], [119, 213, 66], [123, 116, 28], [127, 116, 151], [104, 69, 144]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [177, 177], []]
 b := ![[], [76, 143, 201], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [124, 166, 41, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8474, 11819, -14718]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-38, 53, -66]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-69, -73, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-69, -73, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![158, 154, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-69, -73, 1], ![258, -33, -438], ![-18834, -2585, -33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-158, -154, 227]], ![![-1, -1, 1], ![306, 297, -438], ![-60, 11, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [203, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [125, 226], [0, 1]]
 g := ![![[166, 104], [160, 144], [133], [209], [16], [201, 196], [125, 1]], ![[0, 123], [0, 83], [133], [209], [16], [185, 31], [23, 226]]]
 h' := ![![[125, 226], [208, 51], [89, 12], [23, 157], [1, 182], [57, 223], [49, 213], [0, 1]], ![[0, 1], [0, 176], [0, 215], [126, 70], [51, 45], [11, 4], [115, 14], [125, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133]]
 b := ![[], [100, 180]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [203, 102, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1242, 275, 18]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -11, 18]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-16, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-16, 1, 0]] 
 ![![227, 0, 0], ![211, 1, 0], ![33, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-16, 1, 0], ![0, -16, 6], ![258, 36, -16]]]
  hmulB := by decide  
  f := ![![![1265, -79, 0], ![17933, 0, 0]], ![![1185, -74, 0], ![16799, 0, 0]], ![![187, -9, -1], ![2651, 38, 0]]]
  g := ![![![1, 0, 0], ![-211, 227, 0], ![-33, 0, 227]], ![![-1, 1, 0], ![14, -16, 6], ![-30, 36, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-69, -73, 1]] ![![227, 0, 0], ![-16, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-3632, 227, 0]], ![![-15663, -16571, 227], ![1362, 1135, -454]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-16, 1, 0]]], ![![![-69, -73, 1]], ![![6, 5, -2]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![481, -13, -5]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![481, -13, -5]] 
 ![![229, 0, 0], ![0, 229, 0], ![87, 140, 1]] where
  M :=![![![481, -13, -5], ![-1290, 301, -78], ![-3354, -683, 301]]]
  hmulB := by decide  
  f := ![![![163, 32, 11]], ![![2838, 559, 192]], ![![1833, 361, 124]]]
  g := ![![![4, 3, -5], ![24, 49, -78], ![-129, -187, 301]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [47, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [204, 228], [0, 1]]
 g := ![![[59, 17], [186], [223, 226], [202], [159], [89, 202], [204, 1]], ![[92, 212], [186], [69, 3], [202], [159], [77, 27], [179, 228]]]
 h' := ![![[204, 228], [21, 186], [53, 145], [82, 40], [141, 109], [168, 173], [30, 120], [0, 1]], ![[0, 1], [180, 43], [92, 84], [227, 189], [164, 120], [194, 56], [7, 109], [204, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [23, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [47, 25, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![563, 90, 17]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, -10, 17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 32, 11]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![163, 32, 11]] 
 ![![229, 0, 0], ![76, 1, 0], ![106, 0, 1]] where
  M :=![![![163, 32, 11], ![2838, 559, 192], ![8256, 1625, 559]]]
  hmulB := by decide  
  f := ![![![481, -13, -5]], ![![154, -3, -2]], ![![208, -9, -1]]]
  g := ![![![-15, 32, 11], ![-262, 559, 192], ![-762, 1625, 559]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![481, -13, -5]] ![![163, 32, 11]]
  ![![229, 0, 0]] where
 M := ![![![229, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB233I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 232 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 232 (by omega)

def PB233I4 : PrimesBelowBoundCertificateInterval O 193 232 233 where
  m := 6
  g := ![3, 1, 1, 1, 2, 2]
  P := ![197, 199, 211, 223, 227, 229]
  hP := PB233I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0]
    · exact ![I211N0]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![197, 197, 197]
    · exact ![7880599]
    · exact ![9393931]
    · exact ![11089567]
    · exact ![51529, 227]
    · exact ![52441, 229]
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
      exact NI229N1
  β := ![I197N0, I197N1, I197N2, I227N1, I229N1]
  Il := ![[I197N0, I197N1, I197N2], [], [], [], [I227N1], [I229N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
