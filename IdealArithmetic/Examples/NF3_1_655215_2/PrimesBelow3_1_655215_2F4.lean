
import IdealArithmetic.Examples.NF3_1_655215_2.RI3_1_655215_2
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [69, 19, 186, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 112, 153], [120, 84, 44], [0, 1]]
 g := ![![[13, 23, 92], [40, 196], [196, 121, 148], [170, 171], [29, 107], [125, 121], [1]], ![[153, 181, 134, 71], [195, 15], [14, 65, 102, 56], [196, 15], [32, 136], [34, 169], [76, 2, 107, 117]], ![[7, 125, 24, 118], [95, 163], [126, 31, 10, 12], [63, 182], [134, 175], [112, 4], [118, 148, 192, 80]]]
 h' := ![![[88, 112, 153], [31, 81, 17], [69, 37, 14], [129, 128, 98], [32, 86, 163], [76, 172, 86], [128, 178, 11], [0, 1]], ![[120, 84, 44], [48, 114, 31], [111, 139, 139], [124, 91, 39], [152, 165, 58], [28, 9, 50], [124, 2, 184], [88, 112, 153]], ![[0, 1], [149, 2, 149], [20, 21, 44], [23, 175, 60], [6, 143, 173], [92, 16, 61], [48, 17, 2], [120, 84, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 188], []]
 b := ![[], [125, 177, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [69, 19, 186, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![141249, 67768, -92590]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![717, 344, -470]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0]] 
 ![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [8, 109, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 163, 174], [74, 35, 25], [0, 1]]
 g := ![![[144, 78, 126], [21, 172, 184], [83, 189, 165], [35, 57], [86, 65], [124, 123], [1]], ![[40, 184, 49, 67], [76, 134, 155, 195], [93, 79, 103, 168], [65, 94], [194, 106], [108, 162], [137, 61, 152, 96]], ![[183, 112, 166, 16], [78, 18, 106, 40], [139, 142, 73, 72], [39, 13], [180, 31], [29, 116], [52, 186, 162, 103]]]
 h' := ![![[42, 163, 174], [31, 28, 46], [132, 60, 69], [120, 20, 168], [20, 162, 183], [67, 179, 57], [191, 90, 116], [0, 1]], ![[74, 35, 25], [165, 166, 114], [94, 198, 119], [1, 176, 7], [83, 119, 166], [21, 29, 107], [158, 32, 19], [42, 163, 174]], ![[0, 1], [168, 5, 39], [177, 140, 11], [131, 3, 24], [170, 117, 49], [139, 190, 35], [42, 77, 64], [74, 35, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 11], []]
 b := ![[], [144, 84, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [8, 109, 83, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![393821, -154623, 34626]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1979, -777, 174]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![91, 1, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![91, 1, 0]] 
 ![![211, 0, 0], ![91, 1, 0], ![34, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![91, 1, 0], ![0, 92, 2], ![120, -35, 91]]]
  hmulB := by decide  
  f := ![![![12559, 138, 0], ![-29118, 0, 0]], ![![5369, 59, 0], ![-12448, 0, 0]], ![![2022, -24, -1], ![-4688, 106, 0]]]
  g := ![![![1, 0, 0], ![-91, 211, 0], ![-34, 0, 211]], ![![0, 1, 0], ![-40, 92, 2], ![1, -35, 91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N0 : Nat.card (O ⧸ I211N0) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N0)

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := prime_ideal_of_norm_prime hp211.out _ NI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-48, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-48, 1, 0]] 
 ![![211, 0, 0], ![163, 1, 0], ![138, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-48, 1, 0], ![0, -47, 2], ![120, -35, -48]]]
  hmulB := by decide  
  f := ![![![1249, -26, 0], ![5486, 0, 0]], ![![1009, -21, 0], ![4432, 0, 0]], ![![846, 6, -1], ![3716, 106, 0]]]
  g := ![![![1, 0, 0], ![-163, 211, 0], ![-138, 0, 211]], ![![-1, 1, 0], ![35, -47, 2], ![59, -35, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-44, 1, 0]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-44, 1, 0]] 
 ![![211, 0, 0], ![167, 1, 0], ![109, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-44, 1, 0], ![0, -43, 2], ![120, -35, -44]]]
  hmulB := by decide  
  f := ![![![1937, -44, 0], ![9284, 0, 0]], ![![1541, -35, 0], ![7386, 0, 0]], ![![1039, -2, -1], ![4980, 106, 0]]]
  g := ![![![1, 0, 0], ![-167, 211, 0], ![-109, 0, 211]], ![![-1, 1, 0], ![33, -43, 2], ![51, -35, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![91, 1, 0]] ![![211, 0, 0], ![-48, 1, 0]]
  ![![211, 0, 0], ![-74, 22, 1]] where
 M := ![![![44521, 0, 0], ![-10128, 211, 0]], ![![19201, 211, 0], ![-4368, 44, 2]]]
 hmul := by decide  
 g := ![![![![211, 0, 0], ![0, 0, 0]], ![![26, -21, -1], ![211, 0, 0]]], ![![![91, 1, 0], ![0, 0, 0]], ![![54, -22, -1], ![213, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-74, 22, 1]] ![![211, 0, 0], ![-44, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-9284, 211, 0]], ![![-15614, 4642, 211], ![3376, -1055, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-44, 1, 0]]], ![![![-74, 22, 1]], ![![16, -5, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1, I211N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
    exact isPrimeI211N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0 ⊙ MulI211N1)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![127, 83, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![127, 83, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![127, 83, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![127, 83, 1], ![120, 175, 166], ![9900, -2845, 92]]]
  hmulB := by decide  
  f := ![![![-126, -83, -1], ![223, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-127, -83, 223]], ![![0, 0, 1], ![-94, -61, 166], ![-8, -47, 92]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [105, 189, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 222], [0, 1]]
 g := ![![[91, 17], [8, 179], [217, 211], [167, 156], [211, 63], [82], [34, 1]], ![[0, 206], [73, 44], [32, 12], [119, 67], [123, 160], [82], [68, 222]]]
 h' := ![![[34, 222], [52, 169], [184, 198], [82, 65], [145, 143], [91, 145], [221, 159], [0, 1]], ![[0, 1], [0, 54], [3, 25], [62, 158], [101, 80], [115, 78], [52, 64], [34, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [183]]
 b := ![[], [117, 203]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [105, 189, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7955, 60, -96]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19, 36, -96]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![57, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![57, 1, 0]] 
 ![![223, 0, 0], ![57, 1, 0], ![131, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![57, 1, 0], ![0, 58, 2], ![120, -35, 57]]]
  hmulB := by decide  
  f := ![![![4561, 80, 0], ![-17840, 0, 0]], ![![1083, 19, 0], ![-4236, 0, 0]], ![![2573, 16, -1], ![-10064, 112, 0]]]
  g := ![![![1, 0, 0], ![-57, 223, 0], ![-131, 0, 223]], ![![0, 1, 0], ![-16, 58, 2], ![-24, -35, 57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![127, 83, 1]] ![![223, 0, 0], ![57, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![12711, 223, 0]], ![![28321, 18509, 223], ![7359, 4906, 223]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![57, 1, 0]]], ![![![127, 83, 1]], ![![33, 22, 1]]]]
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [27, 98, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 30, 133], [37, 196, 94], [0, 1]]
 g := ![![[22, 43, 161], [92, 218, 108], [111, 219], [77, 189], [131, 222], [86, 36, 167], [1]], ![[161, 123, 63, 27], [190, 92, 68, 108], [98, 169], [28, 207], [87, 175], [47, 14, 121, 177], [21, 81, 40, 9]], ![[223, 149, 84, 35], [8, 1, 63, 194], [31, 33], [68, 3], [192, 29], [52, 59, 152, 157], [161, 96, 11, 218]]]
 h' := ![![[87, 30, 133], [13, 212, 36], [86, 112, 154], [141, 167, 197], [75, 149, 125], [175, 182, 201], [200, 129, 124], [0, 1]], ![[37, 196, 94], [31, 206, 67], [167, 12, 134], [61, 226, 214], [96, 190, 52], [185, 194, 42], [90, 51, 147], [87, 30, 133]], ![[0, 1], [42, 36, 124], [120, 103, 166], [7, 61, 43], [150, 115, 50], [106, 78, 211], [225, 47, 183], [37, 196, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122, 175], []]
 b := ![[], [90, 214, 154], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [27, 98, 103, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-438791, 421312, -252878]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1933, 1856, -1114]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0]] 
 ![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [221, 86, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 25, 129], [157, 203, 100], [0, 1]]
 g := ![![[35, 166, 154], [130, 151], [207, 28, 159], [29, 224], [156, 203], [56, 76, 212], [1]], ![[110, 171, 129, 125], [138, 144], [221, 20, 10, 146], [80, 1], [97, 154], [119, 2, 1, 94], [182, 186, 38, 43]], ![[56, 72, 133, 33], [116, 118], [64, 116, 214, 171], [198, 70], [23, 176], [56, 80, 125, 214], [45, 0, 190, 186]]]
 h' := ![![[51, 25, 129], [185, 123, 200], [53, 119, 36], [221, 156, 173], [203, 98, 37], [219, 207, 165], [8, 143, 208], [0, 1]], ![[157, 203, 100], [94, 26, 133], [140, 40, 217], [2, 18, 54], [7, 165, 1], [190, 215, 200], [142, 1, 215], [51, 25, 129]], ![[0, 1], [197, 80, 125], [52, 70, 205], [191, 55, 2], [50, 195, 191], [211, 36, 93], [153, 85, 35], [157, 203, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [227, 203], []]
 b := ![[], [94, 211, 215], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [221, 86, 21, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7099, 47174, -42136]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31, 206, -184]
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



lemma PB230I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 229 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 229 (by omega)

def PB230I4 : PrimesBelowBoundCertificateInterval O 193 229 230 where
  m := 6
  g := ![1, 1, 3, 2, 1, 1]
  P := ![197, 199, 211, 223, 227, 229]
  hP := PB230I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0, I223N1]
    · exact ![I227N0]
    · exact ![I229N0]
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
    · exact ![7645373]
    · exact ![7880599]
    · exact ![211, 211, 211]
    · exact ![49729, 223]
    · exact ![11697083]
    · exact ![12008989]
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
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
      exact NI211N2
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
  β := ![I211N0, I211N1, I211N2, I223N1]
  Il := ![[], [], [I211N0, I211N1, I211N2], [I223N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
