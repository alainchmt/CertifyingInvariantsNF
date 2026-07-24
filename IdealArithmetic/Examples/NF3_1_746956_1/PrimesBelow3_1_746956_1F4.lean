
import IdealArithmetic.Examples.NF3_1_746956_1.RI3_1_746956_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![112, 7, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![112, 7, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![112, 7, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![112, 7, 1], ![99, 117, 73], ![667, -143, 64]]]
  hmulB := by decide  
  f := ![![![-111, -7, -1], ![197, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-112, -7, 197]], ![![0, 0, 1], ![-41, -2, 73], ![-33, -3, 64]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [111, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [165, 196], [0, 1]]
 g := ![![[105, 196], [25], [104, 100], [150], [23], [62], [165, 1]], ![[137, 1], [25], [56, 97], [150], [23], [62], [133, 196]]]
 h' := ![![[165, 196], [117, 183], [79, 192], [150, 187], [45, 97], [49, 107], [6, 125], [0, 1]], ![[0, 1], [171, 14], [42, 5], [76, 10], [93, 100], [171, 90], [143, 72], [165, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [182, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [111, 32, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2704, -422, -2959]
  a := ![1, -5, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1696, 103, -2959]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-73, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-73, 1, 0]] 
 ![![197, 0, 0], ![124, 1, 0], ![133, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-73, 1, 0], ![-1, -69, 11], ![106, -23, -77]]]
  hmulB := by decide  
  f := ![![![-26640, -1853343, 295460], ![591, -5291420, 0]], ![![-16759, -1166516, 185966], ![395, -3330482, 0]], ![![-17965, -1251242, 199473], ![454, -3572380, 0]]]
  g := ![![![1, 0, 0], ![-124, 197, 0], ![-133, 0, 197]], ![![-1, 1, 0], ![36, -69, 11], ![67, -23, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![112, 7, 1]] ![![197, 0, 0], ![-73, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-14381, 197, 0]], ![![22064, 1379, 197], ![-8077, -394, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-73, 1, 0]]], ![![![112, 7, 1]], ![![-41, -2, 0]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [48, 161, 191, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 90, 60], [193, 108, 139], [0, 1]]
 g := ![![[8, 184, 80], [122, 58, 64], [16, 135, 114], [86, 9], [76, 66], [125, 64], [1]], ![[64, 64, 14, 134], [98, 188, 78, 119], [29, 128, 184, 54], [30, 177], [48, 50], [165, 8], [23, 75, 167, 85]], ![[156, 107, 39, 80], [25, 182, 33, 26], [72, 137, 47, 63], [146, 184], [40, 187], [30, 29], [2, 180, 177, 114]]]
 h' := ![![[14, 90, 60], [114, 49, 105], [28, 103, 191], [76, 93, 121], [194, 135, 3], [85, 20, 128], [151, 38, 8], [0, 1]], ![[193, 108, 139], [152, 175, 151], [115, 107, 142], [57, 173, 141], [30, 89, 66], [155, 153, 99], [48, 46, 159], [14, 90, 60]], ![[0, 1], [44, 174, 142], [43, 188, 65], [68, 132, 136], [67, 174, 130], [185, 26, 171], [86, 115, 32], [193, 108, 139]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 26], []]
 b := ![[], [184, 14, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [48, 161, 191, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![47411949, -11082708, 10118354]
  a := ![-3, 9, 32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![238251, -55692, 50846]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![891, 29, 38]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![891, 29, 38]] 
 ![![211, 0, 0], ![0, 211, 0], ![29, 184, 1]] where
  M :=![![![891, 29, 38], ![3999, 133, 167], ![224, 17, 15]]]
  hmulB := by decide  
  f := ![![![-4, 1, -1]], ![![-107, 23, 15]], ![![-93, 20, 13]]]
  g := ![![![-1, -33, 38], ![-4, -145, 167], ![-1, -13, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [158, 147, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 210], [0, 1]]
 g := ![![[45, 44], [123, 204], [53], [188], [119, 173], [188], [64, 1]], ![[118, 167], [97, 7], [53], [188], [8, 38], [188], [128, 210]]]
 h' := ![![[64, 210], [189, 39], [150, 170], [154, 106], [188, 140], [92, 54], [16, 140], [0, 1]], ![[0, 1], [153, 172], [58, 41], [186, 105], [75, 71], [172, 157], [114, 71], [64, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [163]]
 b := ![[], [135, 187]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [158, 147, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![639242, -121927, -114496]
  a := ![1, -67, -75]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18766, 99267, -114496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, -1, 1]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![4, -1, 1]] 
 ![![211, 0, 0], ![90, 1, 0], ![94, 0, 1]] where
  M :=![![![4, -1, 1], ![107, -23, -15], ![-181, 41, -12]]]
  hmulB := by decide  
  f := ![![![-891, -29, -38]], ![![-399, -13, -17]], ![![-398, -13, -17]]]
  g := ![![![0, -1, 1], ![17, -23, -15], ![-13, 41, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![891, 29, 38]] ![![4, -1, 1]]
  ![![211, 0, 0]] where
 M := ![![![-211, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [191, 7, 176, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [131, 162, 100], [139, 60, 123], [0, 1]]
 g := ![![[25, 31, 74], [169, 175, 55], [122, 192, 105], [207, 109, 172], [1, 86, 50], [139, 202], [1]], ![[199, 148, 180, 7], [213, 134, 2, 7], [18, 82, 138, 49], [27, 219, 93, 43], [138, 106, 179, 212], [154, 58], [130, 121, 12, 68]], ![[219, 102, 83, 159], [128, 2, 49, 92], [218, 196, 38, 12], [61, 54, 156, 87], [73, 107, 208, 158], [197, 178], [143, 53, 93, 155]]]
 h' := ![![[131, 162, 100], [56, 15, 175], [113, 57, 151], [157, 164, 95], [32, 197, 29], [120, 137, 148], [32, 216, 47], [0, 1]], ![[139, 60, 123], [19, 93, 181], [117, 42, 42], [172, 43, 23], [112, 85, 32], [193, 131, 57], [174, 109, 113], [131, 162, 100]], ![[0, 1], [25, 115, 90], [179, 124, 30], [65, 16, 105], [168, 164, 162], [191, 178, 18], [146, 121, 63], [139, 60, 123]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [175, 136], []]
 b := ![[], [150, 197, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [191, 7, 176, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-44980661, 11293612, -18649044]
  a := ![3, -10, -32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-201707, 50644, -83628]
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [145, 51, 205, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [157, 46, 200], [92, 180, 27], [0, 1]]
 g := ![![[204, 49, 173], [146, 5, 189], [192, 79], [110, 221], [], [22, 5, 30], [1]], ![[218, 5, 158, 111], [82, 221, 141, 91], [63, 63], [151, 110], [213, 134], [91, 159, 218, 115], [65, 94, 131, 66]], ![[31, 49, 51, 62], [200, 185, 226, 25], [13, 181], [92, 36], [119, 134], [93, 46, 194, 33], [155, 175, 179, 161]]]
 h' := ![![[157, 46, 200], [168, 145, 207], [215, 155, 125], [19, 157, 144], [144, 84, 69], [215, 110], [82, 176, 22], [0, 1]], ![[92, 180, 27], [31, 99, 203], [48, 18, 155], [199, 144, 116], [23, 9, 164], [6, 66, 208], [106, 47, 116], [157, 46, 200]], ![[0, 1], [168, 210, 44], [13, 54, 174], [189, 153, 194], [96, 134, 221], [120, 51, 19], [76, 4, 89], [92, 180, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [157, 144], []]
 b := ![[], [189, 158, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [145, 51, 205, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![62879, 88303, -1188572]
  a := ![1, -5, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![277, 389, -5236]
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


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [220, 139, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 7, 68], [151, 221, 161], [0, 1]]
 g := ![![[180, 228, 60], [211, 111], [152, 18, 103], [3, 15], [100, 135], [222, 199, 57], [1]], ![[68, 174, 60, 147], [178, 184], [114, 176, 147, 185], [161, 165], [19, 91], [77, 227, 147, 85], [192, 217, 9, 15]], ![[147, 7, 42, 130], [221, 181], [134, 52, 168, 68], [64, 76], [207, 132], [177, 44, 57, 48], [210, 158, 88, 214]]]
 h' := ![![[17, 7, 68], [103, 47, 17], [223, 97, 180], [192, 15, 65], [60, 54, 123], [166, 97, 89], [9, 90, 168], [0, 1]], ![[151, 221, 161], [47, 143, 83], [174, 124, 118], [101, 0, 42], [207, 56, 169], [6, 42, 159], [0, 112, 196], [17, 7, 68]], ![[0, 1], [176, 39, 129], [146, 8, 160], [117, 214, 122], [122, 119, 166], [159, 90, 210], [223, 27, 94], [151, 221, 161]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 159], []]
 b := ![[], [104, 117, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [220, 139, 61, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5647827, 1824672, -1527888]
  a := ![-1, 24, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24663, 7968, -6672]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![97, 103, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![97, 103, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![97, 103, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![97, 103, 1], ![3, 486, 1129], ![10843, -2351, -335]]]
  hmulB := by decide  
  f := ![![![-96, -103, -1], ![233, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-97, -103, 233]], ![![0, 0, 1], ![-470, -497, 1129], ![186, 138, -335]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [222, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [154, 232], [0, 1]]
 g := ![![[14, 204], [195], [219], [201, 32], [182], [48, 123], [154, 1]], ![[208, 29], [195], [219], [3, 201], [182], [117, 110], [75, 232]]]
 h' := ![![[154, 232], [78, 196], [27, 112], [114, 59], [21, 126], [62, 132], [63, 194], [0, 1]], ![[0, 1], [205, 37], [33, 121], [113, 174], [86, 107], [119, 101], [115, 39], [154, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [156]]
 b := ![[], [52, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [222, 79, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5414, 1342, -4000]
  a := ![1, -2, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1642, 1774, -4000]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![36, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![36, 1, 0]] 
 ![![233, 0, 0], ![36, 1, 0], ![102, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![36, 1, 0], ![-1, 40, 11], ![106, -23, 32]]]
  hmulB := by decide  
  f := ![![![-27500, 1097158, 301719], ![466, -6390957, 0]], ![![-4273, 169479, 46607], ![234, -987221, 0]], ![![-12072, 480300, 132083], ![420, -2797758, 0]]]
  g := ![![![1, 0, 0], ![-36, 233, 0], ![-102, 0, 233]], ![![0, 1, 0], ![-11, 40, 11], ![-10, -23, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![97, 103, 1]] ![![233, 0, 0], ![36, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![8388, 233, 0]], ![![22601, 23999, 233], ![3495, 4194, 1165]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![36, 1, 0]]], ![![![97, 103, 1]], ![![15, 18, 5]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-50, -66, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-50, -66, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![189, 173, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-50, -66, 1], ![172, -337, -730], ![-7071, 1536, 194]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-189, -173, 239]], ![![-1, -1, 1], ![578, 527, -730], ![-183, -134, 194]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [83, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [157, 238], [0, 1]]
 g := ![![[168, 72], [129, 226], [108, 133], [87, 4], [183], [228, 211], [157, 1]], ![[0, 167], [0, 13], [196, 106], [237, 235], [183], [134, 28], [75, 238]]]
 h' := ![![[157, 238], [48, 123], [118, 153], [188, 206], [44, 2], [196, 209], [114, 188], [0, 1]], ![[0, 1], [0, 116], [0, 86], [26, 33], [119, 237], [27, 30], [233, 51], [157, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [209, 145]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [83, 82, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5518, 630, -8657]
  a := ![-2, 9, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6869, 6269, -8657]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![13, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![13, 1, 0]] 
 ![![239, 0, 0], ![13, 1, 0], ![45, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![13, 1, 0], ![-1, 17, 11], ![106, -23, 9]]]
  hmulB := by decide  
  f := ![![![-16769, 284646, 184184], ![478, -4001816, 0]], ![![-923, 15469, 10010], ![240, -217490, 0]], ![![-3163, 53594, 34679], ![194, -753480, 0]]]
  g := ![![![1, 0, 0], ![-13, 239, 0], ![-45, 0, 239]], ![![0, 1, 0], ![-3, 17, 11], ![0, -23, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-50, -66, 1]] ![![239, 0, 0], ![13, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![3107, 239, 0]], ![![-11950, -15774, 239], ![-478, -1195, -717]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![13, 1, 0]]], ![![![-50, -66, 1]], ![![-2, -5, -3]]]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![85, 1, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![85, 1, 0]] 
 ![![241, 0, 0], ![85, 1, 0], ![79, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![85, 1, 0], ![-1, 89, 11], ![106, -23, 81]]]
  hmulB := by decide  
  f := ![![![36907, -3269502, -404096], ![-482, 8853376, 0]], ![![12956, -1153084, -142516], ![1, 3122396, 0]], ![![12053, -1071746, -132463], ![-30, 2902144, 0]]]
  g := ![![![1, 0, 0], ![-85, 241, 0], ![-79, 0, 241]], ![![0, 1, 0], ![-35, 89, 11], ![-18, -23, 81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N0 : Nat.card (O ⧸ I241N0) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N0)

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := prime_ideal_of_norm_prime hp241.out _ NI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-79, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-79, 1, 0]] 
 ![![241, 0, 0], ![162, 1, 0], ![9, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-79, 1, 0], ![-1, -75, 11], ![106, -23, -83]]]
  hmulB := by decide  
  f := ![![![9456, 709125, -104005], ![0, 2278655, 0]], ![![6356, 476625, -69905], ![1, 1531555, 0]], ![![420, 26481, -3884], ![204, 85095, 0]]]
  g := ![![![1, 0, 0], ![-162, 241, 0], ![-9, 0, 241]], ![![-1, 1, 0], ![50, -75, 11], ![19, -23, -83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-6, 1, 0]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-6, 1, 0]] 
 ![![241, 0, 0], ![235, 1, 0], ![196, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-6, 1, 0], ![-1, -2, 11], ![106, -23, -10]]]
  hmulB := by decide  
  f := ![![![-8873, -17761, 97680], ![241, -2140080, 0]], ![![-8651, -17317, 95238], ![242, -2086578, 0]], ![![-7214, -14445, 79441], ![285, -1740480, 0]]]
  g := ![![![1, 0, 0], ![-235, 241, 0], ![-196, 0, 241]], ![![-1, 1, 0], ![-7, -2, 11], ![31, -23, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![85, 1, 0]] ![![241, 0, 0], ![-79, 1, 0]]
  ![![241, 0, 0], ![-19, -21, 1]] where
 M := ![![![58081, 0, 0], ![-19039, 241, 0]], ![![20485, 241, 0], ![-6716, 10, 11]]]
 hmul := by decide  
 g := ![![![![241, 0, 0], ![0, 0, 0]], ![![-60, 22, -1], ![241, 0, 0]]], ![![![85, 1, 0], ![0, 0, 0]], ![![-27, 1, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![-19, -21, 1]] ![![241, 0, 0], ![-6, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![-1446, 241, 0]], ![![-4579, -5061, 241], ![241, 0, -241]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![-6, 1, 0]]], ![![![-19, -21, 1]], ![![1, 0, -1]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1, I241N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
    exact isPrimeI241N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0 ⊙ MulI241N1)


lemma PB245I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 244 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 244 (by omega)

def PB245I4 : PrimesBelowBoundCertificateInterval O 193 244 245 where
  m := 9
  g := ![2, 1, 2, 1, 1, 1, 2, 2, 3]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241]
  hP := PB245I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1, I241N2]
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
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![11697083]
    · exact ![12008989]
    · exact ![54289, 233]
    · exact ![57121, 239]
    · exact ![241, 241, 241]
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
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
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
      exact NI241N1
      exact NI241N2
  β := ![I197N1, I211N1, I233N1, I239N1, I241N0, I241N1, I241N2]
  Il := ![[I197N1], [], [I211N1], [], [], [], [I233N1], [I239N1], [I241N0, I241N1, I241N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
