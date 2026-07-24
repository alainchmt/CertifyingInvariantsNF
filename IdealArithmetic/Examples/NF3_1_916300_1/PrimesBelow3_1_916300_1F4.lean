
import IdealArithmetic.Examples.NF3_1_916300_1.RI3_1_916300_1
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [174, 159, 105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [137, 169, 27], [152, 27, 170], [0, 1]]
 g := ![![[143, 127, 61], [15, 156], [186, 6, 28], [61, 92], [8, 4], [44, 190], [1]], ![[64, 94, 21, 159], [21, 39], [192, 38, 3, 166], [51, 174], [168, 144], [34, 114], [93, 13, 43, 180]], ![[89, 74, 171, 129], [184, 154], [22, 33, 190, 78], [96, 175], [100, 100], [90, 181], [63, 108, 134, 17]]]
 h' := ![![[137, 169, 27], [132, 158, 88], [141, 92, 133], [136, 177, 15], [30, 195, 180], [162, 107, 2], [23, 38, 92], [0, 1]], ![[152, 27, 170], [66, 84, 141], [78, 145, 165], [17, 30, 62], [82, 0, 78], [54, 151, 185], [81, 85, 161], [137, 169, 27]], ![[0, 1], [121, 152, 165], [115, 157, 96], [41, 187, 120], [0, 2, 136], [8, 136, 10], [156, 74, 141], [152, 27, 170]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 76], []]
 b := ![[], [108, 78, 165], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [174, 159, 105, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![59691, 3743, -7092]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![303, 19, -36]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![2, -24, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![2, -24, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![2, 175, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![2, -24, 1], ![153, -45, -23], ![-3519, 1234, -68]]]
  hmulB := by decide  
  f := ![![![-1, 24, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -175, 199]], ![![0, -1, 1], ![1, 20, -23], ![-17, 66, -68]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [79, 125, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 198], [0, 1]]
 g := ![![[57, 131], [117, 28], [32, 91], [132], [2], [178], [74, 1]], ![[0, 68], [0, 171], [0, 108], [132], [2], [178], [148, 198]]]
 h' := ![![[74, 198], [110, 176], [59, 174], [152, 84], [113, 172], [120, 20], [124, 24], [0, 1]], ![[0, 1], [0, 23], [0, 25], [0, 115], [105, 27], [8, 179], [109, 175], [74, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114]]
 b := ![[], [80, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [79, 125, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-504, 1272, -53]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, 53, -53]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![23, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![23, 1, 0]] 
 ![![199, 0, 0], ![23, 1, 0], ![68, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![23, 1, 0], ![0, 23, 1], ![153, -47, 24]]]
  hmulB := by decide  
  f := ![![![553, 24, 0], ![-4776, 0, 0]], ![![23, 1, 0], ![-198, 0, 0]], ![![164, 7, 0], ![-1416, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 199, 0], ![-68, 0, 199]], ![![0, 1, 0], ![-3, 23, 1], ![-2, -47, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![2, -24, 1]] ![![199, 0, 0], ![23, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![4577, 199, 0]], ![![398, -4776, 199], ![199, -597, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![23, 1, 0]]], ![![![2, -24, 1]], ![![1, -3, 0]]]]
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


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [196, 86, 98, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [169, 143, 35], [155, 67, 176], [0, 1]]
 g := ![![[166, 181, 20], [25, 85, 196], [74, 209], [155, 79], [13, 26, 117], [55, 109], [1]], ![[39, 197, 166, 94], [210, 91, 79, 140], [66, 125], [61, 173], [54, 198, 40, 26], [107, 20], [76, 85, 28, 42]], ![[41, 20, 150, 150], [74, 112, 131, 24], [80, 16], [114, 62], [160, 157, 30, 189], [195, 180], [160, 164, 95, 169]]]
 h' := ![![[169, 143, 35], [164, 48, 130], [135, 57, 197], [49, 12, 118], [195, 141, 135], [206, 22, 31], [15, 125, 113], [0, 1]], ![[155, 67, 176], [148, 66, 51], [155, 99, 2], [208, 194, 97], [83, 54, 54], [116, 207, 104], [58, 124, 130], [169, 143, 35]], ![[0, 1], [157, 97, 30], [53, 55, 12], [142, 5, 207], [139, 16, 22], [196, 193, 76], [15, 173, 179], [155, 67, 176]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118, 77], []]
 b := ![[], [204, 95, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [196, 86, 98, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![117738, -2532, 2532]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![558, -12, 12]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![98, 1, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![98, 1, 0]] 
 ![![223, 0, 0], ![98, 1, 0], ![208, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![98, 1, 0], ![0, 98, 1], ![153, -47, 99]]]
  hmulB := by decide  
  f := ![![![4901, 50, 0], ![-11150, 0, 0]], ![![2058, 21, 0], ![-4682, 0, 0]], ![![4552, 46, 0], ![-10356, 1, 0]]]
  g := ![![![1, 0, 0], ![-98, 223, 0], ![-208, 0, 223]], ![![0, 1, 0], ![-44, 98, 1], ![-71, -47, 99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N0 : Nat.card (O ⧸ I223N0) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N0)

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := prime_ideal_of_norm_prime hp223.out _ NI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-172, 62, -1]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-172, 62, -1]] 
 ![![223, 0, 0], ![151, 1, 0], ![168, 0, 1]] where
  M :=![![![-172, 62, -1], ![-153, -125, 61], ![9333, -3020, -64]]]
  hmulB := by decide  
  f := ![![![-192220, -6988, -3657]], ![![-132667, -4823, -2524]], ![![-152115, -5530, -2894]]]
  g := ![![![-42, 62, -1], ![38, -125, 61], ![2135, -3020, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-27, 1, 0]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-27, 1, 0]] 
 ![![223, 0, 0], ![196, 1, 0], ![163, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-27, 1, 0], ![0, -27, 1], ![153, -47, -26]]]
  hmulB := by decide  
  f := ![![![5347, -198, 0], ![44154, 0, 0]], ![![4672, -173, 0], ![38580, 0, 0]], ![![3919, -145, 0], ![32362, 1, 0]]]
  g := ![![![1, 0, 0], ![-196, 223, 0], ![-163, 0, 223]], ![![-1, 1, 0], ![23, -27, 1], ![61, -47, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![98, 1, 0]] ![![-172, 62, -1]]
  ![![223, 0, 0], ![80, 26, 1]] where
 M := ![![![-38356, 13826, -223]], ![![-17009, 5951, -37]]]
 hmul := by decide  
 g := ![![![![-172, 62, -1], ![0, 0, 0]]], ![![![-143, 5, -1], ![186, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![80, 26, 1]] ![![223, 0, 0], ![-27, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![-6021, 223, 0]], ![![17840, 5798, 223], ![-2007, -669, 0]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![-27, 1, 0]]], ![![![80, 26, 1]], ![![-9, -3, 0]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0]] 
 ![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [53, 132, 171, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [142, 66, 221], [141, 160, 6], [0, 1]]
 g := ![![[53, 7, 62], [64, 8, 82], [129, 129], [133, 71], [207, 186], [147, 116, 185], [1]], ![[10, 162, 106, 192], [69, 72, 82, 90], [17, 177], [179, 177], [16, 16], [74, 126, 45, 195], [200, 38, 26, 11]], ![[84, 38, 134, 162], [67, 145, 140, 72], [9, 166], [51, 172], [164, 212], [113, 174, 207, 88], [126, 86, 93, 216]]]
 h' := ![![[142, 66, 221], [13, 65, 17], [159, 95, 38], [169, 177, 105], [33, 195, 170], [154, 184, 58], [174, 95, 56], [0, 1]], ![[141, 160, 6], [123, 213, 60], [220, 81, 62], [126, 214, 75], [83, 21, 152], [134, 117, 4], [206, 184, 218], [142, 66, 221]], ![[0, 1], [157, 176, 150], [146, 51, 127], [13, 63, 47], [197, 11, 132], [221, 153, 165], [130, 175, 180], [141, 160, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [143, 182], []]
 b := ![[], [212, 41, 106], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [53, 132, 171, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-358887, 543211, -136427]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1581, 2393, -601]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![6, 1, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![6, 1, 0]] 
 ![![229, 0, 0], ![6, 1, 0], ![193, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![6, 1, 0], ![0, 6, 1], ![153, -47, 7]]]
  hmulB := by decide  
  f := ![![![1087, 181, 0], ![-41449, 0, 0]], ![![18, 3, 0], ![-686, 0, 0]], ![![919, 153, 0], ![-35043, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 229, 0], ![-193, 0, 229]], ![![0, 1, 0], ![-1, 6, 1], ![-4, -47, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N0 : Nat.card (O ⧸ I229N0) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N0)

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := prime_ideal_of_norm_prime hp229.out _ NI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![93, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![93, 1, 0]] 
 ![![229, 0, 0], ![93, 1, 0], ![53, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![93, 1, 0], ![0, 93, 1], ![153, -47, 94]]]
  hmulB := by decide  
  f := ![![![7162, 77, 0], ![-17633, 0, 0]], ![![2976, 32, 0], ![-7327, 0, 0]], ![![1526, 16, 0], ![-3757, 1, 0]]]
  g := ![![![1, 0, 0], ![-93, 229, 0], ![-53, 0, 229]], ![![0, 1, 0], ![-38, 93, 1], ![-2, -47, 94]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-100, 1, 0]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-100, 1, 0]] 
 ![![229, 0, 0], ![129, 1, 0], ![76, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-100, 1, 0], ![0, -100, 1], ![153, -47, -99]]]
  hmulB := by decide  
  f := ![![![10701, -107, 0], ![24503, 0, 0]], ![![6201, -62, 0], ![14199, 0, 0]], ![![3644, -36, 0], ![8344, 1, 0]]]
  g := ![![![1, 0, 0], ![-129, 229, 0], ![-76, 0, 229]], ![![-1, 1, 0], ![56, -100, 1], ![60, -47, -99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![6, 1, 0]] ![![229, 0, 0], ![93, 1, 0]]
  ![![229, 0, 0], ![100, 99, 1]] where
 M := ![![![52441, 0, 0], ![21297, 229, 0]], ![![1374, 229, 0], ![558, 99, 1]]]
 hmul := by decide  
 g := ![![![![129, -99, -1], ![229, 0, 0]], ![![-7, -98, -1], ![229, 0, 0]]], ![![![-94, -98, -1], ![229, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![100, 99, 1]] ![![229, 0, 0], ![-100, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-22900, 229, 0]], ![![22900, 22671, 229], ![-9847, -9847, 0]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-100, 1, 0]]], ![![![100, 99, 1]], ![![-43, -43, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1, I229N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
    exact isPrimeI229N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0 ⊙ MulI229N1)
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


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [150, 140, 141, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 161, 92], [63, 71, 141], [0, 1]]
 g := ![![[20, 101, 110], [208, 52], [232, 171], [5, 182, 167], [18, 181], [107, 105, 76], [1]], ![[178, 185, 230, 36], [137, 31], [226, 71], [175, 96, 58, 116], [198, 142], [226, 171, 192, 202], [147, 158, 78, 2]], ![[160, 96, 73, 200], [52, 50], [18, 19], [94, 138, 129, 38], [146, 178], [64, 154, 214, 72], [190, 166, 160, 231]]]
 h' := ![![[29, 161, 92], [183, 0, 209], [188, 4, 127], [182, 225, 95], [126, 65, 213], [27, 158, 114], [83, 93, 92], [0, 1]], ![[63, 71, 141], [217, 27, 160], [27, 6, 65], [29, 207, 184], [20, 119, 133], [137, 204, 29], [9, 74, 176], [29, 161, 92]], ![[0, 1], [152, 206, 97], [206, 223, 41], [24, 34, 187], [40, 49, 120], [51, 104, 90], [197, 66, 198], [63, 71, 141]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 90], []]
 b := ![[], [97, 190, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [150, 140, 141, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![76191, 4194, -8621]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![327, 18, -37]
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

instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1103, 801, -145]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-1103, 801, -145]] 
 ![![239, 0, 0], ![0, 239, 0], ![62, 67, 1]] where
  M :=![![![-1103, 801, -145], ![-22185, 5712, 656], ![100368, -53017, 6368]]]
  hmulB := by decide  
  f := ![![![-297712, -10823, -5664]], ![![-866592, -31504, -16487]], ![![-330721, -12023, -6292]]]
  g := ![![![33, 44, -145], ![-263, -160, 656], ![-1232, -2007, 6368]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [105, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [226, 238], [0, 1]]
 g := ![![[98, 93], [15, 6], [219, 93], [227, 198], [10], [60, 33], [226, 1]], ![[84, 146], [176, 233], [205, 146], [43, 41], [10], [109, 206], [213, 238]]]
 h' := ![![[226, 238], [98, 103], [188, 217], [65, 136], [132, 26], [153, 38], [170, 64], [0, 1]], ![[0, 1], [193, 136], [235, 22], [209, 103], [33, 213], [137, 201], [55, 175], [226, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [21, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [105, 13, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6086, -1395, 368]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-70, -109, 368]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![297712, 10823, 5664]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![297712, 10823, 5664]] 
 ![![239, 0, 0], ![171, 1, 0], ![156, 0, 1]] where
  M :=![![![297712, 10823, 5664], ![866592, 31504, 16487], ![2522511, 91703, 47991]]]
  hmulB := by decide  
  f := ![![![1103, -801, 145]], ![![882, -597, 101]], ![![300, -301, 68]]]
  g := ![![![-10195, 10823, 5664], ![-29676, 31504, 16487], ![-86382, 91703, 47991]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-1103, 801, -145]] ![![297712, 10823, 5664]]
  ![![239, 0, 0]] where
 M := ![![![-239, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [139, 240, 148, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 28, 62], [92, 212, 179], [0, 1]]
 g := ![![[26, 191, 91], [212, 194], [224, 217], [137, 96], [234, 69, 98], [100, 85, 214], [1]], ![[5, 23, 91, 93], [120, 236], [29, 159], [187, 9], [142, 51, 111, 17], [55, 2, 183, 207], [48, 52, 172, 220]], ![[87, 215, 124, 35], [4, 30], [192, 41], [209, 180], [70, 156, 94, 149], [173, 188, 123, 115], [17, 191, 105, 21]]]
 h' := ![![[1, 28, 62], [139, 19, 36], [98, 37, 215], [77, 179, 159], [9, 101, 108], [78, 135, 87], [102, 1, 93], [0, 1]], ![[92, 212, 179], [8, 161, 134], [163, 32, 156], [196, 140, 221], [142, 28, 238], [212, 132, 63], [77, 134, 16], [1, 28, 62]], ![[0, 1], [173, 61, 71], [27, 172, 111], [98, 163, 102], [62, 112, 136], [202, 215, 91], [64, 106, 132], [92, 212, 179]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 24], []]
 b := ![[], [225, 28, 124], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [139, 240, 148, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-183401, 82663, -6748]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-761, 343, -28]
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


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [118, 58, 185, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [163, 95, 220], [154, 155, 31], [0, 1]]
 g := ![![[5, 150, 94], [160, 114, 190], [174, 214], [50, 109, 189], [135, 247, 41], [52, 226, 89], [1]], ![[100, 211, 221, 133], [33, 27, 70, 150], [37, 115], [135, 18, 101, 24], [83, 163, 51, 50], [112, 126, 36, 150], [220, 127, 172, 78]], ![[60, 48, 202, 227], [197, 86, 140, 154], [223, 131], [155, 143, 168, 39], [83, 108, 8, 91], [245, 203, 156, 85], [161, 66, 208, 173]]]
 h' := ![![[163, 95, 220], [196, 31, 40], [115, 242, 21], [124, 186, 88], [134, 166, 213], [139, 53, 36], [133, 193, 66], [0, 1]], ![[154, 155, 31], [36, 237, 219], [197, 158, 20], [48, 66, 93], [54, 120, 8], [246, 138, 172], [137, 112, 231], [163, 95, 220]], ![[0, 1], [67, 234, 243], [127, 102, 210], [60, 250, 70], [148, 216, 30], [48, 60, 43], [41, 197, 205], [154, 155, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [171, 26], []]
 b := ![[], [61, 53, 98], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [118, 58, 185, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![216613, -6777, -13554]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![863, -27, -54]
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

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0]] 
 ![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [227, 248, 190, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [162, 48, 199], [162, 208, 58], [0, 1]]
 g := ![![[211, 140, 11], [65, 70], [11, 222], [121, 168], [187, 60], [200, 193], [67, 1], []], ![[246, 86, 104, 176], [49, 8], [132, 35], [181, 16], [200, 178], [81, 92], [201, 88], [85, 23]], ![[225, 80, 190, 242], [172, 99], [6, 165], [143, 157], [107, 21], [62, 169], [217, 248], [226, 23]]]
 h' := ![![[162, 48, 199], [84, 238, 36], [31, 31, 228], [230, 77, 42], [55, 216, 164], [149, 240, 211], [211, 119, 129], [0, 0, 1], [0, 1]], ![[162, 208, 58], [193, 194, 109], [137, 183, 137], [17, 189, 158], [193, 15, 253], [19, 198, 156], [219, 209, 141], [10, 45, 208], [162, 48, 199]], ![[0, 1], [72, 82, 112], [56, 43, 149], [90, 248, 57], [13, 26, 97], [245, 76, 147], [21, 186, 244], [128, 212, 48], [162, 208, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 95], []]
 b := ![[], [216, 123, 139], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [227, 248, 190, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-221277, 195320, -39064]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-861, 760, -152]
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



lemma PB271I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB271I4 : PrimesBelowBoundCertificateInterval O 193 257 271 where
  m := 11
  g := ![1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB271I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1]
    · exact ![I211N0]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
    · exact ![I251N0]
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
    · exact ![223, 223, 223]
    · exact ![11697083]
    · exact ![229, 229, 229]
    · exact ![12649337]
    · exact ![57121, 239]
    · exact ![13997521]
    · exact ![15813251]
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
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
      exact NI229N2
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
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
  β := ![I199N1, I223N0, I223N1, I223N2, I229N0, I229N1, I229N2, I239N1]
  Il := ![[], [I199N1], [], [I223N0, I223N1, I223N2], [], [I229N0, I229N1, I229N2], [], [I239N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
