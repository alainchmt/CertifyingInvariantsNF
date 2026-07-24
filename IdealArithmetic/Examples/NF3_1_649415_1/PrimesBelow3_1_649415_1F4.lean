
import IdealArithmetic.Examples.NF3_1_649415_1.RI3_1_649415_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![54, 7, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![54, 7, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![54, 7, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![54, 7, 1], ![171, 55, 36], ![1165, 89, 69]]]
  hmulB := by decide  
  f := ![![![-53, -7, -1], ![197, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -7, 197]], ![![0, 0, 1], ![-9, -1, 36], ![-13, -2, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [192, 133, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 196], [0, 1]]
 g := ![![[131, 24], [43], [153, 93], [40], [59], [114], [64, 1]], ![[91, 173], [43], [195, 104], [40], [59], [114], [128, 196]]]
 h' := ![![[64, 196], [153, 157], [174, 35], [66, 68], [76, 51], [136, 16], [123, 161], [0, 1]], ![[0, 1], [154, 40], [50, 162], [84, 129], [188, 146], [175, 181], [183, 36], [64, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [72, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [192, 133, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1580, 825, -445]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![130, 20, -445]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-36, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-36, 1, 0]] 
 ![![197, 0, 0], ![161, 1, 0], ![128, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-36, 1, 0], ![2, -37, 5], ![157, 8, -35]]]
  hmulB := by decide  
  f := ![![![9391, -182360, 24645], ![-2561, -971013, 0]], ![![7697, -149026, 20140], ![-1969, -793516, 0]], ![![6112, -118488, 16013], ![-1608, -630912, 0]]]
  g := ![![![1, 0, 0], ![-161, 197, 0], ![-128, 0, 197]], ![![-1, 1, 0], ![27, -37, 5], ![17, 8, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![54, 7, 1]] ![![197, 0, 0], ![-36, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-7092, 197, 0]], ![![10638, 1379, 197], ![-1773, -197, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-36, 1, 0]]], ![![![54, 7, 1]], ![![-9, -1, 0]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [86, 154, 175, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 41, 155], [128, 157, 44], [0, 1]]
 g := ![![[66, 73, 158], [76, 69, 140], [154, 161, 20], [42, 92], [76, 32], [64, 178], [1]], ![[81, 39, 131, 28], [80, 121, 43, 89], [160, 8, 54, 180], [37, 18], [134, 103], [6, 9], [91, 27, 35, 187]], ![[151, 43, 110, 21], [175, 34, 68, 54], [160, 10, 61, 99], [2, 126], [103, 35], [14, 43], [64, 183, 127, 12]]]
 h' := ![![[95, 41, 155], [31, 34, 77], [89, 141, 109], [93, 58, 47], [83, 63, 106], [101, 130, 80], [113, 45, 24], [0, 1]], ![[128, 157, 44], [169, 81, 46], [121, 131, 163], [113, 44, 51], [67, 194, 139], [7, 159, 74], [18, 35, 196], [95, 41, 155]], ![[0, 1], [52, 84, 76], [17, 126, 126], [131, 97, 101], [169, 141, 153], [79, 109, 45], [158, 119, 178], [128, 157, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 10], []]
 b := ![[], [187, 141, 154], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [86, 154, 175, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7518419, 1909206, 241188]
  a := ![5, -5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![37781, 9594, 1212]
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


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [61, 27, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [137, 33, 176], [69, 177, 35], [0, 1]]
 g := ![![[188, 47, 62], [187, 11, 196], [194, 169], [94, 16], [103, 135, 134], [145, 25], [1]], ![[146, 29, 160, 122], [45, 207, 82, 183], [5, 101], [69, 53], [90, 131, 86, 83], [32, 13], [86, 169, 160, 169]], ![[33, 163, 35, 156], [137, 66, 176, 85], [71, 99], [74, 65], [210, 3, 21, 166], [52, 71], [155, 114, 174, 42]]]
 h' := ![![[137, 33, 176], [198, 128, 22], [28, 153, 197], [62, 113, 13], [47, 180, 4], [151, 175, 150], [150, 184, 206], [0, 1]], ![[69, 177, 35], [43, 101, 47], [79, 0, 185], [54, 113, 34], [26, 88, 105], [86, 68, 169], [136, 94, 60], [137, 33, 176]], ![[0, 1], [130, 193, 142], [40, 58, 40], [183, 196, 164], [107, 154, 102], [55, 179, 103], [22, 144, 156], [69, 177, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 16], []]
 b := ![[], [97, 186, 115], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [61, 27, 5, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13500636660, -1343961757, -394050940]
  a := ![-66, 2, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-63984060, -6369487, -1867540]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-57, -80, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-57, -80, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![166, 143, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-57, -80, 1], ![-3, 31, -399], ![-12494, -607, -129]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-166, -143, 223]], ![![-1, -1, 1], ![297, 256, -399], ![40, 80, -129]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [115, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [147, 222], [0, 1]]
 g := ![![[181, 64], [110, 66], [45, 128], [168, 74], [4, 212], [37], [147, 1]], ![[0, 159], [0, 157], [129, 95], [119, 149], [171, 11], [37], [71, 222]]]
 h' := ![![[147, 222], [61, 215], [177, 17], [81, 103], [209, 48], [47, 124], [43, 86], [0, 1]], ![[0, 1], [0, 8], [0, 206], [58, 120], [129, 175], [212, 99], [197, 137], [147, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124]]
 b := ![[], [126, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [115, 76, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5382, 4993, 470]
  a := ![-5, 4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-374, -279, 470]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-47, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-47, 1, 0]] 
 ![![223, 0, 0], ![176, 1, 0], ![129, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-47, 1, 0], ![2, -48, 5], ![157, 8, -46]]]
  hmulB := by decide  
  f := ![![![59560, -1527465, 159120], ![-19401, -7096752, 0]], ![![47037, -1205500, 125580], ![-15163, -5600868, 0]], ![![34462, -883601, 92047], ![-11185, -4105296, 0]]]
  g := ![![![1, 0, 0], ![-176, 223, 0], ![-129, 0, 223]], ![![-1, 1, 0], ![35, -48, 5], ![21, 8, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![-57, -80, 1]] ![![223, 0, 0], ![-47, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![-10481, 223, 0]], ![![-12711, -17840, 223], ![2676, 3791, -446]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![-47, 1, 0]]], ![![![-57, -80, 1]], ![![12, 17, -2]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![39, 90, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![39, 90, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![39, 90, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![39, 90, 1], ![337, -43, 451], ![14196, 753, 137]]]
  hmulB := by decide  
  f := ![![![-38, -90, -1], ![227, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -90, 227]], ![![0, 0, 1], ![-76, -179, 451], ![39, -51, 137]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [112, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [147, 226], [0, 1]]
 g := ![![[98, 75], [211, 136], [177], [102], [89], [66, 84], [147, 1]], ![[0, 152], [0, 91], [177], [102], [89], [156, 143], [67, 226]]]
 h' := ![![[147, 226], [203, 204], [38, 131], [121, 75], [60, 97], [99, 166], [107, 159], [0, 1]], ![[0, 1], [0, 23], [0, 96], [23, 152], [18, 130], [212, 61], [99, 68], [147, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [180, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [112, 80, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1606, 825, -180]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38, 75, -180]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![3, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![3, 1, 0]] 
 ![![227, 0, 0], ![3, 1, 0], ![90, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![3, 1, 0], ![2, 2, 5], ![157, 8, 4]]]
  hmulB := by decide  
  f := ![![![-8511, -8512, -21280], ![0, 966112, 0]], ![![-112, -112, -280], ![1, 12712, 0]], ![![-3375, -3375, -8437], ![45, 383040, 0]]]
  g := ![![![1, 0, 0], ![-3, 227, 0], ![-90, 0, 227]], ![![0, 1, 0], ![-2, 2, 5], ![-1, 8, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![39, 90, 1]] ![![227, 0, 0], ![3, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![681, 227, 0]], ![![8853, 20430, 227], ![454, 227, 454]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![3, 1, 0]]], ![![![39, 90, 1]], ![![2, 1, 2]]]]
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


lemma PB229I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 228 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 228 (by omega)

def PB229I4 : PrimesBelowBoundCertificateInterval O 193 228 229 where
  m := 5
  g := ![2, 1, 1, 2, 2]
  P := ![197, 199, 211, 223, 227]
  hP := PB229I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![7880599]
    · exact ![9393931]
    · exact ![49729, 223]
    · exact ![51529, 227]
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
      exact NI223N1
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
  β := ![I197N1, I223N1, I227N1]
  Il := ![[I197N1], [], [], [I223N1], [I227N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
