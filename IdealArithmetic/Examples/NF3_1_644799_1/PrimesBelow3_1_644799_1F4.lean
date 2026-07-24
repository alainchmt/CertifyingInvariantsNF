
import IdealArithmetic.Examples.NF3_1_644799_1.RI3_1_644799_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![15, -40, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![15, -40, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![15, 157, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![15, -40, 1], ![-36, 96, -357], ![6153, -57, -102]]]
  hmulB := by decide  
  f := ![![![-14, 40, -1], ![197, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -157, 197]], ![![0, -1, 1], ![27, 285, -357], ![39, 81, -102]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [183, 112, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 196], [0, 1]]
 g := ![![[189, 112], [49], [139, 26], [61], [109], [136], [85, 1]], ![[56, 85], [49], [182, 171], [61], [109], [136], [170, 196]]]
 h' := ![![[85, 196], [80, 167], [173, 190], [15, 82], [151, 109], [195, 122], [8, 147], [0, 1]], ![[0, 1], [91, 30], [169, 7], [90, 115], [157, 88], [124, 75], [92, 50], [85, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [14, 148]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [183, 112, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4794, -3567, -1344]
  a := ![5, 3, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![78, 1053, -1344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-37, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-37, 1, 0]] 
 ![![197, 0, 0], ![160, 1, 0], ![102, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-37, 1, 0], ![-3, -39, 9], ![-156, 1, -34]]]
  hmulB := by decide  
  f := ![![![40924, 543567, -125433], ![-4728, 2745589, 0]], ![![33218, 441461, -101871], ![-3939, 2229843, 0]], ![![21181, 281441, -64945], ![-2491, 1421574, 0]]]
  g := ![![![1, 0, 0], ![-160, 197, 0], ![-102, 0, 197]], ![![-1, 1, 0], ![27, -39, 9], ![16, 1, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![15, -40, 1]] ![![197, 0, 0], ![-37, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-7289, 197, 0]], ![![2955, -7880, 197], ![-591, 1576, -394]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-37, 1, 0]]], ![![![15, -40, 1]], ![![-3, 8, -2]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [198, 101, 162, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 23, 138], [194, 175, 61], [0, 1]]
 g := ![![[42, 50, 117], [193, 133, 158], [26, 72, 8], [45, 124], [97, 196], [195, 175], [1]], ![[76, 182, 122, 48], [185, 149, 43, 15], [159, 19, 147, 37], [126, 81], [99, 112], [37, 50], [176, 159, 139, 78]], ![[70, 166, 69, 196], [52, 75, 154, 20], [69, 146, 165, 4], [166, 139], [105, 102], [194, 188], [130, 84, 41, 121]]]
 h' := ![![[42, 23, 138], [193, 22, 52], [26, 96, 77], [137, 162, 159], [106, 77, 70], [196, 178, 14], [1, 98, 37], [0, 1]], ![[194, 175, 61], [46, 139, 196], [42, 107, 57], [111, 13, 33], [69, 60, 190], [13, 130, 149], [37, 22, 99], [42, 23, 138]], ![[0, 1], [148, 38, 150], [90, 195, 65], [73, 24, 7], [107, 62, 138], [20, 90, 36], [5, 79, 63], [194, 175, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 37], []]
 b := ![[], [26, 17, 105], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [198, 101, 162, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7372950, -678988, 34228]
  a := ![-5, -4, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![37050, -3412, 172]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-98, -16, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-98, -16, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![113, 195, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-98, -16, 1], ![-108, -65, -141], ![2409, -33, -143]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-113, -195, 211]], ![![-1, -1, 1], ![75, 130, -141], ![88, 132, -143]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [146, 210, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 210], [0, 1]]
 g := ![![[13, 139], [70, 209], [62], [125], [116, 5], [136], [1, 1]], ![[152, 72], [68, 2], [62], [125], [121, 206], [136], [2, 210]]]
 h' := ![![[1, 210], [119, 136], [197, 118], [78, 22], [155, 97], [194, 65], [65, 66], [0, 1]], ![[0, 1], [44, 75], [104, 93], [100, 189], [41, 114], [48, 146], [131, 145], [1, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [38, 135]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [146, 210, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-369285, -76237, -1130]
  a := ![1, 1, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1145, 683, -1130]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-70, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-70, 1, 0]] 
 ![![211, 0, 0], ![141, 1, 0], ![143, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-70, 1, 0], ![-3, -72, 9], ![-156, 1, -67]]]
  hmulB := by decide  
  f := ![![![604, 14472, -1809], ![0, 42411, 0]], ![![403, 9648, -1206], ![1, 28274, 0]], ![![412, 9808, -1226], ![8, 28743, 0]]]
  g := ![![![1, 0, 0], ![-141, 211, 0], ![-143, 0, 211]], ![![-1, 1, 0], ![42, -72, 9], ![44, 1, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-98, -16, 1]] ![![211, 0, 0], ![-70, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-14770, 211, 0]], ![![-20678, -3376, 211], ![6752, 1055, -211]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-70, 1, 0]]], ![![![-98, -16, 1]], ![![32, 5, -1]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-77, 92, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-77, 92, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![146, 92, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-77, 92, 1], ![-432, -260, 831], ![-14439, 75, 202]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-146, -92, 223]], ![![-1, 0, 1], ![-546, -344, 831], ![-197, -83, 202]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [218, 176, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 222], [0, 1]]
 g := ![![[54, 89], [130, 89], [15, 98], [201, 74], [2, 28], [33], [47, 1]], ![[0, 134], [76, 134], [161, 125], [111, 149], [203, 195], [33], [94, 222]]]
 h' := ![![[47, 222], [204, 138], [75, 138], [113, 105], [10, 48], [86, 52], [12, 207], [0, 1]], ![[0, 1], [0, 85], [94, 85], [142, 118], [36, 175], [77, 171], [152, 16], [47, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [176, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [218, 176, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2176, -6100, -2975]
  a := ![7, 5, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1938, 1200, -2975]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![61, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![61, 1, 0]] 
 ![![223, 0, 0], ![61, 1, 0], ![21, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![61, 1, 0], ![-3, 59, 9], ![-156, 1, 64]]]
  hmulB := by decide  
  f := ![![![10333, -214002, -32643], ![2007, 808821, 0]], ![![2793, -58531, -8928], ![670, 221216, 0]], ![![952, -20153, -3074], ![266, 76167, 0]]]
  g := ![![![1, 0, 0], ![-61, 223, 0], ![-21, 0, 223]], ![![0, 1, 0], ![-17, 59, 9], ![-7, 1, 64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![-77, 92, 1]] ![![223, 0, 0], ![61, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![13603, 223, 0]], ![![-17171, 20516, 223], ![-5129, 5352, 892]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![61, 1, 0]]], ![![![-77, 92, 1]], ![![-23, 24, 4]]]]
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [180, 25, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [188, 59, 222], [224, 167, 5], [0, 1]]
 g := ![![[4, 213, 134], [167, 90, 175], [107, 57], [38, 71], [24, 16], [103, 198, 175], [1]], ![[76, 98, 133, 49], [63, 189, 68, 29], [111, 3], [121, 122], [145, 36], [70, 19, 161, 121], [14, 175, 141, 102]], ![[74, 84, 165, 61], [168, 183, 147, 179], [170, 10], [111, 181], [226, 100], [107, 47, 144, 111], [7, 21, 11, 125]]]
 h' := ![![[188, 59, 222], [131, 139, 208], [68, 121, 42], [184, 223, 113], [21, 89, 170], [74, 87, 4], [47, 202, 185], [0, 1]], ![[224, 167, 5], [4, 57, 218], [98, 64, 53], [97, 159, 50], [174, 114, 24], [214, 157, 6], [132, 152, 148], [188, 59, 222]], ![[0, 1], [217, 31, 28], [206, 42, 132], [36, 72, 64], [128, 24, 33], [185, 210, 217], [75, 100, 121], [224, 167, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [163, 206], []]
 b := ![[], [48, 207, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [180, 25, 42, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9076595, -31326, 156630]
  a := ![5, 3, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39985, -138, 690]
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



lemma PB228I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 227 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 227 (by omega)

def PB228I4 : PrimesBelowBoundCertificateInterval O 193 227 228 where
  m := 5
  g := ![2, 1, 2, 2, 1]
  P := ![197, 199, 211, 223, 227]
  hP := PB228I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0]
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
    · exact ![44521, 211]
    · exact ![49729, 223]
    · exact ![11697083]
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
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
  β := ![I197N1, I211N1, I223N1]
  Il := ![[I197N1], [], [I211N1], [I223N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
