
import IdealArithmetic.Examples.NF3_1_760455_3.RI3_1_760455_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-39, 95, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-39, 95, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![158, 95, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-39, 95, 1], ![227, -164, 666], ![3517, -2849, 26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-158, -95, 197]], ![![-1, 0, 1], ![-533, -322, 666], ![-3, -27, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [36, 190, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 196], [0, 1]]
 g := ![![[60, 104], [178], [50, 169], [157], [136], [169], [7, 1]], ![[0, 93], [178], [51, 28], [157], [136], [169], [14, 196]]]
 h' := ![![[7, 196], [34, 164], [170, 93], [161, 13], [10, 123], [93, 147], [142, 13], [0, 1]], ![[0, 1], [0, 33], [33, 104], [55, 184], [83, 74], [137, 50], [36, 184], [7, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [2, 112]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [36, 190, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-242, 49, -2772]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2222, 1337, -2772]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-75, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-75, 1, 0]] 
 ![![197, 0, 0], ![122, 1, 0], ![171, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-75, 1, 0], ![2, -76, 7], ![37, -30, -74]]]
  hmulB := by decide  
  f := ![![![-6488, 306411, -28224], ![4137, 794304, 0]], ![![-4016, 189683, -17472], ![2562, 491712, 0]], ![![-5634, 265971, -24499], ![3585, 689472, 0]]]
  g := ![![![1, 0, 0], ![-122, 197, 0], ![-171, 0, 197]], ![![-1, 1, 0], ![41, -76, 7], ![83, -30, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-39, 95, 1]] ![![197, 0, 0], ![-75, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-14775, 197, 0]], ![![-7683, 18715, 197], ![3152, -7289, 591]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-75, 1, 0]]], ![![![-39, 95, 1]], ![![16, -37, 3]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [176, 123, 70, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [124, 28, 105], [5, 170, 94], [0, 1]]
 g := ![![[40, 106, 140], [22, 164, 100], [181, 176, 43], [166, 81], [85, 102], [182, 124], [1]], ![[151, 7, 75, 3], [135, 169, 122, 74], [191, 66, 72, 170], [71, 61], [75, 52], [143, 18], [82, 188, 198, 42]], ![[134, 27, 63, 45], [135, 20, 174, 33], [59, 14, 92, 116], [110, 80], [106, 46], [168, 100], [63, 165, 159, 157]]]
 h' := ![![[124, 28, 105], [108, 128, 90], [183, 0, 189], [107, 19, 21], [104, 118, 190], [138, 81, 36], [23, 76, 129], [0, 1]], ![[5, 170, 94], [166, 158, 84], [127, 49, 91], [113, 51, 192], [79, 184, 114], [155, 22, 98], [100, 83, 60], [124, 28, 105]], ![[0, 1], [10, 112, 25], [66, 150, 118], [189, 129, 185], [131, 96, 94], [9, 96, 65], [181, 40, 10], [5, 170, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 25], []]
 b := ![[], [92, 117, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [176, 123, 70, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4683465, -4173030, 4285465]
  a := ![5, -5, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![23535, -20970, 21535]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![845, -716, 349]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![845, -716, 349]] 
 ![![211, 0, 0], ![0, 211, 0], ![26, 163, 1]] where
  M :=![![![845, -716, 349], ![11481, -8909, -4663], ![-25794, 21829, -10341]]]
  hmulB := by decide  
  f := ![![![-919036, -1015, -30559]], ![![-1132713, -1251, -37664]], ![![-988748, -1092, -32877]]]
  g := ![![![-39, -273, 349], ![629, 3560, -4663], ![1152, 8092, -10341]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [119, 191, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 210], [0, 1]]
 g := ![![[147, 172], [163, 54], [64], [49], [51, 5], [47], [20, 1]], ![[0, 39], [188, 157], [64], [49], [151, 206], [47], [40, 210]]]
 h' := ![![[20, 210], [15, 52], [106, 138], [45, 203], [50, 7], [209, 65], [152, 70], [0, 1]], ![[0, 1], [0, 159], [123, 73], [96, 8], [190, 204], [32, 146], [75, 141], [20, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [133, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [119, 191, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41627, 63595, -1200539]
  a := ![-66, 2, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![148131, 927732, -1200539]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-919036, -1015, -30559]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![-919036, -1015, -30559]] 
 ![![211, 0, 0], ![124, 1, 0], ![52, 0, 1]] where
  M :=![![![-919036, -1015, -30559], ![-1132713, -1251, -37664], ![-98673, -109, -3281]]]
  hmulB := by decide  
  f := ![![![845, -716, 349]], ![![551, -463, 183]], ![![86, -73, 37]]]
  g := ![![![3772, -1015, -30559], ![4649, -1251, -37664], ![405, -109, -3281]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![845, -716, 349]] ![![-919036, -1015, -30559]]
  ![![211, 0, 0]] where
 M := ![![![211, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![555665027, 613687, 18476499]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![555665027, 613687, 18476499]] 
 ![![223, 0, 0], ![0, 223, 0], ![209, 82, 1]] where
  M :=![![![555665027, 613687, 18476499], ![684857837, 756370, 22772308], ![59659417, 65889, 1983744]]]
  hmulB := by decide  
  f := ![![![-684, 621, -758]], ![![-26804, 21435, 3589]], ![![-10401, 8377, 711]]]
  g := ![![![-14824768, -6791297, 18476499], ![-18271545, -8370282, 22772308], ![-1591673, -729153, 1983744]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [203, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [123, 222], [0, 1]]
 g := ![![[218, 78], [101, 30], [9, 38], [113, 152], [127, 181], [2], [123, 1]], ![[0, 145], [0, 193], [0, 185], [77, 71], [90, 42], [2], [23, 222]]]
 h' := ![![[123, 222], [13, 154], [180, 91], [30, 201], [87, 179], [89, 36], [7, 208], [0, 1]], ![[0, 1], [0, 69], [0, 132], [0, 22], [27, 44], [57, 187], [169, 15], [123, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [213]]
 b := ![[], [196, 218]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [203, 100, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4920, 4988, -11372]
  a := ![-5, 4, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10636, 4204, -11372]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-684, 621, -758]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-684, 621, -758]] 
 ![![223, 0, 0], ![94, 1, 0], ![185, 0, 1]] where
  M :=![![![-684, 621, -758], ![-26804, 21435, 3589], ![21461, -19388, 22677]]]
  hmulB := by decide  
  f := ![![![555665027, 613687, 18476499]], ![![237297625, 262076, 7890418]], ![![461245244, 509408, 15336933]]]
  g := ![![![364, 621, -758], ![-12133, 21435, 3589], ![-10544, -19388, 22677]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![555665027, 613687, 18476499]] ![![-684, 621, -758]]
  ![![223, 0, 0]] where
 M := ![![![223, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [103, 63, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [213, 27, 111], [201, 199, 116], [0, 1]]
 g := ![![[150, 12, 76], [14, 50, 144], [100, 9], [18, 77], [188, 175], [36, 60, 11], [1]], ![[70, 118, 98, 218], [149, 60, 189, 115], [59, 48], [36, 70], [175, 77], [129, 195, 181, 54], [169, 143, 53, 183]], ![[119, 90, 103, 221], [36, 224, 79, 182], [208, 219], [128, 121], [114, 176], [222, 104, 181, 189], [25, 156, 212, 44]]]
 h' := ![![[213, 27, 111], [147, 199, 59], [97, 193, 215], [78, 1, 3], [32, 92, 118], [151, 118, 42], [124, 164, 187], [0, 1]], ![[201, 199, 116], [28, 175, 7], [196, 170, 194], [215, 209, 27], [219, 33, 98], [159, 59, 118], [52, 34, 29], [213, 27, 111]], ![[0, 1], [49, 80, 161], [14, 91, 45], [10, 17, 197], [74, 102, 11], [127, 50, 67], [52, 29, 11], [201, 199, 116]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106, 37], []]
 b := ![[], [115, 71, 151], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [103, 63, 40, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11350, 22246, -359114]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50, 98, -1582]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4061881493, 4486019, 135062215]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![4061881493, 4486019, 135062215]] 
 ![![229, 0, 0], ![0, 229, 0], ![159, 44, 1]] where
  M :=![![![4061881493, 4486019, 135062215], ![5006273993, 5529024, 166464348], ![436107133, 481645, 14501062]]]
  hmulB := by decide  
  f := ![![![-4668, 3893, -1212]], ![![-37058, 27799, 26039]], ![![-9743, 7529, 4317]]]
  g := ![![![-76039348, -25931229, 135062215], ![-93718591, -31960272, 166464348], ![-8164025, -2784127, 14501062]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [109, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [129, 228], [0, 1]]
 g := ![![[190, 174], [224], [181, 33], [53], [146], [53, 104], [129, 1]], ![[194, 55], [224], [87, 196], [53], [146], [187, 125], [29, 228]]]
 h' := ![![[129, 228], [167, 113], [194, 192], [94, 105], [72, 125], [177, 72], [137, 44], [0, 1]], ![[0, 1], [88, 116], [1, 37], [128, 124], [167, 104], [76, 157], [88, 185], [129, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [163, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [109, 100, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14586, -9116, 688]
  a := ![3, 18, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-414, -172, 688]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4668, -3893, 1212]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![4668, -3893, 1212]] 
 ![![229, 0, 0], ![149, 1, 0], ![56, 0, 1]] where
  M :=![![![4668, -3893, 1212], ![37058, -27799, -26039], ![-141617, 118002, -35585]]]
  hmulB := by decide  
  f := ![![![-4061881493, -4486019, -135062215]], ![![-2664745050, -2942995, -88605827]], ![![-995202929, -1099121, -33091638]]]
  g := ![![![2257, -3893, 1212], ![24617, -27799, -26039], ![-68695, 118002, -35585]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![4061881493, 4486019, 135062215]] ![![4668, -3893, 1212]]
  ![![229, 0, 0]] where
 M := ![![![-229, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![87, 36, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![87, 36, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![87, 36, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![87, 36, 1], ![109, 21, 253], ![1334, -1079, 93]]]
  hmulB := by decide  
  f := ![![![-86, -36, -1], ![233, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-87, -36, 233]], ![![0, 0, 1], ![-94, -39, 253], ![-29, -19, 93]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [4, 187, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 232], [0, 1]]
 g := ![![[105, 175], [7], [1], [102, 66], [1], [170, 225], [46, 1]], ![[0, 58], [7], [1], [109, 167], [1], [35, 8], [92, 232]]]
 h' := ![![[46, 232], [23, 116], [98, 163], [58, 232], [124, 84], [19, 1], [49, 15], [0, 1]], ![[0, 1], [0, 117], [140, 70], [12, 1], [27, 149], [65, 232], [40, 218], [46, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [154]]
 b := ![[], [93, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [4, 187, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3276, 3208, -4778]
  a := ![-3, 4, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1770, 752, -4778]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-20, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-20, 1, 0]] 
 ![![233, 0, 0], ![213, 1, 0], ![140, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-20, 1, 0], ![2, -21, 7], ![37, -30, -19]]]
  hmulB := by decide  
  f := ![![![83805, -889765, 296604], ![-10951, -9872676, 0]], ![![76609, -813371, 271138], ![-10018, -9025022, 0]], ![![50360, -534623, 178217], ![-6521, -5932080, 0]]]
  g := ![![![1, 0, 0], ![-213, 233, 0], ![-140, 0, 233]], ![![-1, 1, 0], ![15, -21, 7], ![39, -30, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![87, 36, 1]] ![![233, 0, 0], ![-20, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-4660, 233, 0]], ![![20271, 8388, 233], ![-1631, -699, 233]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-20, 1, 0]]], ![![![87, 36, 1]], ![![-7, -3, 1]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-99, -59, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-99, -59, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![140, 180, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-99, -59, 1], ![-81, -70, -412], ![-2181, 1771, -188]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-140, -180, 239]], ![![-1, -1, 1], ![241, 310, -412], ![101, 149, -188]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [10, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [193, 238], [0, 1]]
 g := ![![[148, 24], [180, 33], [70, 201], [95, 142], [187], [7, 113], [193, 1]], ![[0, 215], [96, 206], [145, 38], [16, 97], [187], [67, 126], [147, 238]]]
 h' := ![![[193, 238], [112, 44], [17, 64], [6, 139], [162, 182], [169, 67], [221, 194], [0, 1]], ![[0, 1], [0, 195], [180, 175], [65, 100], [155, 57], [194, 172], [140, 45], [193, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [204]]
 b := ![[], [195, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [10, 46, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-432, 981, -5145]
  a := ![4, -1, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3012, 3879, -5145]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-66, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-66, 1, 0]] 
 ![![239, 0, 0], ![173, 1, 0], ![188, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-66, 1, 0], ![2, -67, 7], ![37, -30, -65]]]
  hmulB := by decide  
  f := ![![![8317, -309526, 32340], ![-3346, -1104180, 0]], ![![6029, -224038, 23408], ![-2389, -799216, 0]], ![![6508, -243476, 25439], ![-2756, -868560, 0]]]
  g := ![![![1, 0, 0], ![-173, 239, 0], ![-188, 0, 239]], ![![-1, 1, 0], ![43, -67, 7], ![73, -30, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-99, -59, 1]] ![![239, 0, 0], ![-66, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-15774, 239, 0]], ![![-23661, -14101, 239], ![6453, 3824, -478]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-66, 1, 0]]], ![![![-99, -59, 1]], ![![27, 16, -2]]]]
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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [193, 100, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 106, 89], [121, 134, 152], [0, 1]]
 g := ![![[36, 232, 194], [26, 233], [82, 18], [188, 32], [197, 193, 145], [178, 182, 216], [1]], ![[236, 149, 115, 138], [218, 133], [74, 123], [71, 150], [147, 71, 102, 171], [162, 24, 205, 93], [121, 176, 85, 44]], ![[48, 97, 127, 51], [23, 200], [222, 5], [196, 83], [203, 229, 144, 139], [207, 32, 141, 11], [25, 70, 11, 197]]]
 h' := ![![[41, 106, 89], [102, 86, 26], [163, 107, 76], [223, 215, 175], [57, 240, 88], [109, 229, 77], [48, 141, 162], [0, 1]], ![[121, 134, 152], [229, 151, 52], [176, 23, 186], [203, 91, 169], [228, 195, 135], [164, 106, 92], [19, 224, 35], [41, 106, 89]], ![[0, 1], [104, 4, 163], [143, 111, 220], [36, 176, 138], [168, 47, 18], [65, 147, 72], [206, 117, 44], [121, 134, 152]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 158], []]
 b := ![[], [149, 169, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [193, 100, 79, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![107968, 216900, -3470400]
  a := ![-5, 0, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![448, 900, -14400]
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



lemma PB247I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 246 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 246 (by omega)

def PB247I4 : PrimesBelowBoundCertificateInterval O 193 246 247 where
  m := 9
  g := ![2, 1, 2, 2, 1, 2, 2, 2, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241]
  hP := PB247I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0]
    · exact ![I229N0, I229N1]
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
    · exact ![44521, 211]
    · exact ![49729, 223]
    · exact ![11697083]
    · exact ![52441, 229]
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
      exact NI211N1
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
  β := ![I197N1, I211N1, I223N1, I229N1, I233N1, I239N1]
  Il := ![[I197N1], [], [I211N1], [I223N1], [], [I229N1], [I233N1], [I239N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
