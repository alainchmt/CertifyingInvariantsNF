
import IdealArithmetic.Examples.NF3_1_977075_1.RI3_1_977075_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![4, -84, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![4, -84, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![4, 113, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![4, -84, 1], ![-332, 77, -83], ![27556, -6391, -6]]]
  hmulB := by decide  
  f := ![![![-3, 84, -1], ![197, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -113, 197]], ![![0, -1, 1], ![0, 48, -83], ![140, -29, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [159, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [157, 196], [0, 1]]
 g := ![![[113, 160], [157], [34, 49], [25], [40], [101], [157, 1]], ![[17, 37], [157], [44, 148], [25], [40], [101], [117, 196]]]
 h' := ![![[157, 196], [139, 95], [110, 123], [139, 190], [78, 192], [79, 146], [56, 62], [0, 1]], ![[0, 1], [82, 102], [115, 74], [25, 7], [81, 5], [149, 51], [137, 135], [157, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [152, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [159, 40, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-837, -153, 37]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, -22, 37]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![83, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![83, 1, 0]] 
 ![![197, 0, 0], ![83, 1, 0], ![6, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![83, 1, 0], ![0, 83, 1], ![-332, 73, 84]]]
  hmulB := by decide  
  f := ![![![1412, 17, 0], ![-3349, 0, 0]], ![![498, 6, 0], ![-1181, 0, 0]], ![![-48, -1, 0], ![114, 1, 0]]]
  g := ![![![1, 0, 0], ![-83, 197, 0], ![-6, 0, 197]], ![![0, 1, 0], ![-35, 83, 1], ![-35, 73, 84]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![4, -84, 1]] ![![197, 0, 0], ![83, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![16351, 197, 0]], ![![788, -16548, 197], ![0, -6895, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![83, 1, 0]]], ![![![4, -84, 1]], ![![0, -35, 0]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-113, -28, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-113, -28, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![86, 171, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-113, -28, 1], ![-332, -40, -27], ![8964, -2303, -67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-86, -171, 199]], ![![-1, -1, 1], ![10, 23, -27], ![74, 46, -67]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [135, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [186, 198], [0, 1]]
 g := ![![[34, 9], [174, 49], [30, 131], [116], [102], [161], [186, 1]], ![[116, 190], [134, 150], [118, 68], [116], [102], [161], [173, 198]]]
 h' := ![![[186, 198], [191, 3], [129, 7], [42, 23], [141, 64], [58, 36], [163, 34], [0, 1]], ![[0, 1], [152, 196], [38, 192], [141, 176], [105, 135], [187, 163], [119, 165], [186, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162]]
 b := ![[], [29, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [135, 13, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1119, -3229, 691]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-293, -610, 691]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![27, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![27, 1, 0]] 
 ![![199, 0, 0], ![27, 1, 0], ![67, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![27, 1, 0], ![0, 27, 1], ![-332, 73, 28]]]
  hmulB := by decide  
  f := ![![![1432, 53, 0], ![-10547, 0, 0]], ![![162, 6, 0], ![-1193, 0, 0]], ![![490, 18, 0], ![-3609, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 199, 0], ![-67, 0, 199]], ![![0, 1, 0], ![-4, 27, 1], ![-21, 73, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-113, -28, 1]] ![![199, 0, 0], ![27, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![5373, 199, 0]], ![![-22487, -5572, 199], ![-3383, -796, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![27, 1, 0]]], ![![![-113, -28, 1]], ![![-17, -4, 0]]]]
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


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [167, 103, 127, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 142, 94], [210, 68, 117], [0, 1]]
 g := ![![[141, 141, 65], [160, 194, 62], [27, 58], [180, 53], [14, 61, 107], [3, 93], [1]], ![[45, 201, 21, 127], [172, 90, 149, 124], [45, 56], [206, 1], [59, 148, 60, 133], [60, 44], [149, 10, 114, 88]], ![[58, 64, 23, 173], [131, 76, 209, 109], [109, 103], [134, 53], [170, 45, 27, 171], [200, 148], [119, 11, 175, 123]]]
 h' := ![![[85, 142, 94], [77, 157, 102], [111, 145, 22], [191, 170, 144], [194, 52, 105], [169, 205, 23], [44, 108, 84], [0, 1]], ![[210, 68, 117], [209, 151, 172], [87, 138, 145], [46, 165, 30], [104, 61, 1], [128, 94, 156], [130, 67, 39], [85, 142, 94]], ![[0, 1], [130, 114, 148], [123, 139, 44], [32, 87, 37], [172, 98, 105], [61, 123, 32], [171, 36, 88], [210, 68, 117]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 18], []]
 b := ![[], [65, 184, 130], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [167, 103, 127, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![95583, 76593, -6541]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![453, 363, -31]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![52, -76, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![52, -76, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![52, 147, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![52, -76, 1], ![-332, 125, -75], ![24900, -5807, 50]]]
  hmulB := by decide  
  f := ![![![-51, 76, -1], ![223, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -147, 223]], ![![0, -1, 1], ![16, 50, -75], ![100, -59, 50]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [53, 213, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 222], [0, 1]]
 g := ![![[105, 101], [117, 110], [114, 72], [65, 196], [42, 63], [202], [10, 1]], ![[0, 122], [102, 113], [165, 151], [18, 27], [3, 160], [202], [20, 222]]]
 h' := ![![[10, 222], [43, 18], [202, 188], [123, 90], [4, 14], [141, 145], [139, 47], [0, 1]], ![[0, 1], [0, 205], [75, 35], [131, 133], [144, 209], [30, 78], [163, 176], [10, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [203, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [53, 213, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-729, -2554, 16]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, -22, 16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![75, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![75, 1, 0]] 
 ![![223, 0, 0], ![75, 1, 0], ![173, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![75, 1, 0], ![0, 75, 1], ![-332, 73, 76]]]
  hmulB := by decide  
  f := ![![![5776, 77, 0], ![-17171, 0, 0]], ![![1950, 26, 0], ![-5797, 0, 0]], ![![4526, 60, 0], ![-13455, 1, 0]]]
  g := ![![![1, 0, 0], ![-75, 223, 0], ![-173, 0, 223]], ![![0, 1, 0], ![-26, 75, 1], ![-85, 73, 76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![52, -76, 1]] ![![223, 0, 0], ![75, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![16725, 223, 0]], ![![11596, -16948, 223], ![3568, -5575, 0]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![75, 1, 0]]], ![![![52, -76, 1]], ![![16, -25, 0]]]]
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [93, 33, 148, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 40, 143], [45, 186, 84], [0, 1]]
 g := ![![[129, 122, 213], [3, 127, 103], [130, 205], [50, 104], [64, 73], [109, 2, 112], [1]], ![[35, 11, 83, 194], [69, 23, 86, 180], [62, 225], [131, 23], [18, 28], [100, 74, 211, 105], [95, 84, 138, 220]], ![[64, 175, 44, 225], [183, 126, 101, 84], [149, 136], [21, 175], [154, 99], [88, 21, 154, 207], [222, 125, 32, 7]]]
 h' := ![![[34, 40, 143], [175, 149, 126], [153, 216, 199], [62, 137, 146], [132, 187, 51], [78, 99, 181], [134, 194, 79], [0, 1]], ![[45, 186, 84], [114, 136, 24], [86, 148, 29], [152, 144, 212], [118, 53, 134], [138, 159, 153], [51, 199, 214], [34, 40, 143]], ![[0, 1], [97, 169, 77], [106, 90, 226], [32, 173, 96], [13, 214, 42], [48, 196, 120], [109, 61, 161], [45, 186, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105, 3], []]
 b := ![[], [60, 8, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [93, 33, 148, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-133703, 6810, 6810]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-589, 30, 30]
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


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [194, 31, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 141, 82], [108, 87, 147], [0, 1]]
 g := ![![[41, 102, 135], [101, 104], [51, 35, 27], [219, 103], [73, 62], [168, 3, 165], [1]], ![[126, 223, 191, 15], [66, 82], [135, 154, 99, 225], [190, 33], [181, 118], [67, 2, 79, 58], [18, 205, 19, 165]], ![[166, 26, 123, 126], [7, 94], [173, 101, 61, 57], [185, 46], [132, 20], [131, 13, 36, 213], [187, 22, 190, 64]]]
 h' := ![![[61, 141, 82], [19, 80, 140], [182, 7, 44], [135, 202, 16], [16, 206, 65], [155, 15, 73], [35, 198, 169], [0, 1]], ![[108, 87, 147], [69, 67, 191], [7, 224, 51], [226, 100, 94], [149, 163, 105], [40, 32, 24], [214, 42, 24], [61, 141, 82]], ![[0, 1], [200, 82, 127], [118, 227, 134], [106, 156, 119], [172, 89, 59], [19, 182, 132], [116, 218, 36], [108, 87, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [180, 184], []]
 b := ![[], [62, 52, 210], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [194, 31, 60, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4791138, 632498, 111294]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20922, 2762, 486]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-67, -3, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-67, -3, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![166, 230, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-67, -3, 1], ![-332, 6, -2], ![664, -478, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-166, -230, 233]], ![![-1, -1, 1], ![0, 2, -2], ![0, -6, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [12, 177, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 232], [0, 1]]
 g := ![![[73, 219], [4], [148], [155, 184], [72], [27, 171], [56, 1]], ![[221, 14], [4], [148], [207, 49], [72], [50, 62], [112, 232]]]
 h' := ![![[56, 232], [50, 174], [104, 2], [4, 71], [194, 157], [142, 189], [27, 95], [0, 1]], ![[0, 1], [8, 59], [216, 231], [19, 162], [132, 76], [8, 44], [221, 138], [56, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150]]
 b := ![[], [230, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [12, 177, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2644, -567, 655]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-478, -649, 655]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![2, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![2, 1, 0]] 
 ![![233, 0, 0], ![2, 1, 0], ![229, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![2, 1, 0], ![0, 2, 1], ![-332, 73, 3]]]
  hmulB := by decide  
  f := ![![![231, 115, 0], ![-26795, 0, 0]], ![![-2, -1, 0], ![234, 0, 0]], ![![227, 113, 0], ![-26331, 1, 0]]]
  g := ![![![1, 0, 0], ![-2, 233, 0], ![-229, 0, 233]], ![![0, 1, 0], ![-1, 2, 1], ![-5, 73, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-67, -3, 1]] ![![233, 0, 0], ![2, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![466, 233, 0]], ![![-15611, -699, 233], ![-466, 0, 0]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![2, 1, 0]]], ![![![-67, -3, 1]], ![![-2, 0, 0]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0]] 
 ![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [145, 77, 188, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 116, 198], [32, 122, 41], [0, 1]]
 g := ![![[18, 227, 220], [150, 53, 110], [121, 0, 155], [153, 31, 176], [128, 66], [64, 39, 211], [1]], ![[233, 164, 77, 3], [233, 210, 83, 183], [87, 53, 76, 142], [24, 212, 59, 169], [134, 49], [200, 126, 233, 218], [72, 7, 157, 150]], ![[211, 223, 92, 95], [62, 20, 147, 111], [78, 188, 230, 131], [87, 125, 207, 206], [204, 80], [167, 106, 42, 39], [90, 211, 58, 89]]]
 h' := ![![[19, 116, 198], [238, 168, 69], [141, 95, 50], [42, 189, 91], [90, 79, 196], [41, 165, 122], [94, 162, 51], [0, 1]], ![[32, 122, 41], [128, 74, 96], [7, 0, 54], [61, 99, 7], [185, 47, 119], [223, 186, 232], [4, 47, 58], [19, 116, 198]], ![[0, 1], [182, 236, 74], [83, 144, 135], [31, 190, 141], [139, 113, 163], [171, 127, 124], [120, 30, 130], [32, 122, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 4], []]
 b := ![[], [166, 97, 140], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [145, 77, 188, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5892067, -1917258, 175426]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24653, -8022, 734]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def PBC239 : ContainsPrimesAboveP 239 ![I239N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![239, 0, 0]]) timesTableT_eq_Table B_one_repr 239 (by decide) 𝕀

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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [38, 142, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 202, 202], [86, 38, 39], [0, 1]]
 g := ![![[194, 113, 24], [105, 80], [177, 48], [171, 1], [114, 38, 9], [15, 71, 3], [1]], ![[178, 164, 74, 186], [115, 9], [43, 193], [139, 80], [143, 208, 98, 184], [57, 135, 52, 66], [89, 13, 62, 208]], ![[107, 66, 59, 207], [143, 151], [79, 122], [201, 221], [204, 201, 205, 171], [175, 98, 147, 176], [15, 136, 195, 33]]]
 h' := ![![[99, 202, 202], [49, 163, 54], [119, 148, 171], [45, 178, 224], [6, 234, 1], [153, 231, 238], [203, 99, 185], [0, 1]], ![[86, 38, 39], [13, 90, 33], [68, 63, 3], [225, 173, 124], [98, 138, 70], [182, 72, 35], [25, 84, 36], [99, 202, 202]], ![[0, 1], [124, 229, 154], [225, 30, 67], [217, 131, 134], [25, 110, 170], [81, 179, 209], [210, 58, 20], [86, 38, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 159], []]
 b := ![[], [209, 189, 208], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [38, 142, 56, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![179545, -94713, 14701]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![745, -393, 61]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![32, 1, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0], ![32, 1, 0]] 
 ![![251, 0, 0], ![32, 1, 0], ![231, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![32, 1, 0], ![0, 32, 1], ![-332, 73, 33]]]
  hmulB := by decide  
  f := ![![![2881, 90, 0], ![-22590, 0, 0]], ![![352, 11, 0], ![-2760, 0, 0]], ![![2693, 84, 0], ![-21116, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 251, 0], ![-231, 0, 251]], ![![0, 1, 0], ![-5, 32, 1], ![-41, 73, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N0 : Nat.card (O ⧸ I251N0) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N0)

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := prime_ideal_of_norm_prime hp251.out _ NI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-23, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-23, 1, 0]] 
 ![![251, 0, 0], ![228, 1, 0], ![224, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-23, 1, 0], ![0, -23, 1], ![-332, 73, -22]]]
  hmulB := by decide  
  f := ![![![3290, -143, 0], ![35893, 0, 0]], ![![3014, -131, 0], ![32882, 0, 0]], ![![2924, -127, 0], ![31900, 1, 0]]]
  g := ![![![1, 0, 0], ![-228, 251, 0], ![-224, 0, 251]], ![![-1, 1, 0], ![20, -23, 1], ![-48, 73, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![-10, 1, 0]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![251, 0, 0], ![-10, 1, 0]] 
 ![![251, 0, 0], ![241, 1, 0], ![151, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![-10, 1, 0], ![0, -10, 1], ![-332, 73, -9]]]
  hmulB := by decide  
  f := ![![![2281, -228, 0], ![57228, 0, 0]], ![![2191, -219, 0], ![54970, 0, 0]], ![![1381, -138, 0], ![34648, 1, 0]]]
  g := ![![![1, 0, 0], ![-241, 251, 0], ![-151, 0, 251]], ![![-1, 1, 0], ![9, -10, 1], ![-66, 73, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![32, 1, 0]] ![![251, 0, 0], ![-23, 1, 0]]
  ![![251, 0, 0], ![17, 9, 1]] where
 M := ![![![63001, 0, 0], ![-5773, 251, 0]], ![![8032, 251, 0], ![-736, 9, 1]]]
 hmul := by decide  
 g := ![![![![234, -9, -1], ![251, 0, 0]], ![![-23, 1, 0], ![0, 0, 0]]], ![![![15, -8, -1], ![251, 0, 0]], ![![-3, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![17, 9, 1]] ![![251, 0, 0], ![-10, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![-2510, 251, 0]], ![![4267, 2259, 251], ![-502, 0, 0]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![-10, 1, 0]]], ![![![17, 9, 1]], ![![-2, 0, 0]]]]
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

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-162, -110, 1]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-162, -110, 1]] 
 ![![257, 0, 0], ![0, 257, 0], ![95, 147, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-162, -110, 1], ![-332, -89, -109], ![36188, -8289, -198]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-95, -147, 257]], ![![-1, -1, 1], ![39, 62, -109], ![214, 81, -198]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [161, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [245, 256], [0, 1]]
 g := ![![[32, 211], [25], [52], [29], [197], [232], [144], [1]], ![[70, 46], [25], [52], [29], [197], [232], [144], [1]]]
 h' := ![![[245, 256], [179, 89], [141, 252], [17, 56], [211, 85], [46, 35], [167, 80], [96, 245], [0, 1]], ![[0, 1], [139, 168], [201, 5], [116, 201], [219, 172], [140, 222], [235, 177], [240, 12], [245, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [220]]
 b := ![[], [146, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [161, 12, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2814, 269, 84]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42, -47, 84]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![109, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![109, 1, 0]] 
 ![![257, 0, 0], ![109, 1, 0], ![198, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![109, 1, 0], ![0, 109, 1], ![-332, 73, 110]]]
  hmulB := by decide  
  f := ![![![8939, 82, 0], ![-21074, 0, 0]], ![![3815, 35, 0], ![-8994, 0, 0]], ![![6914, 63, 0], ![-16300, 1, 0]]]
  g := ![![![1, 0, 0], ![-109, 257, 0], ![-198, 0, 257]], ![![0, 1, 0], ![-47, 109, 1], ![-117, 73, 110]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![-162, -110, 1]] ![![257, 0, 0], ![109, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![28013, 257, 0]], ![![-41634, -28270, 257], ![-17990, -12079, 0]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![109, 1, 0]]], ![![![-162, -110, 1]], ![![-70, -47, 0]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0)


lemma PB280I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB280I4 : PrimesBelowBoundCertificateInterval O 193 257 280 where
  m := 11
  g := ![2, 2, 1, 2, 1, 1, 2, 1, 1, 3, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB280I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1]
    · exact ![I211N0]
    · exact ![I223N0, I223N1]
    · exact ![I227N0]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
    · exact ![I239N0]
    · exact ![I241N0]
    · exact ![I251N0, I251N1, I251N2]
    · exact ![I257N0, I257N1]
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
    · exact ![38809, 197]
    · exact ![39601, 199]
    · exact ![9393931]
    · exact ![49729, 223]
    · exact ![11697083]
    · exact ![12008989]
    · exact ![54289, 233]
    · exact ![13651919]
    · exact ![13997521]
    · exact ![251, 251, 251]
    · exact ![66049, 257]
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
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
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
      exact NI257N1
  β := ![I197N1, I199N1, I223N1, I233N1, I251N0, I251N1, I251N2, I257N1]
  Il := ![[I197N1], [I199N1], [], [I223N1], [], [], [I233N1], [], [], [I251N0, I251N1, I251N2], [I257N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
