
import IdealArithmetic.Examples.NF3_1_933107_3.RI3_1_933107_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![48, -80, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![48, -80, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![48, 117, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![48, -80, 1], ![-137, 97, -639], ![-1842, 2479, -63]]]
  hmulB := by decide  
  f := ![![![-47, 80, -1], ![197, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -117, 197]], ![![0, -1, 1], ![155, 380, -639], ![6, 50, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [86, 167, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 196], [0, 1]]
 g := ![![[160, 109], [23], [43, 51], [168], [196], [85], [30, 1]], ![[81, 88], [23], [194, 146], [168], [196], [85], [60, 196]]]
 h' := ![![[30, 196], [47, 122], [45, 90], [172, 144], [47, 103], [143, 183], [178, 26], [0, 1]], ![[0, 1], [161, 75], [184, 107], [158, 53], [182, 94], [117, 14], [170, 171], [30, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [168, 107]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [86, 167, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1244, 760, -6412]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1556, 3812, -6412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![48, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![48, 1, 0]] 
 ![![197, 0, 0], ![48, 1, 0], ![63, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![48, 1, 0], ![2, 47, 8], ![23, -31, 49]]]
  hmulB := by decide  
  f := ![![![-6755, -172290, -29328], ![-2364, 722202, 0]], ![![-1642, -41968, -7144], ![-590, 175921, 0]], ![![-2169, -55098, -9379], ![-720, 230958, 0]]]
  g := ![![![1, 0, 0], ![-48, 197, 0], ![-63, 0, 197]], ![![0, 1, 0], ![-14, 47, 8], ![-8, -31, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![48, -80, 1]] ![![197, 0, 0], ![48, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![9456, 197, 0]], ![![9456, -15760, 197], ![2167, -3743, -591]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![48, 1, 0]]], ![![![48, -80, 1]], ![![11, -19, -3]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [37, 191, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 54, 94], [116, 144, 105], [0, 1]]
 g := ![![[143, 128, 158], [54, 117, 158], [126, 67, 8], [48, 20], [54, 102], [182, 1], [1]], ![[134, 126, 44, 53], [160, 134, 21, 178], [87, 44, 26, 90], [139, 124], [153, 193], [86, 121], [79, 18, 67, 157]], ![[179, 13, 71, 154], [5, 139, 109, 113], [24, 190, 178, 59], [168, 157], [98, 157], [13, 100], [71, 89, 91, 42]]]
 h' := ![![[82, 54, 94], [191, 144, 77], [114, 16, 77], [166, 88, 40], [56, 139, 152], [8, 31, 163], [162, 8, 198], [0, 1]], ![[116, 144, 105], [84, 18, 147], [58, 71, 55], [63, 37, 102], [119, 136, 129], [3, 47, 118], [1, 127, 11], [82, 54, 94]], ![[0, 1], [70, 37, 174], [70, 112, 67], [65, 74, 57], [50, 123, 117], [166, 121, 117], [99, 64, 189], [116, 144, 105]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [163, 76], []]
 b := ![[], [174, 73, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [37, 191, 1, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1134101, -1287530, 2027810]
  a := ![3, -3, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5699, -6470, 10190]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16, -24, -21]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![16, -24, -21]] 
 ![![211, 0, 0], ![0, 211, 0], ![160, 182, 1]] where
  M :=![![![16, -24, -21], ![-531, 691, -213], ![-510, 765, 643]]]
  hmulB := by decide  
  f := ![![![2878, -3, 93]], ![![2133, -2, 69]], ![![4021, -4, 130]]]
  g := ![![![16, 18, -21], ![159, 187, -213], ![-490, -551, 643]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [70, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [203, 210], [0, 1]]
 g := ![![[187, 208], [148, 143], [161], [199], [15, 126], [36], [203, 1]], ![[0, 3], [59, 68], [161], [199], [62, 85], [36], [195, 210]]]
 h' := ![![[203, 210], [190, 182], [143, 96], [21, 43], [5, 58], [66, 166], [138, 205], [0, 1]], ![[0, 1], [0, 29], [8, 115], [99, 168], [174, 153], [4, 45], [186, 6], [203, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [86, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [70, 8, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-82071, -26387, -1167368]
  a := ![-65, 1, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![884819, 1006799, -1167368]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2878, -3, 93]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![2878, -3, 93]] 
 ![![211, 0, 0], ![20, 1, 0], ![111, 0, 1]] where
  M :=![![![2878, -3, 93], ![2133, -2, 69], ![-255, 0, -8]]]
  hmulB := by decide  
  f := ![![![16, -24, -21]], ![![-1, 1, -3]], ![![6, -9, -8]]]
  g := ![![![-35, -3, 93], ![-26, -2, 69], ![3, 0, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![16, -24, -21]] ![![2878, -3, 93]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0]] 
 ![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [48, 45, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 206, 112], [86, 16, 111], [0, 1]]
 g := ![![[73, 104, 220], [209, 155, 181], [28, 108, 60], [187, 113, 106], [3, 70, 152], [221, 200], [1]], ![[170, 65, 82, 38], [27, 217, 87, 127], [141, 127, 93, 19], [179, 111, 119, 213], [138, 83, 197, 166], [155, 181], [183, 10, 6, 28]], ![[48, 169, 7, 96], [219, 144, 79, 123], [21, 124, 41, 99], [58, 165, 84, 145], [114, 141, 162, 221], [113, 31], [126, 151, 49, 195]]]
 h' := ![![[64, 206, 112], [3, 139, 79], [217, 37, 36], [167, 207, 27], [79, 206, 38], [170, 162, 179], [175, 178, 150], [0, 1]], ![[86, 16, 111], [81, 218, 107], [218, 8, 37], [211, 25, 201], [172, 57, 42], [51, 85, 46], [32, 37, 36], [64, 206, 112]], ![[0, 1], [29, 89, 37], [137, 178, 150], [24, 214, 218], [55, 183, 143], [125, 199, 221], [33, 8, 37], [86, 16, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 75], []]
 b := ![[], [101, 189, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [48, 45, 73, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2204801, 2348413, -5234702]
  a := ![-4, 3, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9887, 10531, -23474]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![10, 1, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![10, 1, 0]] 
 ![![227, 0, 0], ![10, 1, 0], ![216, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![10, 1, 0], ![2, 9, 8], ![23, -31, 11]]]
  hmulB := by decide  
  f := ![![![60559, 273303, 242952], ![4086, -6893763, 0]], ![![2664, 12032, 10696], ![228, -303499, 0]], ![![57632, 260060, 231179], ![3716, -6559704, 0]]]
  g := ![![![1, 0, 0], ![-10, 227, 0], ![-216, 0, 227]], ![![0, 1, 0], ![-8, 9, 8], ![-9, -31, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N0 : Nat.card (O ⧸ I227N0) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N0)

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := prime_ideal_of_norm_prime hp227.out _ NI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![14, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![14, 1, 0]] 
 ![![227, 0, 0], ![14, 1, 0], ![91, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![14, 1, 0], ![2, 13, 8], ![23, -31, 15]]]
  hmulB := by decide  
  f := ![![![13933, 91098, 56064], ![1362, -1590816, 0]], ![![850, 5615, 3456], ![228, -98064, 0]], ![![5579, 36519, 22475], ![651, -637728, 0]]]
  g := ![![![1, 0, 0], ![-14, 227, 0], ![-91, 0, 227]], ![![0, 1, 0], ![-4, 13, 8], ![-4, -31, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-24, 1, 0]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-24, 1, 0]] 
 ![![227, 0, 0], ![203, 1, 0], ![209, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-24, 1, 0], ![2, -25, 8], ![23, -31, -23]]]
  hmulB := by decide  
  f := ![![![38665, -491373, 157248], ![-6129, -4461912, 0]], ![![34579, -439401, 140616], ![-5447, -3989979, 0]], ![![35611, -452410, 144779], ![-5530, -4108104, 0]]]
  g := ![![![1, 0, 0], ![-203, 227, 0], ![-209, 0, 227]], ![![-1, 1, 0], ![15, -25, 8], ![49, -31, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![10, 1, 0]] ![![227, 0, 0], ![14, 1, 0]]
  ![![227, 0, 0], ![-39, 88, 1]] where
 M := ![![![51529, 0, 0], ![3178, 227, 0]], ![![2270, 227, 0], ![142, 23, 8]]]
 hmul := by decide  
 g := ![![![![227, 0, 0], ![0, 0, 0]], ![![14, 1, 0], ![0, 0, 0]]], ![![![10, 1, 0], ![0, 0, 0]], ![![2, -3, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-39, 88, 1]] ![![227, 0, 0], ![-24, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-5448, 227, 0]], ![![-8853, 19976, 227], ![1135, -2270, 681]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-24, 1, 0]]], ![![![-39, 88, 1]], ![![5, -10, 3]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1, I227N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
    exact isPrimeI227N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0 ⊙ MulI227N1)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![64, 1, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![64, 1, 0]] 
 ![![229, 0, 0], ![64, 1, 0], ![126, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![64, 1, 0], ![2, 63, 8], ![23, -31, 65]]]
  hmulB := by decide  
  f := ![![![-19455, -685404, -87040], ![-8244, 2491520, 0]], ![![-5440, -191510, -24320], ![-2289, 696160, 0]], ![![-10714, -377122, -47891], ![-4502, 1370880, 0]]]
  g := ![![![1, 0, 0], ![-64, 229, 0], ![-126, 0, 229]], ![![0, 1, 0], ![-22, 63, 8], ![-27, -31, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N0 : Nat.card (O ⧸ I229N0) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N0)

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := prime_ideal_of_norm_prime hp229.out _ NI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-56, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-56, 1, 0]] 
 ![![229, 0, 0], ![173, 1, 0], ![2, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-56, 1, 0], ![2, -57, 8], ![23, -31, -55]]]
  hmulB := by decide  
  f := ![![![39729, -1237518, 173696], ![-15114, -4972048, 0]], ![![30061, -934865, 131216], ![-11220, -3756058, 0]], ![![402, -10809, 1517], ![93, -43424, 0]]]
  g := ![![![1, 0, 0], ![-173, 229, 0], ![-2, 0, 229]], ![![-1, 1, 0], ![43, -57, 8], ![24, -31, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-8, 1, 0]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-8, 1, 0]] 
 ![![229, 0, 0], ![221, 1, 0], ![163, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-8, 1, 0], ![2, -9, 8], ![23, -31, -7]]]
  hmulB := by decide  
  f := ![![![48533, -218779, 194480], ![-2519, -5566990, 0]], ![![46833, -211129, 187680], ![-2518, -5372340, 0]], ![![34547, -155725, 138429], ![-1745, -3962530, 0]]]
  g := ![![![1, 0, 0], ![-221, 229, 0], ![-163, 0, 229]], ![![-1, 1, 0], ![3, -9, 8], ![35, -31, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![64, 1, 0]] ![![229, 0, 0], ![-56, 1, 0]]
  ![![229, 0, 0], ![-47, -85, 1]] where
 M := ![![![52441, 0, 0], ![-12824, 229, 0]], ![![14656, 229, 0], ![-3582, 7, 8]]]
 hmul := by decide  
 g := ![![![![229, 0, 0], ![0, 0, 0]], ![![-9, 86, -1], ![229, 0, 0]]], ![![![64, 1, 0], ![0, 0, 0]], ![![-14, 3, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-47, -85, 1]] ![![229, 0, 0], ![-8, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-1832, 229, 0]], ![![-10763, -19465, 229], ![229, 687, -687]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-8, 1, 0]]], ![![![-47, -85, 1]], ![![1, 3, -3]]]]
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


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [45, 34, 197, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [221, 41, 11], [48, 191, 222], [0, 1]]
 g := ![![[109, 230, 92], [60, 120], [219, 18], [151, 26, 23], [81, 157], [84, 171, 131], [1]], ![[165, 16, 95, 150], [212, 187], [155, 50], [162, 162, 114, 3], [42, 182], [109, 52, 208, 198], [8, 3, 122, 166]], ![[132, 74, 10, 88], [159, 219], [133, 128], [38, 14, 172, 140], [108, 197], [17, 228, 51, 174], [60, 54, 214, 67]]]
 h' := ![![[221, 41, 11], [159, 70, 201], [210, 90, 54], [195, 68, 211], [224, 106, 16], [181, 95, 200], [188, 199, 36], [0, 1]], ![[48, 191, 222], [22, 151, 17], [230, 167, 120], [139, 176, 41], [115, 230, 28], [181, 210, 101], [9, 63, 211], [221, 41, 11]], ![[0, 1], [101, 12, 15], [75, 209, 59], [148, 222, 214], [31, 130, 189], [124, 161, 165], [13, 204, 219], [48, 191, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [213, 146], []]
 b := ![[], [22, 137, 135], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [45, 34, 197, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-530541, 418002, -2492168]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2277, 1794, -10696]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-13, -77, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-13, -77, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![226, 162, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-13, -77, 1], ![-131, 33, -615], ![-1773, 2386, -121]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-226, -162, 239]], ![![-1, -1, 1], ![581, 417, -615], ![107, 92, -121]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [230, 218, 1] where
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
 g := ![![[82, 49], [222, 186], [103, 88], [37, 102], [160], [144, 67], [21, 1]], ![[155, 190], [65, 53], [39, 151], [28, 137], [160], [117, 172], [42, 238]]]
 h' := ![![[21, 238], [86, 7], [210, 80], [94, 142], [169, 126], [101, 152], [189, 211], [0, 1]], ![[0, 1], [233, 232], [217, 159], [208, 97], [186, 113], [186, 87], [79, 28], [21, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [218, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [230, 218, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13628, -2438, -212011]
  a := ![22, -1, 87]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![200422, 143696, -212011]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-102, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-102, 1, 0]] 
 ![![239, 0, 0], ![137, 1, 0], ![121, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-102, 1, 0], ![2, -103, 8], ![23, -31, -101]]]
  hmulB := by decide  
  f := ![![![16199, -1081041, 83968], ![-11233, -2508544, 0]], ![![9279, -619621, 48128], ![-6452, -1437824, 0]], ![![8173, -547305, 42511], ![-5753, -1270016, 0]]]
  g := ![![![1, 0, 0], ![-137, 239, 0], ![-121, 0, 239]], ![![-1, 1, 0], ![55, -103, 8], ![69, -31, -101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-13, -77, 1]] ![![239, 0, 0], ![-102, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-24378, 239, 0]], ![![-3107, -18403, 239], ![1195, 7887, -717]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-102, 1, 0]]], ![![![-13, -77, 1]], ![![5, 33, -3]]]]
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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [153, 238, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [135, 52, 143], [44, 188, 98], [0, 1]]
 g := ![![[70, 126, 108], [129, 221], [65, 16], [148, 1], [99, 19, 94], [219, 131, 229], [1]], ![[33, 82, 186, 209], [49, 15], [178, 166], [76, 159], [179, 148, 67, 134], [206, 142, 160, 147], [238, 211, 19, 154]], ![[82, 131, 90, 217], [115, 133], [17, 217], [103, 200], [212, 68, 131, 79], [53, 85, 46, 45], [14, 52, 89, 87]]]
 h' := ![![[135, 52, 143], [9, 8, 95], [15, 38, 71], [101, 139, 237], [36, 105, 1], [233, 167, 24], [88, 3, 179], [0, 1]], ![[44, 188, 98], [199, 22, 206], [15, 233, 225], [4, 215, 86], [8, 164, 20], [26, 152, 196], [224, 25, 100], [135, 52, 143]], ![[0, 1], [199, 211, 181], [125, 211, 186], [39, 128, 159], [55, 213, 220], [64, 163, 21], [138, 213, 203], [44, 188, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [218, 204], []]
 b := ![[], [35, 221, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [153, 238, 62, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![964, -964, -964]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, -4, -4]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, 1, -3]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![-10, 1, -3]] 
 ![![251, 0, 0], ![0, 251, 0], ![87, 167, 1]] where
  M :=![![![-10, 1, -3], ![-67, 82, 5], ![29, -28, 84]]]
  hmulB := by decide  
  f := ![![![-28, 0, -1]], ![![-23, 3, -1]], ![![-25, 2, -1]]]
  g := ![![![1, 2, -3], ![-2, -3, 5], ![-29, -56, 84]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [179, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [247, 250], [0, 1]]
 g := ![![[237, 122], [148, 68], [81], [206, 164], [197, 209], [162, 214], [247, 1]], ![[0, 129], [127, 183], [81], [52, 87], [114, 42], [59, 37], [243, 250]]]
 h' := ![![[247, 250], [114, 154], [86, 90], [23, 9], [128, 72], [118, 65], [214, 88], [0, 1]], ![[0, 1], [0, 97], [228, 161], [238, 242], [91, 179], [109, 186], [113, 163], [247, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [142]]
 b := ![[], [142, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [179, 4, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2408, 2048, -12168]
  a := ![5, -2, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4208, 8104, -12168]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28, 0, 1]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![28, 0, 1]] 
 ![![251, 0, 0], ![169, 1, 0], ![28, 0, 1]] where
  M :=![![![28, 0, 1], ![23, -3, 1], ![-2, -1, -3]]]
  hmulB := by decide  
  f := ![![![10, -1, 3]], ![![7, -1, 2]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![2, -3, 1], ![1, -1, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![-10, 1, -3]] ![![28, 0, 1]]
  ![![251, 0, 0]] where
 M := ![![![-251, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0)
instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![33, 1, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![33, 1, 0]] 
 ![![257, 0, 0], ![33, 1, 0], ![61, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![33, 1, 0], ![2, 32, 8], ![23, -31, 34]]]
  hmulB := by decide  
  f := ![![![31769, 520936, 130240], ![6168, -4183960, 0]], ![![4048, 66876, 16720], ![1029, -537130, 0]], ![![7531, 123646, 30913], ![1538, -993080, 0]]]
  g := ![![![1, 0, 0], ![-33, 257, 0], ![-61, 0, 257]], ![![0, 1, 0], ![-6, 32, 8], ![-4, -31, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N0 : Nat.card (O ⧸ I257N0) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N0)

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := prime_ideal_of_norm_prime hp257.out _ NI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![74, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![74, 1, 0]] 
 ![![257, 0, 0], ![74, 1, 0], ![96, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![74, 1, 0], ![2, 73, 8], ![23, -31, 75]]]
  hmulB := by decide  
  f := ![![![-7163, -293886, -32208], ![-3084, 1034682, 0]], ![![-2096, -84604, -9272], ![-770, 297863, 0]], ![![-2718, -109779, -12031], ![-1005, 386496, 0]]]
  g := ![![![1, 0, 0], ![-74, 257, 0], ![-96, 0, 257]], ![![0, 1, 0], ![-24, 73, 8], ![-19, -31, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1

def I257N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-107, 1, 0]] i)))

def SI257N2: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-107, 1, 0]] 
 ![![257, 0, 0], ![150, 1, 0], ![162, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-107, 1, 0], ![2, -108, 8], ![23, -31, -106]]]
  hmulB := by decide  
  f := ![![![-673, 47950, -3552], ![514, 114108, 0]], ![![-303, 27970, -2072], ![515, 66563, 0]], ![![-393, 30225, -2239], ![399, 71928, 0]]]
  g := ![![![1, 0, 0], ![-150, 257, 0], ![-162, 0, 257]], ![![-1, 1, 0], ![58, -108, 8], ![85, -31, -106]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N2 : Nat.card (O ⧸ I257N2) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N2)

lemma isPrimeI257N2 : Ideal.IsPrime I257N2 := prime_ideal_of_norm_prime hp257.out _ NI257N2
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![33, 1, 0]] ![![257, 0, 0], ![74, 1, 0]]
  ![![257, 0, 0], ![-80, -51, 1]] where
 M := ![![![66049, 0, 0], ![19018, 257, 0]], ![![8481, 257, 0], ![2444, 106, 8]]]
 hmul := by decide  
 g := ![![![![257, 0, 0], ![0, 0, 0]], ![![74, 1, 0], ![0, 0, 0]]], ![![![33, 1, 0], ![0, 0, 0]], ![![12, 2, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI257N1 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![-80, -51, 1]] ![![257, 0, 0], ![-107, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![-27499, 257, 0]], ![![-20560, -13107, 257], ![8481, 5397, -514]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![-107, 1, 0]]], ![![![-80, -51, 1]], ![![33, 21, -2]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1, I257N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
    exact isPrimeI257N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0 ⊙ MulI257N1)


lemma PB274I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB274I4 : PrimesBelowBoundCertificateInterval O 193 257 274 where
  m := 11
  g := ![2, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB274I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0, I227N1, I227N2]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
    · exact ![I251N0, I251N1]
    · exact ![I257N0, I257N1, I257N2]
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
    · exact ![7880599]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![227, 227, 227]
    · exact ![229, 229, 229]
    · exact ![12649337]
    · exact ![57121, 239]
    · exact ![13997521]
    · exact ![63001, 251]
    · exact ![257, 257, 257]
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
      exact NI227N1
      exact NI227N2
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
      exact NI251N1
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
      exact NI257N2
  β := ![I197N1, I211N1, I227N0, I227N1, I227N2, I229N0, I229N1, I229N2, I239N1, I251N1, I257N0, I257N1, I257N2]
  Il := ![[I197N1], [], [I211N1], [], [I227N0, I227N1, I227N2], [I229N0, I229N1, I229N2], [], [I239N1], [], [I251N1], [I257N0, I257N1, I257N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
