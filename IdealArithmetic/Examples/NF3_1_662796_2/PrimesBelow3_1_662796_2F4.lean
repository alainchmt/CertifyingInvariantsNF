
import IdealArithmetic.Examples.NF3_1_662796_2.RI3_1_662796_2
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [116, 61, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 135, 142], [49, 61, 55], [0, 1]]
 g := ![![[57, 45, 127], [193, 54], [3, 154, 10], [80, 190], [65, 138], [120, 101], [1]], ![[191, 183, 115, 156], [172, 85], [165, 47, 109, 41], [139, 51], [184, 65], [61, 104], [25, 4, 115, 90]], ![[164, 189, 79, 107], [52, 107], [109, 185, 192, 33], [5, 142], [84, 121], [123, 160], [57, 189, 69, 107]]]
 h' := ![![[86, 135, 142], [19, 116, 18], [46, 41, 60], [113, 189, 124], [118, 94, 105], [127, 41, 170], [81, 136, 135], [0, 1]], ![[49, 61, 55], [6, 128, 37], [88, 188, 26], [131, 31, 124], [135, 33, 53], [20, 71, 38], [195, 173, 164], [86, 135, 142]], ![[0, 1], [145, 150, 142], [142, 165, 111], [154, 174, 146], [145, 70, 39], [32, 85, 186], [126, 85, 95], [49, 61, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [143, 21], []]
 b := ![[], [11, 2, 115], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [116, 61, 62, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2722737, -728900, -128247]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13821, -3700, -651]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![38, -70, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![38, -70, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![38, 129, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![38, -70, 1], ![539, 44, -211], ![-33168, -5189, 185]]]
  hmulB := by decide  
  f := ![![![-37, 70, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -129, 199]], ![![0, -1, 1], ![43, 137, -211], ![-202, -146, 185]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [141, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [136, 198], [0, 1]]
 g := ![![[119, 187], [125, 144], [43, 31], [70], [47], [20], [136, 1]], ![[79, 12], [8, 55], [80, 168], [70], [47], [20], [73, 198]]]
 h' := ![![[136, 198], [86, 171], [106, 187], [74, 35], [118, 104], [175, 131], [127, 47], [0, 1]], ![[0, 1], [59, 28], [66, 12], [58, 164], [133, 95], [81, 68], [151, 152], [136, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [169, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [141, 63, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21671, 8384, 5384]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1137, -3448, 5384]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![12, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![12, 1, 0]] 
 ![![199, 0, 0], ![12, 1, 0], ![14, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![12, 1, 0], ![-1, 13, 3], ![469, 76, 11]]]
  hmulB := by decide  
  f := ![![![-7066, 91714, 21165], ![199, -1403945, 0]], ![![-437, 5524, 1275], ![200, -84575, 0]], ![![-500, 6452, 1489], ![62, -98770, 0]]]
  g := ![![![1, 0, 0], ![-12, 199, 0], ![-14, 0, 199]], ![![0, 1, 0], ![-1, 13, 3], ![-3, 76, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![38, -70, 1]] ![![199, 0, 0], ![12, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![2388, 199, 0]], ![![7562, -13930, 199], ![995, -796, -199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![12, 1, 0]]], ![![![38, -70, 1]], ![![5, -4, -1]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-149, 57, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-149, 57, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![62, 57, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-149, 57, 1], ![412, -16, 170], ![26395, 4463, -129]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-62, -57, 211]], ![![-1, 0, 1], ![-48, -46, 170], ![163, 56, -129]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [172, 205, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 210], [0, 1]]
 g := ![![[130, 119], [103, 188], [25], [34], [201, 87], [139], [6, 1]], ![[0, 92], [176, 23], [25], [34], [90, 124], [139], [12, 210]]]
 h' := ![![[6, 210], [8, 69], [128, 71], [29, 206], [32, 33], [42, 64], [23, 75], [0, 1]], ![[0, 1], [0, 142], [132, 140], [210, 5], [19, 178], [4, 147], [51, 136], [6, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [189]]
 b := ![[], [33, 200]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [172, 205, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2501144, 1230683, 335496]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-86728, -84799, 335496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![41, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![41, 1, 0]] 
 ![![211, 0, 0], ![41, 1, 0], ![129, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![41, 1, 0], ![-1, 42, 3], ![469, 76, 40]]]
  hmulB := by decide  
  f := ![![![6126, -257250, -18375], ![0, 1292375, 0]], ![![1190, -49980, -3570], ![1, 251090, 0]], ![![3748, -157276, -11234], ![-14, 790125, 0]]]
  g := ![![![1, 0, 0], ![-41, 211, 0], ![-129, 0, 211]], ![![0, 1, 0], ![-10, 42, 3], ![-37, 76, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-149, 57, 1]] ![![211, 0, 0], ![41, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![8651, 211, 0]], ![![-31439, 12027, 211], ![-5697, 2321, 211]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![41, 1, 0]]], ![![![-149, 57, 1]], ![![-27, 11, 1]]]]
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


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [169, 62, 100, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 209, 65], [77, 13, 158], [0, 1]]
 g := ![![[133, 114, 58], [46, 76, 153], [215, 86, 29], [96, 163, 109], [140, 85, 58], [67, 188], [1]], ![[15, 82, 112, 15], [142, 168, 115, 16], [157, 95, 113, 101], [75, 174, 60, 148], [180, 211, 142, 136], [207, 38], [122, 53, 8, 112]], ![[102, 145, 204, 160], [94, 77, 211, 52], [107, 27], [198, 187, 194, 185], [61, 149, 53, 137], [214, 63], [22, 83, 28, 111]]]
 h' := ![![[46, 209, 65], [31, 110, 110], [14, 137, 61], [55, 212, 67], [201, 176, 46], [67, 194, 110], [54, 161, 123], [0, 1]], ![[77, 13, 158], [178, 123, 106], [208, 178, 109], [159, 58, 156], [112, 206, 219], [64, 62, 214], [6, 86, 22], [46, 209, 65]], ![[0, 1], [161, 213, 7], [59, 131, 53], [210, 176], [129, 64, 181], [198, 190, 122], [125, 199, 78], [77, 13, 158]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 202], []]
 b := ![[], [140, 77, 165], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [169, 62, 100, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26567105, -10311520, -2331465]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-119135, -46240, -10455]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-107, 1, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-107, 1, 0]] 
 ![![227, 0, 0], ![120, 1, 0], ![78, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-107, 1, 0], ![-1, -106, 3], ![469, 76, -108]]]
  hmulB := by decide  
  f := ![![![5741, 608440, -17220], ![0, 1302980, 0]], ![![3035, 321604, -9102], ![1, 688718, 0]], ![![2025, 209067, -5917], ![111, 447720, 0]]]
  g := ![![![1, 0, 0], ![-120, 227, 0], ![-78, 0, 227]], ![![-1, 1, 0], ![55, -106, 3], ![-1, 76, -108]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N0 : Nat.card (O ⧸ I227N0) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N0)

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := prime_ideal_of_norm_prime hp227.out _ NI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-78, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-78, 1, 0]] 
 ![![227, 0, 0], ![149, 1, 0], ![192, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-78, 1, 0], ![-1, -77, 3], ![469, 76, -79]]]
  hmulB := by decide  
  f := ![![![3553, 273504, -10656], ![0, 806304, 0]], ![![2332, 179487, -6993], ![1, 529137, 0]], ![![3066, 231333, -9013], ![177, 681984, 0]]]
  g := ![![![1, 0, 0], ![-149, 227, 0], ![-192, 0, 227]], ![![-1, 1, 0], ![48, -77, 3], ![19, 76, -79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-42, 1, 0]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-42, 1, 0]] 
 ![![227, 0, 0], ![185, 1, 0], ![31, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-42, 1, 0], ![-1, -41, 3], ![469, 76, -43]]]
  hmulB := by decide  
  f := ![![![3943, 161622, -11826], ![0, 894834, 0]], ![![3213, 131692, -9636], ![1, 729124, 0]], ![![569, 22071, -1615], ![165, 122202, 0]]]
  g := ![![![1, 0, 0], ![-185, 227, 0], ![-31, 0, 227]], ![![-1, 1, 0], ![33, -41, 3], ![-54, 76, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-107, 1, 0]] ![![227, 0, 0], ![-78, 1, 0]]
  ![![227, 0, 0], ![-18, 90, 1]] where
 M := ![![![51529, 0, 0], ![-17706, 227, 0]], ![![-24289, 227, 0], ![8345, -184, 3]]]
 hmul := by decide  
 g := ![![![![227, 0, 0], ![0, 0, 0]], ![![-60, -89, -1], ![227, 0, 0]]], ![![![-89, -89, -1], ![227, 0, 0]], ![![37, -2, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-18, 90, 1]] ![![227, 0, 0], ![-42, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-9534, 227, 0]], ![![-4086, 20430, 227], ![1135, -3632, 227]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-42, 1, 0]]], ![![![-18, 90, 1]], ![![5, -16, 1]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 1, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![11, 1, 0]] 
 ![![229, 0, 0], ![11, 1, 0], ![32, 0, 1]] where
  M :=![![![11, 1, 0], ![-1, 12, 3], ![469, 76, 10]]]
  hmulB := by decide  
  f := ![![![-108, -10, 3]], ![![1, 0, 0]], ![![-40, -3, 1]]]
  g := ![![![0, 1, 0], ![-1, 12, 3], ![-3, 76, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N0 : Nat.card (O ⧸ I229N0) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N0)

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := prime_ideal_of_norm_prime hp229.out _ NI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![74, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![74, 1, 0]] 
 ![![229, 0, 0], ![74, 1, 0], ![58, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![74, 1, 0], ![-1, 75, 3], ![469, 76, 73]]]
  hmulB := by decide  
  f := ![![![-1243, 87749, 3510], ![229, -267930, 0]], ![![-452, 28349, 1134], ![230, -86562, 0]], ![![-362, 22224, 889], ![204, -67860, 0]]]
  g := ![![![1, 0, 0], ![-74, 229, 0], ![-58, 0, 229]], ![![0, 1, 0], ![-25, 75, 3], ![-41, 76, 73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-85, 1, 0]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-85, 1, 0]] 
 ![![229, 0, 0], ![144, 1, 0], ![215, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-85, 1, 0], ![-1, -84, 3], ![469, 76, -86]]]
  hmulB := by decide  
  f := ![![![-21958, -1851697, 66132], ![229, -5048076, 0]], ![![-13775, -1164325, 41583], ![230, -3174169, 0]], ![![-20600, -1738493, 62089], ![257, -4739460, 0]]]
  g := ![![![1, 0, 0], ![-144, 229, 0], ![-215, 0, 229]], ![![-1, 1, 0], ![50, -84, 3], ![35, 76, -86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![11, 1, 0]] ![![229, 0, 0], ![74, 1, 0]]
  ![![229, 0, 0], ![42, 105, 1]] where
 M := ![![![2519, 229, 0], ![813, 86, 3]]]
 hmul := by decide  
 g := ![![![![-31, -104, -1], ![229, 0, 0]], ![![3, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![42, 105, 1]] ![![229, 0, 0], ![-85, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-19465, 229, 0]], ![![9618, 24045, 229], ![-3206, -8702, 229]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-85, 1, 0]]], ![![![42, 105, 1]], ![![-14, -38, 1]]]]
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


lemma PB231I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 230 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 230 (by omega)

def PB231I4 : PrimesBelowBoundCertificateInterval O 193 230 231 where
  m := 6
  g := ![1, 2, 2, 1, 3, 3]
  P := ![197, 199, 211, 223, 227, 229]
  hP := PB231I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0, I227N1, I227N2]
    · exact ![I229N0, I229N1, I229N2]
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
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![227, 227, 227]
    · exact ![229, 229, 229]
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
  β := ![I199N1, I211N1, I227N0, I227N1, I227N2, I229N0, I229N1, I229N2]
  Il := ![[], [I199N1], [I211N1], [], [I227N0, I227N1, I227N2], [I229N0, I229N1, I229N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
