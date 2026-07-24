
import IdealArithmetic.Examples.NF3_1_672300_4.RI3_1_672300_4
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [94, 193, 77, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 9, 175], [45, 187, 22], [0, 1]]
 g := ![![[148, 2, 181], [13, 42], [62, 124, 114], [95, 36], [26, 61], [88, 19], [1]], ![[131, 115, 195, 157], [118, 26], [139, 81, 101, 90], [133, 112], [98, 60], [54, 7], [1, 136, 48, 187]], ![[196, 90, 126, 16], [129, 93], [137, 51, 150, 148], [81, 182], [16, 193], [159, 196], [37, 133, 76, 10]]]
 h' := ![![[75, 9, 175], [183, 84, 56], [82, 154, 47], [147, 151, 36], [58, 124, 6], [170, 178, 109], [103, 4, 120], [0, 1]], ![[45, 187, 22], [111, 128, 153], [163, 85, 82], [143, 111, 61], [148, 120, 167], [62, 56, 116], [4, 13, 91], [75, 9, 175]], ![[0, 1], [27, 182, 185], [50, 155, 68], [134, 132, 100], [38, 150, 24], [153, 160, 169], [179, 180, 183], [45, 187, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [186, 109], []]
 b := ![[], [132, 93, 193], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [94, 193, 77, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-847888, 202713, -79982]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4304, 1029, -406]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [111, 91, 110, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 150, 53], [8, 48, 146], [0, 1]]
 g := ![![[166, 126, 132], [92, 41, 184], [9, 22, 9], [105, 151], [151, 80], [32, 160], [1]], ![[7, 113, 72, 117], [124, 90, 88, 115], [80, 18, 182, 155], [102, 13], [124, 50], [58, 126], [37, 7, 38, 25]], ![[29, 27, 112, 109], [178, 126, 11, 179], [191, 157, 176, 149], [21, 80], [115, 36], [116, 116], [115, 93, 92, 174]]]
 h' := ![![[81, 150, 53], [136, 28, 27], [195, 140, 130], [139, 163, 196], [124, 183, 56], [13, 127, 94], [88, 108, 89], [0, 1]], ![[8, 48, 146], [7, 174, 193], [16, 112, 128], [10, 155, 137], [136, 40, 49], [186, 147, 99], [183, 121, 46], [81, 150, 53]], ![[0, 1], [173, 196, 178], [24, 146, 140], [115, 80, 65], [43, 175, 94], [120, 124, 6], [85, 169, 64], [8, 48, 146]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147, 24], []]
 b := ![[], [172, 58, 161], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [111, 91, 110, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21771197, -1438571, -256909]
  a := ![5, -5, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![109403, -7229, -1291]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-82, 56, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-82, 56, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![129, 56, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-82, 56, 1], ![268, -147, 393], ![8778, -483, -35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-129, -56, 211]], ![![-1, 0, 1], ![-239, -105, 393], ![63, 7, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [98, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [130, 210], [0, 1]]
 g := ![![[158, 180], [14, 46], [59], [189], [159, 148], [176], [130, 1]], ![[137, 31], [86, 165], [59], [189], [198, 63], [176], [49, 210]]]
 h' := ![![[130, 210], [105, 32], [140, 149], [15, 108], [32, 20], [124, 123], [131, 133], [0, 1]], ![[0, 1], [45, 179], [98, 62], [129, 103], [100, 191], [78, 88], [119, 78], [130, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [87, 135]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [98, 81, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1538182, 838679, -347028]
  a := ![-66, 2, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![219454, 96077, -347028]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![29, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![29, 1, 0]] 
 ![![211, 0, 0], ![29, 1, 0], ![35, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![29, 1, 0], ![2, 28, 7], ![156, -9, 30]]]
  hmulB := by decide  
  f := ![![![14005, 201726, 50435], ![2954, -1520255, 0]], ![![1922, 27718, 6930], ![423, -208890, 0]], ![![2304, 33461, 8366], ![629, -252175, 0]]]
  g := ![![![1, 0, 0], ![-29, 211, 0], ![-35, 0, 211]], ![![0, 1, 0], ![-5, 28, 7], ![-3, -9, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-82, 56, 1]] ![![211, 0, 0], ![29, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![6119, 211, 0]], ![![-17302, 11816, 211], ![-2110, 1477, 422]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![29, 1, 0]]], ![![![-82, 56, 1]], ![![-10, 7, 2]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-90, 85, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-90, 85, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![133, 85, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-90, 85, 1], ![326, -184, 596], ![13302, -744, -14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-133, -85, 223]], ![![-1, 0, 1], ![-354, -228, 596], ![68, 2, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [221, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [131, 222], [0, 1]]
 g := ![![[177, 109], [113, 81], [142, 100], [179, 86], [13, 18], [64], [131, 1]], ![[184, 114], [20, 142], [85, 123], [72, 137], [141, 205], [64], [39, 222]]]
 h' := ![![[131, 222], [3, 177], [61, 9], [135, 213], [26, 117], [88, 178], [39, 215], [0, 1]], ![[0, 1], [221, 46], [125, 214], [163, 10], [189, 106], [214, 45], [106, 8], [131, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [46, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [221, 92, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9038, 8412, -4424]
  a := ![-5, 4, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2598, 1724, -4424]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![73, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![73, 1, 0]] 
 ![![223, 0, 0], ![73, 1, 0], ![14, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![73, 1, 0], ![2, 72, 7], ![156, -9, 74]]]
  hmulB := by decide  
  f := ![![![-12732, -534571, -51975], ![-6467, 1655775, 0]], ![![-4203, -174951, -17010], ![-2006, 541890, 0]], ![![-835, -33561, -3263], ![-297, 103950, 0]]]
  g := ![![![1, 0, 0], ![-73, 223, 0], ![-14, 0, 223]], ![![0, 1, 0], ![-24, 72, 7], ![-1, -9, 74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![-90, 85, 1]] ![![223, 0, 0], ![73, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![16279, 223, 0]], ![![-20070, 18955, 223], ![-6244, 6021, 669]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![73, 1, 0]]], ![![![-90, 85, 1]], ![![-28, 27, 3]]]]
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [188, 163, 107, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 181, 83], [56, 45, 144], [0, 1]]
 g := ![![[217, 13, 97], [125, 86, 177], [123, 209], [172, 155], [124, 89], [43, 0, 99], [1]], ![[177, 39, 139, 24], [187, 55, 165, 93], [205, 207], [171, 210], [55, 10], [120, 12, 92, 15], [23, 12, 52, 201]], ![[14, 202, 27, 182], [103, 41, 133, 48], [78, 102], [109, 16], [194, 9], [120, 211, 117, 78], [214, 174, 165, 26]]]
 h' := ![![[64, 181, 83], [108, 14, 209], [163, 138, 152], [70, 73, 182], [95, 54, 90], [88, 187, 166], [39, 64, 120], [0, 1]], ![[56, 45, 144], [9, 147, 125], [120, 88, 134], [98, 95, 175], [127, 144, 133], [222, 195, 64], [175, 106, 43], [64, 181, 83]], ![[0, 1], [71, 66, 120], [195, 1, 168], [176, 59, 97], [187, 29, 4], [148, 72, 224], [92, 57, 64], [56, 45, 144]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107, 23], []]
 b := ![[], [200, 87, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [188, 163, 107, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-785874, 233583, -92162]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3462, 1029, -406]
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


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [44, 101, 171, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [169, 148, 96], [118, 80, 133], [0, 1]]
 g := ![![[43, 149, 178], [189, 15], [115, 0, 173], [29, 220], [91, 56], [49, 196, 158], [1]], ![[135, 181, 227, 127], [130, 42], [139, 26, 102, 114], [207, 154], [101, 173], [138, 152, 41, 189], [71, 214, 42, 109]], ![[132, 180, 225, 188], [8, 56], [34, 85, 224, 198], [134, 76], [117, 153], [33, 125, 14, 59], [172, 125, 19, 120]]]
 h' := ![![[169, 148, 96], [183, 203, 112], [207, 67, 106], [158, 41, 196], [212, 59, 92], [134, 42, 96], [185, 128, 58], [0, 1]], ![[118, 80, 133], [21, 79, 52], [225, 93, 27], [66, 59, 151], [181, 107, 200], [31, 193, 33], [29, 110, 211], [169, 148, 96]], ![[0, 1], [92, 176, 65], [98, 69, 96], [187, 129, 111], [75, 63, 166], [52, 223, 100], [175, 220, 189], [118, 80, 133]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [143, 163], []]
 b := ![[], [185, 12, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [44, 101, 171, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14224793, 1096452, 609140]
  a := ![3, 18, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![62117, 4788, 2660]
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



lemma PB233I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 232 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 232 (by omega)

def PB233I4 : PrimesBelowBoundCertificateInterval O 193 232 233 where
  m := 6
  g := ![1, 1, 2, 2, 1, 1]
  P := ![197, 199, 211, 223, 227, 229]
  hP := PB233I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
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
    · exact ![44521, 211]
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
  β := ![I211N1, I223N1]
  Il := ![[], [], [I211N1], [I223N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
