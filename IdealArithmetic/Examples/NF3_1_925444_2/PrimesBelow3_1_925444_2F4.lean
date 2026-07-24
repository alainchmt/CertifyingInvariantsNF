
import IdealArithmetic.Examples.NF3_1_925444_2.RI3_1_925444_2
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [34, 184, 125, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 21, 77], [184, 175, 120], [0, 1]]
 g := ![![[96, 122, 100], [125, 105], [176, 129, 148], [33, 172], [122, 105], [32, 62], [1]], ![[88, 25, 96, 195], [162, 188], [103, 8, 63, 78], [12, 33], [87, 181], [143, 64], [160, 33, 153, 84]], ![[79, 85, 114, 73], [103, 191], [15, 47, 41, 69], [186, 15], [170, 150], [196, 96], [93, 81, 184, 113]]]
 h' := ![![[85, 21, 77], [44, 178, 10], [123, 176, 41], [86, 111, 99], [82, 113, 70], [68, 182, 156], [163, 13, 72], [0, 1]], ![[184, 175, 120], [47, 50, 90], [165, 80, 42], [8, 19, 65], [131, 0, 69], [118, 149, 141], [152, 78, 8], [85, 21, 77]], ![[0, 1], [144, 166, 97], [10, 138, 114], [123, 67, 33], [145, 84, 58], [58, 63, 97], [157, 106, 117], [184, 175, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123, 77], []]
 b := ![[], [120, 173, 196], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [34, 184, 125, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1816340, -329384, -65010]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9220, -1672, -330]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-61, -38, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-61, -38, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![138, 161, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-61, -38, 1], ![308, -105, -191], ![-8968, -1176, 10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-138, -161, 199]], ![![-1, -1, 1], ![134, 154, -191], ![-52, -14, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [29, 160, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 198], [0, 1]]
 g := ![![[81, 151], [158, 98], [196, 46], [122], [62], [50], [39, 1]], ![[0, 48], [0, 101], [0, 153], [122], [62], [50], [78, 198]]]
 h' := ![![[39, 198], [194, 143], [87, 59], [52, 65], [40, 108], [131, 96], [63, 99], [0, 1]], ![[0, 1], [0, 56], [0, 140], [0, 134], [73, 91], [94, 103], [143, 100], [39, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [53, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [29, 160, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11506, 7604, 6524]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4582, -5240, 6524]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-8, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-8, 1, 0]] 
 ![![199, 0, 0], ![191, 1, 0], ![189, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-8, 1, 0], ![-2, -6, 5], ![232, 32, -9]]]
  hmulB := by decide  
  f := ![![![11129, 33409, -27840], ![-199, 1108032, 0]], ![![10681, 32065, -26720], ![-198, 1063456, 0]], ![![10571, 31730, -26441], ![-158, 1052352, 0]]]
  g := ![![![1, 0, 0], ![-191, 199, 0], ![-189, 0, 199]], ![![-1, 1, 0], ![1, -6, 5], ![-21, 32, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-61, -38, 1]] ![![199, 0, 0], ![-8, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-1592, 199, 0]], ![![-12139, -7562, 199], ![796, 199, -199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-8, 1, 0]]], ![![![-61, -38, 1]], ![![4, 1, -1]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![60, 89, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![60, 89, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![60, 89, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![60, 89, 1], ![54, 270, 444], ![20496, 2888, 4]]]
  hmulB := by decide  
  f := ![![![-59, -89, -1], ![211, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -89, 211]], ![![0, 0, 1], ![-126, -186, 444], ![96, 12, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [135, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [108, 210], [0, 1]]
 g := ![![[168, 25], [], [126], [193], [0, 24], [79], [108, 1]], ![[125, 186], [], [126], [193], [60, 187], [79], [5, 210]]]
 h' := ![![[108, 210], [0, 5], [146], [109, 166], [0, 68], [115, 119], [190, 135], [0, 1]], ![[0, 1], [118, 206], [146], [102, 45], [170, 143], [96, 92], [0, 76], [108, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [161]]
 b := ![[], [84, 186]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [135, 103, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5870671, 3181759, 1266781]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-332399, -519250, 1266781]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-22, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-22, 1, 0]] 
 ![![211, 0, 0], ![189, 1, 0], ![207, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-22, 1, 0], ![-2, -20, 5], ![232, 32, -23]]]
  hmulB := by decide  
  f := ![![![61915, 622676, -155665], ![-3376, 6569063, 0]], ![![55465, 557734, -139430], ![-2953, 5883946, 0]], ![![60735, 610872, -152714], ![-3372, 6444531, 0]]]
  g := ![![![1, 0, 0], ![-189, 211, 0], ![-207, 0, 211]], ![![-1, 1, 0], ![13, -20, 5], ![-5, 32, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![60, 89, 1]] ![![211, 0, 0], ![-22, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-4642, 211, 0]], ![![12660, 18779, 211], ![-1266, -1688, 422]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-22, 1, 0]]], ![![![60, 89, 1]], ![![-6, -8, 2]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![0, -107, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![0, -107, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![0, 116, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![0, -107, 1], ![446, -182, -536], ![-24976, -3384, 140]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -116, 223]], ![![0, -1, 1], ![2, 278, -536], ![-112, -88, 140]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [111, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [191, 222], [0, 1]]
 g := ![![[159, 18], [165, 17], [9, 178], [182, 63], [194, 119], [218], [191, 1]], ![[29, 205], [67, 206], [111, 45], [173, 160], [177, 104], [218], [159, 222]]]
 h' := ![![[191, 222], [194, 45], [116, 54], [91, 160], [97, 78], [142, 157], [207, 21], [0, 1]], ![[0, 1], [92, 178], [172, 169], [100, 63], [54, 145], [24, 66], [204, 202], [191, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [203]]
 b := ![[], [63, 213]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [111, 32, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4906, 7956, 4221]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22, -2160, 4221]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![90, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![90, 1, 0]] 
 ![![223, 0, 0], ![90, 1, 0], ![83, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![90, 1, 0], ![-2, 92, 5], ![232, 32, 89]]]
  hmulB := by decide  
  f := ![![![-12551, 618802, 33630], ![-2230, -1499898, 0]], ![![-5068, 249692, 13570], ![-891, -605222, 0]], ![![-4711, 230316, 12517], ![-732, -558258, 0]]]
  g := ![![![1, 0, 0], ![-90, 223, 0], ![-83, 0, 223]], ![![0, 1, 0], ![-39, 92, 5], ![-45, 32, 89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![0, -107, 1]] ![![223, 0, 0], ![90, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![20070, 223, 0]], ![![0, -23861, 223], ![446, -9812, -446]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![90, 1, 0]]], ![![![0, -107, 1]], ![![2, -44, -2]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-18, 44, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-18, 44, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![209, 44, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-18, 44, 1], ![144, 102, 219], ![10056, 1448, -29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-209, -44, 227]], ![![-1, 0, 1], ![-201, -42, 219], ![71, 12, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [54, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [188, 226], [0, 1]]
 g := ![![[89, 190], [39, 195], [205], [171], [161], [27, 129], [188, 1]], ![[170, 37], [152, 32], [205], [171], [161], [217, 98], [149, 226]]]
 h' := ![![[188, 226], [164, 72], [186, 167], [157, 146], [68, 202], [131, 36], [63, 105], [0, 1]], ![[0, 1], [80, 155], [29, 60], [138, 81], [135, 25], [89, 191], [54, 122], [188, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [156, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [54, 39, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3278, 1849, 625]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-561, -113, 625]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![8, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![8, 1, 0]] 
 ![![227, 0, 0], ![8, 1, 0], ![29, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![8, 1, 0], ![-2, 10, 5], ![232, 32, 7]]]
  hmulB := by decide  
  f := ![![![47121, -235723, -117860], ![681, 5350844, 0]], ![![1652, -8301, -4150], ![228, 188410, 0]], ![![6015, -30115, -15057], ![225, 683588, 0]]]
  g := ![![![1, 0, 0], ![-8, 227, 0], ![-29, 0, 227]], ![![0, 1, 0], ![-1, 10, 5], ![-1, 32, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-18, 44, 1]] ![![227, 0, 0], ![8, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![1816, 227, 0]], ![![-4086, 9988, 227], ![0, 454, 227]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![8, 1, 0]]], ![![![-18, 44, 1]], ![![0, 2, 1]]]]
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


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [74, 133, 153, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [114, 38, 200], [191, 190, 29], [0, 1]]
 g := ![![[147, 96, 58], [24, 169], [128, 81, 11], [219, 154], [217, 25], [143, 148, 51], [1]], ![[213, 170, 119, 189], [67, 60], [53, 58, 69, 38], [99, 19], [17, 224], [171, 67, 63, 2], [152, 5, 114, 114]], ![[80, 36, 28, 88], [70, 213], [208, 154, 195, 69], [158, 168], [20, 161], [225, 168, 24, 166], [226, 53, 111, 115]]]
 h' := ![![[114, 38, 200], [75, 7, 150], [146, 53, 13], [20, 1, 195], [215, 123, 200], [181, 8, 224], [155, 96, 76], [0, 1]], ![[191, 190, 29], [29, 127, 130], [112, 144, 17], [136, 155, 152], [135, 214, 83], [83, 72, 192], [116, 167, 206], [114, 38, 200]], ![[0, 1], [5, 95, 178], [39, 32, 199], [191, 73, 111], [77, 121, 175], [130, 149, 42], [81, 195, 176], [191, 190, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140, 34], []]
 b := ![[], [108, 113, 167], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [74, 133, 153, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![56687805, 13198644, 3927579]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![247545, 57636, 17151]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0]] 
 ![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [1, 65, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [198, 59, 17], [222, 173, 216], [0, 1]]
 g := ![![[35, 192, 32], [187, 107], [18, 178], [77, 222, 181], [62, 81], [41, 213, 19], [1]], ![[51, 12, 29, 22], [151, 91], [125, 81], [68, 157, 220, 54], [110, 171], [115, 27, 199, 6], [141, 204, 138, 20]], ![[97, 117, 166, 189], [192, 117], [196, 37], [178, 156, 89, 193], [29, 173], [116, 219, 45, 160], [217, 18, 160, 213]]]
 h' := ![![[198, 59, 17], [219, 219, 107], [86, 185, 56], [156, 43, 90], [221, 201, 114], [192, 152, 224], [232, 168, 187], [0, 1]], ![[222, 173, 216], [83, 118, 99], [232, 114, 18], [130, 32, 224], [232, 65, 72], [153, 15, 95], [89, 86, 24], [198, 59, 17]], ![[0, 1], [73, 129, 27], [126, 167, 159], [97, 158, 152], [212, 200, 47], [63, 66, 147], [83, 212, 22], [222, 173, 216]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [222, 113], []]
 b := ![[], [226, 111, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [1, 65, 46, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3962165, -1357924, -382586]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17005, -5828, -1642]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-44, 100, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-44, 100, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![195, 100, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-44, 100, 1], ![32, 188, 499], ![23048, 3240, -111]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-195, -100, 239]], ![![-1, 0, 1], ![-407, -208, 499], ![187, 60, -111]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [228, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [218, 238], [0, 1]]
 g := ![![[85, 16], [112, 153], [93, 187], [19, 121], [187], [206, 198], [218, 1]], ![[227, 223], [6, 86], [229, 52], [107, 118], [187], [111, 41], [197, 238]]]
 h' := ![![[218, 238], [37, 235], [67, 48], [209, 172], [225, 11], [115, 67], [8, 213], [0, 1]], ![[0, 1], [121, 4], [15, 191], [182, 67], [233, 228], [142, 172], [76, 26], [218, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136]]
 b := ![[], [236, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [228, 21, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8110, 7315, 3455]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2785, -1415, 3455]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-21, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-21, 1, 0]] 
 ![![239, 0, 0], ![218, 1, 0], ![111, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-21, 1, 0], ![-2, -19, 5], ![232, 32, -22]]]
  hmulB := by decide  
  f := ![![![-3982, -38039, 10010], ![239, -478478, 0]], ![![-3630, -34695, 9130], ![240, -436414, 0]], ![![-1842, -17667, 4649], ![195, -222222, 0]]]
  g := ![![![1, 0, 0], ![-218, 239, 0], ![-111, 0, 239]], ![![-1, 1, 0], ![15, -19, 5], ![-18, 32, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-44, 100, 1]] ![![239, 0, 0], ![-21, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-5019, 239, 0]], ![![-10516, 23900, 239], ![956, -1912, 478]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-21, 1, 0]]], ![![![-44, 100, 1]], ![![4, -8, 2]]]]
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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [225, 240, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 158, 101], [156, 82, 140], [0, 1]]
 g := ![![[20, 199, 223], [15, 30], [160, 212], [145, 121], [180, 68, 87], [8, 13, 36], [1]], ![[190, 126, 38, 92], [183, 232], [84, 120], [20, 16], [223, 117, 166, 178], [63, 37, 212, 111], [9, 166, 176, 26]], ![[7, 219, 86, 115], [172, 54], [51, 187], [207, 225], [221, 25, 216, 208], [221, 219, 22, 23], [15, 183, 69, 215]]]
 h' := ![![[79, 158, 101], [150, 234, 114], [174, 180, 111], [54, 183, 104], [229, 59, 230], [128, 231, 91], [16, 1, 235], [0, 1]], ![[156, 82, 140], [41, 240, 206], [138, 171, 49], [177, 148, 19], [154, 106, 237], [111, 61, 186], [97, 214, 91], [79, 158, 101]], ![[0, 1], [54, 8, 162], [215, 131, 81], [134, 151, 118], [14, 76, 15], [48, 190, 205], [183, 26, 156], [156, 82, 140]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113, 155], []]
 b := ![[], [29, 24, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [225, 240, 6, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-64612100, -16375950, -4729625]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-268100, -67950, -19625]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![69, -57, 1]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0], ![69, -57, 1]] 
 ![![251, 0, 0], ![0, 251, 0], ![69, 194, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![69, -57, 1], ![346, -13, -286], ![-13376, -1784, 159]]]
  hmulB := by decide  
  f := ![![![-68, 57, -1], ![251, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-69, -194, 251]], ![![0, -1, 1], ![80, 221, -286], ![-97, -130, 159]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [93, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [169, 250], [0, 1]]
 g := ![![[206, 27], [220, 119], [115], [49, 66], [2, 181], [132, 232], [169, 1]], ![[0, 224], [0, 132], [115], [159, 185], [220, 70], [184, 19], [87, 250]]]
 h' := ![![[169, 250], [122, 228], [113, 133], [212, 93], [65, 98], [23, 159], [96, 105], [0, 1]], ![[0, 1], [0, 23], [0, 118], [116, 158], [61, 153], [37, 92], [20, 146], [169, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101]]
 b := ![[], [188, 176]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [93, 82, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54131, 8060, 9652]
  a := ![-6, -2, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2869, -7428, 9652]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![35, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![35, 1, 0]] 
 ![![251, 0, 0], ![35, 1, 0], ![92, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![35, 1, 0], ![-2, 37, 5], ![232, 32, 34]]]
  hmulB := by decide  
  f := ![![![16882, -315541, -42640], ![1255, 2140528, 0]], ![![2343, -43994, -5945], ![252, 298439, 0]], ![![6169, -115657, -15629], ![595, 784576, 0]]]
  g := ![![![1, 0, 0], ![-35, 251, 0], ![-92, 0, 251]], ![![0, 1, 0], ![-7, 37, 5], ![-16, 32, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![69, -57, 1]] ![![251, 0, 0], ![35, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![8785, 251, 0]], ![![17319, -14307, 251], ![2761, -2008, -251]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![35, 1, 0]]], ![![![69, -57, 1]], ![![11, -8, -1]]]]
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

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0]] 
 ![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [19, 193, 242, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 246, 146], [1, 10, 111], [0, 1]]
 g := ![![[121, 141, 81], [84, 8], [243, 162], [170, 32], [], [26, 253], [15, 1], []], ![[254, 63, 128, 241], [113, 189], [153, 232], [12, 67], [167, 2], [119, 60], [235, 100], [161, 242]], ![[85, 77, 85, 13], [142, 241], [244, 185], [202, 197], [248, 2], [43, 196], [38, 121], [196, 242]]]
 h' := ![![[14, 246, 146], [8, 231, 248], [24, 244, 120], [234, 210, 26], [61, 6, 17], [33, 187], [229, 170, 32], [0, 0, 1], [0, 1]], ![[1, 10, 111], [225, 20, 226], [148, 6, 73], [182, 29, 80], [47, 208, 18], [81, 256, 60], [172, 218, 211], [221, 1, 10], [14, 246, 146]], ![[0, 1], [79, 6, 40], [174, 7, 64], [21, 18, 151], [255, 43, 222], [220, 71, 197], [254, 126, 14], [132, 256, 246], [1, 10, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 243], []]
 b := ![[], [232, 254, 155], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [19, 193, 242, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1595914745, 434726808, 130744124]
  a := ![-15, 27, 44]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6209785, 1691544, 508732]
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



lemma PB273I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB273I4 : PrimesBelowBoundCertificateInterval O 193 257 273 where
  m := 11
  g := ![1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB273I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
    · exact ![I229N0]
    · exact ![I233N0]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
    · exact ![I251N0, I251N1]
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
    · exact ![44521, 211]
    · exact ![49729, 223]
    · exact ![51529, 227]
    · exact ![12008989]
    · exact ![12649337]
    · exact ![57121, 239]
    · exact ![13997521]
    · exact ![63001, 251]
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
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
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
  β := ![I199N1, I211N1, I223N1, I227N1, I239N1, I251N1]
  Il := ![[], [I199N1], [I211N1], [I223N1], [I227N1], [], [], [I239N1], [], [I251N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
