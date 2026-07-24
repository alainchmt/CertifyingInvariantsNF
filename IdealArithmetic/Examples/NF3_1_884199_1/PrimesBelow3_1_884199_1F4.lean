
import IdealArithmetic.Examples.NF3_1_884199_1.RI3_1_884199_1
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [185, 69, 188, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [102, 60, 108], [104, 136, 89], [0, 1]]
 g := ![![[107, 18, 133], [3, 22], [150, 110, 34], [53, 47], [101, 23], [78, 81], [1]], ![[174, 170, 24, 149], [136, 105], [65, 83, 177, 38], [42, 164], [14, 19], [99, 63], [34, 75, 149, 94]], ![[32, 180, 66, 35], [11, 23], [124, 51, 67, 195], [140, 24], [96, 169], [100, 133], [90, 121, 122, 103]]]
 h' := ![![[102, 60, 108], [174, 22, 112], [27, 3, 66], [94, 67, 25], [190, 112, 176], [95, 41, 90], [12, 128, 9], [0, 1]], ![[104, 136, 89], [28, 99, 75], [184, 55, 41], [87, 161, 195], [119, 17, 178], [98, 33, 120], [180, 168, 76], [102, 60, 108]], ![[0, 1], [44, 76, 10], [75, 139, 90], [67, 166, 174], [102, 68, 40], [59, 123, 184], [89, 98, 112], [104, 136, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170, 125], []]
 b := ![[], [161, 48, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [185, 69, 188, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5800468, -1378606, -191878]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29444, -6998, -974]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [174, 83, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 104, 23], [94, 94, 176], [0, 1]]
 g := ![![[91, 18, 178], [168, 112, 125], [41, 103, 32], [181, 140], [172, 16], [76, 162], [1]], ![[135, 136, 83, 125], [143, 113, 70, 130], [38, 16, 71, 58], [43, 16], [90, 23], [125, 33], [126, 174, 142, 28]], ![[119, 157, 165, 181], [57, 140, 113, 129], [142, 105, 101, 129], [136, 80], [126, 65], [114, 111], [85, 131, 62, 171]]]
 h' := ![![[86, 104, 23], [21, 104, 24], [30, 47, 181], [173, 43, 80], [184, 39, 90], [137, 159, 4], [25, 116, 180], [0, 1]], ![[94, 94, 176], [125, 121, 71], [155, 24, 185], [9, 65, 151], [39, 118, 4], [66, 127, 53], [18, 9, 86], [86, 104, 23]], ![[0, 1], [34, 173, 104], [79, 128, 32], [195, 91, 167], [24, 42, 105], [156, 112, 142], [93, 74, 132], [94, 94, 176]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167, 128], []]
 b := ![[], [155, 56, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [174, 83, 19, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5097385, 1891694, 457501]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25615, 9506, 2299]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-34, 3, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-34, 3, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![177, 3, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-34, 3, 1], ![327, 27, 9], ![872, 283, 24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-177, -3, 211]], ![![-1, 0, 1], ![-6, 0, 9], ![-16, 1, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [66, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [202, 210], [0, 1]]
 g := ![![[144, 16], [57, 56], [37], [4], [179, 56], [14], [202, 1]], ![[0, 195], [186, 155], [37], [4], [97, 155], [14], [193, 210]]]
 h' := ![![[202, 210], [36, 4], [170, 181], [162, 167], [2, 209], [175, 181], [172, 15], [0, 1]], ![[0, 1], [0, 207], [18, 30], [136, 44], [20, 2], [23, 30], [37, 196], [202, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [173, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [66, 9, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3477, 109, 177]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-132, -2, 177]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-9, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-9, 1, 0]] 
 ![![211, 0, 0], ![202, 1, 0], ![187, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-9, 1, 0], ![0, -8, 3], ![327, 58, -9]]]
  hmulB := by decide  
  f := ![![![496, -55, 0], ![11605, 0, 0]], ![![478, -53, 0], ![11184, 0, 0]], ![![454, -45, -2], ![10623, 141, 0]]]
  g := ![![![1, 0, 0], ![-202, 211, 0], ![-187, 0, 211]], ![![-1, 1, 0], ![5, -8, 3], ![-46, 58, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-34, 3, 1]] ![![211, 0, 0], ![-9, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-1899, 211, 0]], ![![-7174, 633, 211], ![633, 0, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-9, 1, 0]]], ![![![-34, 3, 1]], ![![3, 0, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-37, -15, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-37, -15, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![186, 208, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-37, -15, 1], ![327, 6, -45], ![-5014, -761, 21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-186, -208, 223]], ![![-1, -1, 1], ![39, 42, -45], ![-40, -23, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [39, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [137, 222], [0, 1]]
 g := ![![[128, 183], [137, 109], [63, 197], [6, 218], [159, 119], [4], [137, 1]], ![[0, 40], [129, 114], [69, 26], [213, 5], [183, 104], [4], [51, 222]]]
 h' := ![![[137, 222], [9, 39], [219, 177], [212, 190], [43, 21], [148, 66], [9, 221], [0, 1]], ![[0, 1], [0, 184], [161, 46], [151, 33], [21, 202], [47, 157], [181, 2], [137, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [175, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [39, 86, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3941, 6793, 2238]
  a := ![1, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1849, -2057, 2238]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![45, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![45, 1, 0]] 
 ![![223, 0, 0], ![45, 1, 0], ![202, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![45, 1, 0], ![0, 46, 3], ![327, 58, 45]]]
  hmulB := by decide  
  f := ![![![3601, 80, 0], ![-17840, 0, 0]], ![![675, 15, 0], ![-3344, 0, 0]], ![![3274, 42, -2], ![-16220, 149, 0]]]
  g := ![![![1, 0, 0], ![-45, 223, 0], ![-202, 0, 223]], ![![0, 1, 0], ![-12, 46, 3], ![-51, 58, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![-37, -15, 1]] ![![223, 0, 0], ![45, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![10035, 223, 0]], ![![-8251, -3345, 223], ![-1338, -669, 0]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![45, 1, 0]]], ![![![-37, -15, 1]], ![![-6, -3, 0]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![2, -59, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![2, -59, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![2, 168, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![2, -59, 1], ![327, 1, -177], ![-19402, -3313, 60]]]
  hmulB := by decide  
  f := ![![![-1, 59, -1], ![227, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -168, 227]], ![![0, -1, 1], ![3, 131, -177], ![-86, -59, 60]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [13, 182, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 226], [0, 1]]
 g := ![![[14, 9], [27, 84], [28], [134], [189], [65, 53], [45, 1]], ![[192, 218], [175, 143], [28], [134], [189], [180, 174], [90, 226]]]
 h' := ![![[45, 226], [103, 224], [76, 159], [101, 153], [150, 19], [63, 102], [96, 196], [0, 1]], ![[0, 1], [195, 3], [194, 68], [176, 74], [97, 208], [113, 125], [63, 31], [45, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [48, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [13, 182, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3828, 3525, 552]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, -393, 552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-50, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-50, 1, 0]] 
 ![![227, 0, 0], ![177, 1, 0], ![167, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-50, 1, 0], ![0, -49, 3], ![327, 58, -50]]]
  hmulB := by decide  
  f := ![![![9201, -184, 0], ![41768, 0, 0]], ![![7151, -143, 0], ![32462, 0, 0]], ![![6821, -120, -1], ![30964, 76, 0]]]
  g := ![![![1, 0, 0], ![-177, 227, 0], ![-167, 0, 227]], ![![-1, 1, 0], ![36, -49, 3], ![-7, 58, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![2, -59, 1]] ![![227, 0, 0], ![-50, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-11350, 227, 0]], ![![454, -13393, 227], ![227, 2951, -227]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-50, 1, 0]]], ![![![2, -59, 1]], ![![1, 13, -1]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-43, 88, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-43, 88, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![186, 88, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-43, 88, 1], ![327, 103, 264], ![28667, 5213, 15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-186, -88, 229]], ![![-1, 0, 1], ![-213, -101, 264], ![113, 17, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [175, 201, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 228], [0, 1]]
 g := ![![[9, 226], [56], [23, 153], [27], [19], [203, 130], [28, 1]], ![[154, 3], [56], [185, 76], [27], [19], [179, 99], [56, 228]]]
 h' := ![![[28, 228], [67, 40], [97, 96], [218, 100], [94, 16], [199, 146], [138, 151], [0, 1]], ![[0, 1], [42, 189], [37, 133], [41, 129], [84, 213], [165, 83], [15, 78], [28, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [109]]
 b := ![[], [153, 169]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [175, 201, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![353428, 282809, 107021]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-85382, -39891, 107021]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-35, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-35, 1, 0]] 
 ![![229, 0, 0], ![194, 1, 0], ![214, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-35, 1, 0], ![0, -34, 3], ![327, 58, -35]]]
  hmulB := by decide  
  f := ![![![3431, -98, 0], ![22442, 0, 0]], ![![2906, -83, 0], ![19008, 0, 0]], ![![3246, -70, -2], ![21232, 153, 0]]]
  g := ![![![1, 0, 0], ![-194, 229, 0], ![-214, 0, 229]], ![![-1, 1, 0], ![26, -34, 3], ![-15, 58, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-43, 88, 1]] ![![229, 0, 0], ![-35, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-8015, 229, 0]], ![![-9847, 20152, 229], ![1832, -2977, 229]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-35, 1, 0]]], ![![![-43, 88, 1]], ![![8, -13, 1]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0]] 
 ![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [178, 94, 119, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [193, 135, 168], [154, 97, 65], [0, 1]]
 g := ![![[84, 146, 121], [61, 104], [9, 49], [121, 67, 71], [111, 51], [66, 134, 181], [1]], ![[2, 3, 152, 12], [121, 231], [19, 203], [94, 23, 74, 111], [63, 81], [206, 14, 205, 84], [170, 177, 1, 82]], ![[230, 2, 121, 17], [158, 112], [179, 162], [169, 113, 90, 194], [8, 232], [91, 96, 127, 82], [7, 10, 139, 151]]]
 h' := ![![[193, 135, 168], [1, 112, 222], [181, 66, 156], [131, 51, 7], [98, 182, 49], [135, 230, 135], [55, 139, 114], [0, 1]], ![[154, 97, 65], [167, 119, 41], [6, 132, 124], [91, 227, 160], [61, 99, 146], [215, 73, 9], [105, 73, 159], [193, 135, 168]], ![[0, 1], [98, 2, 203], [31, 35, 186], [111, 188, 66], [36, 185, 38], [166, 163, 89], [141, 21, 193], [154, 97, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [186, 62], []]
 b := ![[], [18, 51, 130], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [178, 94, 119, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2165269, 733018, 173352]
  a := ![-1, 2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9293, 3146, 744]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![30, 1, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![30, 1, 0]] 
 ![![239, 0, 0], ![30, 1, 0], ![168, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![30, 1, 0], ![0, 31, 3], ![327, 58, 30]]]
  hmulB := by decide  
  f := ![![![181, 6, 0], ![-1434, 0, 0]], ![![-30, -1, 0], ![240, 0, 0]], ![![132, -6, -1], ![-1046, 80, 0]]]
  g := ![![![1, 0, 0], ![-30, 239, 0], ![-168, 0, 239]], ![![0, 1, 0], ![-6, 31, 3], ![-27, 58, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N0 : Nat.card (O ⧸ I239N0) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N0)

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := prime_ideal_of_norm_prime hp239.out _ NI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![33, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![33, 1, 0]] 
 ![![239, 0, 0], ![33, 1, 0], ![104, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![33, 1, 0], ![0, 34, 3], ![327, 58, 33]]]
  hmulB := by decide  
  f := ![![![694, 21, 0], ![-5019, 0, 0]], ![![66, 2, 0], ![-477, 0, 0]], ![![244, -4, -1], ![-1764, 80, 0]]]
  g := ![![![1, 0, 0], ![-33, 239, 0], ![-104, 0, 239]], ![![0, 1, 0], ![-6, 34, 3], ![-21, 58, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-64, 1, 0]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-64, 1, 0]] 
 ![![239, 0, 0], ![175, 1, 0], ![90, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-64, 1, 0], ![0, -63, 3], ![327, 58, -64]]]
  hmulB := by decide  
  f := ![![![12737, -199, 0], ![47561, 0, 0]], ![![9345, -146, 0], ![34895, 0, 0]], ![![4806, -54, -1], ![17946, 80, 0]]]
  g := ![![![1, 0, 0], ![-175, 239, 0], ![-90, 0, 239]], ![![-1, 1, 0], ![45, -63, 3], ![-17, 58, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![30, 1, 0]] ![![239, 0, 0], ![33, 1, 0]]
  ![![239, 0, 0], ![-148, 101, 1]] where
 M := ![![![57121, 0, 0], ![7887, 239, 0]], ![![7170, 239, 0], ![990, 64, 3]]]
 hmul := by decide  
 g := ![![![![239, 0, 0], ![0, 0, 0]], ![![33, 1, 0], ![0, 0, 0]]], ![![![30, 1, 0], ![0, 0, 0]], ![![6, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-148, 101, 1]] ![![239, 0, 0], ![-64, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-15296, 239, 0]], ![![-35372, 24139, 239], ![9799, -6453, 239]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-64, 1, 0]]], ![![![-148, 101, 1]], ![![41, -27, 1]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1, I239N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
    exact isPrimeI239N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0 ⊙ MulI239N1)
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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [151, 211, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [120, 169, 114], [88, 71, 127], [0, 1]]
 g := ![![[162, 187, 108], [66, 183], [21, 162], [83, 217], [96, 13, 18], [145, 161, 125], [1]], ![[9, 42, 222, 124], [129, 122], [216, 191], [157, 141], [50, 19, 59, 139], [145, 85, 234, 26], [22, 127, 27, 117]], ![[224, 54, 31, 44], [0, 225], [145, 160], [7, 233], [39, 168, 36, 44], [71, 116, 62, 148], [140, 97, 27, 124]]]
 h' := ![![[120, 169, 114], [228, 83, 146], [109, 107, 122], [90, 54, 43], [205, 44, 159], [36, 189, 66], [90, 30, 208], [0, 1]], ![[88, 71, 127], [203, 12, 66], [99, 20, 134], [105, 71, 51], [215, 32, 158], [48, 175, 204], [82, 227, 113], [120, 169, 114]], ![[0, 1], [183, 146, 29], [119, 114, 226], [223, 116, 147], [202, 165, 165], [213, 118, 212], [233, 225, 161], [88, 71, 127]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170, 166], []]
 b := ![[], [5, 160, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [151, 211, 33, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26251166, 8822287, 2017652]
  a := ![0, 3, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![108926, 36607, 8372]
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


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [197, 201, 120, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [238, 174, 191], [144, 76, 60], [0, 1]]
 g := ![![[23, 220, 60], [102, 65, 88], [176, 198], [27, 170, 45], [113, 94, 119], [91, 183, 93], [1]], ![[217, 103, 185, 34], [97, 197, 189, 188], [218, 140], [106, 19, 205, 126], [61, 151, 141, 62], [114, 142, 152, 200], [96, 174, 197, 111]], ![[84, 44, 172, 245], [79, 65, 108, 75], [158, 125], [228, 89, 204, 218], [148, 144, 132, 17], [142, 227, 56, 28], [172, 147, 47, 140]]]
 h' := ![![[238, 174, 191], [237, 197, 173], [11, 75, 29], [203, 48, 82], [78, 125, 203], [145, 29, 118], [54, 50, 131], [0, 1]], ![[144, 76, 60], [143, 38, 73], [130, 204, 214], [197, 11, 89], [87, 100, 147], [39, 16, 200], [226, 6, 179], [238, 174, 191]], ![[0, 1], [40, 16, 5], [3, 223, 8], [235, 192, 80], [152, 26, 152], [218, 206, 184], [89, 195, 192], [144, 76, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92, 103], []]
 b := ![[], [197, 25, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [197, 201, 120, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-163636689, -47312496, -9492318]
  a := ![2, -8, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-651939, -188496, -37818]
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

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![464, 164, -39]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![464, 164, -39]] 
 ![![257, 0, 0], ![0, 257, 0], ![54, 121, 1]] where
  M :=![![![464, 164, -39], ![-12753, -1634, 492], ![57879, 5261, -1798]]]
  hmulB := by decide  
  f := ![![![1360, 349, 66]], ![![21582, 5537, 1047]], ![![10863, 2787, 527]]]
  g := ![![![10, 19, -39], ![-153, -238, 492], ![603, 867, -1798]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [162, 227, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 256], [0, 1]]
 g := ![![[95, 211], [226], [249], [198], [159], [123], [129], [1]], ![[0, 46], [226], [249], [198], [159], [123], [129], [1]]]
 h' := ![![[30, 256], [157, 89], [180, 212], [244, 121], [127, 55], [151, 38], [206, 61], [95, 30], [0, 1]], ![[0, 1], [0, 168], [115, 45], [19, 136], [235, 202], [6, 219], [237, 196], [224, 227], [30, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155]]
 b := ![[], [251, 206]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [162, 227, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3173, 109, 311]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-53, -146, 311]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1360, -349, -66]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-1360, -349, -66]] 
 ![![257, 0, 0], ![151, 1, 0], ![145, 0, 1]] where
  M :=![![![-1360, -349, -66], ![-21582, -5537, -1047], ![-106929, -27436, -5188]]]
  hmulB := by decide  
  f := ![![![-464, -164, 39]], ![![-223, -90, 21]], ![![-487, -113, 29]]]
  g := ![![![237, -349, -66], ![3760, -5537, -1047], ![18631, -27436, -5188]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![464, 164, -39]] ![![-1360, -349, -66]]
  ![![257, 0, 0]] where
 M := ![![![-257, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB267I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB267I4 : PrimesBelowBoundCertificateInterval O 193 257 267 where
  m := 11
  g := ![1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB267I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0]
    · exact ![I239N0, I239N1, I239N2]
    · exact ![I241N0]
    · exact ![I251N0]
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
    · exact ![7645373]
    · exact ![7880599]
    · exact ![44521, 211]
    · exact ![49729, 223]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![12649337]
    · exact ![239, 239, 239]
    · exact ![13997521]
    · exact ![15813251]
    · exact ![66049, 257]
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
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
  β := ![I211N1, I223N1, I227N1, I229N1, I239N0, I239N1, I239N2, I257N1]
  Il := ![[], [], [I211N1], [I223N1], [I227N1], [I229N1], [], [I239N0, I239N1, I239N2], [], [], [I257N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
