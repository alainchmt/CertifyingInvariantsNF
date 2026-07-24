
import IdealArithmetic.Examples.NF3_1_688076_2.RI3_1_688076_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![34, 41, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![34, 41, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![34, 41, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![34, 41, 1], ![-133, 54, 83], ![-7211, 743, 95]]]
  hmulB := by decide  
  f := ![![![-33, -41, -1], ![197, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -41, 197]], ![![0, 0, 1], ![-15, -17, 83], ![-53, -16, 95]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [47, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [190, 196], [0, 1]]
 g := ![![[172, 109], [171], [73, 36], [138], [7], [4], [190, 1]], ![[0, 88], [171], [18, 161], [138], [7], [4], [183, 196]]]
 h' := ![![[190, 196], [66, 122], [115, 34], [142, 6], [18, 27], [97, 106], [132, 2], [0, 1]], ![[0, 1], [0, 75], [74, 163], [100, 191], [26, 170], [143, 91], [118, 195], [190, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [78, 163]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [47, 7, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-962, -233, 76]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -17, 76]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-83, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-83, 1, 0]] 
 ![![197, 0, 0], ![114, 1, 0], ![102, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-83, 1, 0], ![1, -83, 2], ![-174, 20, -82]]]
  hmulB := by decide  
  f := ![![![5046, -590935, 14240], ![-4925, -1402640, 0]], ![![2959, -341946, 8240], ![-2757, -811640, 0]], ![![2584, -305966, 7373], ![-2618, -726240, 0]]]
  g := ![![![1, 0, 0], ![-114, 197, 0], ![-102, 0, 197]], ![![-1, 1, 0], ![47, -83, 2], ![30, 20, -82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![34, 41, 1]] ![![197, 0, 0], ![-83, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-16351, 197, 0]], ![![6698, 8077, 197], ![-2955, -3349, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-83, 1, 0]]], ![![![34, 41, 1]], ![![-15, -17, 0]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [168, 117, 194, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 104, 154], [194, 94, 45], [0, 1]]
 g := ![![[26, 49, 122], [82, 106, 63], [80, 3, 47], [186, 65], [155, 114], [149, 25], [1]], ![[29, 196, 97, 34], [53, 14, 68, 166], [182, 46, 177, 142], [55, 7], [77, 57], [4, 102], [81, 60, 60, 17]], ![[29, 66, 21, 123], [163, 13, 97, 92], [184, 179, 143, 161], [73, 40], [127, 80], [26, 165], [174, 96, 34, 182]]]
 h' := ![![[10, 104, 154], [154, 166, 108], [92, 93, 62], [87, 10, 68], [93, 11, 57], [8, 167, 78], [31, 82, 5], [0, 1]], ![[194, 94, 45], [167, 172, 95], [176, 140, 51], [145, 22, 171], [80, 39, 87], [190, 93, 16], [128, 101, 163], [10, 104, 154]], ![[0, 1], [90, 60, 195], [52, 165, 86], [195, 167, 159], [188, 149, 55], [80, 138, 105], [95, 16, 31], [194, 94, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 49], []]
 b := ![[], [108, 110, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [168, 117, 194, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2322330, -909828, 155419]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11670, -4572, 781]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![88, 19, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![88, 19, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![88, 19, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![88, 19, 1], ![-155, 108, 39], ![-3383, 303, 127]]]
  hmulB := by decide  
  f := ![![![-87, -19, -1], ![211, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-88, -19, 211]], ![![0, 0, 1], ![-17, -3, 39], ![-69, -10, 127]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [108, 123, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 210], [0, 1]]
 g := ![![[7, 20], [21, 62], [62], [43], [159, 154], [123], [88, 1]], ![[79, 191], [202, 149], [62], [43], [207, 57], [123], [176, 210]]]
 h' := ![![[88, 210], [53, 81], [169, 22], [18, 189], [130, 185], [90, 187], [202, 40], [0, 1]], ![[0, 1], [7, 130], [206, 189], [192, 22], [163, 26], [88, 24], [135, 171], [88, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [178, 159]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [108, 123, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-316105, -338059, 87452]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37971, -9477, 87452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-39, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-39, 1, 0]] 
 ![![211, 0, 0], ![172, 1, 0], ![84, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-39, 1, 0], ![1, -39, 2], ![-174, 20, -38]]]
  hmulB := by decide  
  f := ![![![-22994, 960645, -49266], ![8862, 5197563, 0]], ![![-18713, 783046, -40158], ![7386, 4236669, 0]], ![![-9120, 382436, -19613], ![3712, 2069172, 0]]]
  g := ![![![1, 0, 0], ![-172, 211, 0], ![-84, 0, 211]], ![![-1, 1, 0], ![31, -39, 2], ![-2, 20, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![88, 19, 1]] ![![211, 0, 0], ![-39, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-8229, 211, 0]], ![![18568, 4009, 211], ![-3587, -633, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-39, 1, 0]]], ![![![88, 19, 1]], ![![-17, -3, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-34, -82, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-34, -82, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![189, 141, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-34, -82, 1], ![-256, -14, -163], ![14191, -1717, -96]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-189, -141, 223]], ![![-1, -1, 1], ![137, 103, -163], ![145, 53, -96]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [183, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [149, 222], [0, 1]]
 g := ![![[210, 39], [74, 1], [13, 162], [170, 130], [213, 197], [136], [149, 1]], ![[0, 184], [0, 222], [67, 61], [139, 93], [130, 26], [136], [75, 222]]]
 h' := ![![[149, 222], [61, 40], [74, 1], [110, 88], [46, 24], [18, 33], [162, 164], [0, 1]], ![[0, 1], [0, 183], [0, 222], [65, 135], [54, 199], [29, 190], [68, 59], [149, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [201]]
 b := ![[], [39, 212]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [183, 74, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-145, -2055, 142]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-121, -99, 142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-60, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-60, 1, 0]] 
 ![![223, 0, 0], ![163, 1, 0], ![96, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-60, 1, 0], ![1, -60, 2], ![-174, 20, -59]]]
  hmulB := by decide  
  f := ![![![-3437, 238671, -7956], ![2007, 887094, 0]], ![![-2486, 174413, -5814], ![1562, 648261, 0]], ![![-1464, 102746, -3425], ![922, 381888, 0]]]
  g := ![![![1, 0, 0], ![-163, 223, 0], ![-96, 0, 223]], ![![-1, 1, 0], ![43, -60, 2], ![10, 20, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![-34, -82, 1]] ![![223, 0, 0], ![-60, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![-13380, 223, 0]], ![![-7582, -18286, 223], ![1784, 4906, -223]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![-60, 1, 0]]], ![![![-34, -82, 1]], ![![8, 22, -1]]]]
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


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [120, 166, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 187, 188], [139, 39, 39], [0, 1]]
 g := ![![[174, 115, 81], [114, 221, 173], [187, 214], [184, 212], [39, 129], [25, 187, 19], [1]], ![[186, 159, 63, 82], [211, 223, 207, 189], [88, 87], [175, 109], [132, 205], [66, 59, 8, 63], [163, 182, 134, 155]], ![[212, 129, 197, 154], [89, 46, 49, 146], [6, 78], [216, 28], [58, 92], [115, 62, 46, 163], [204, 109, 70, 72]]]
 h' := ![![[4, 187, 188], [167, 170, 9], [206, 193, 207], [20, 146, 21], [218, 211, 62], [178, 68, 105], [107, 61, 143], [0, 1]], ![[139, 39, 39], [63, 21, 77], [198, 24, 92], [61, 12, 119], [75, 60, 91], [5, 208, 81], [26, 30, 20], [4, 187, 188]], ![[0, 1], [199, 36, 141], [23, 10, 155], [210, 69, 87], [5, 183, 74], [137, 178, 41], [18, 136, 64], [139, 39, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123, 125], []]
 b := ![[], [226, 45, 172], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [120, 166, 84, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-132114, 3178, 6356]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-582, 14, 28]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-88, 60, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-88, 60, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![141, 60, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-88, 60, 1], ![-114, -68, 121], ![-10517, 1123, -8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-141, -60, 229]], ![![-1, 0, 1], ![-75, -32, 121], ![-41, 7, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [124, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [158, 228], [0, 1]]
 g := ![![[128, 146], [193], [197, 149], [61], [202], [197, 214], [158, 1]], ![[67, 83], [193], [152, 80], [61], [202], [117, 15], [87, 228]]]
 h' := ![![[158, 228], [13, 157], [75, 184], [154, 148], [42, 176], [75, 109], [102, 108], [0, 1]], ![[0, 1], [87, 72], [64, 45], [180, 81], [141, 53], [122, 120], [220, 121], [158, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [74, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [124, 71, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19898, 3012, 1241]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-851, -312, 1241]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![108, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![108, 1, 0]] 
 ![![229, 0, 0], ![108, 1, 0], ![8, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![108, 1, 0], ![1, 108, 2], ![-174, 20, 109]]]
  hmulB := by decide  
  f := ![![![-7267, -1216475, -22528], ![-8473, 2579456, 0]], ![![-3476, -573679, -10624], ![-3892, 1216448, 0]], ![![-260, -42497, -787], ![-283, 90112, 0]]]
  g := ![![![1, 0, 0], ![-108, 229, 0], ![-8, 0, 229]], ![![0, 1, 0], ![-51, 108, 2], ![-14, 20, 109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-88, 60, 1]] ![![229, 0, 0], ![108, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![24732, 229, 0]], ![![-20152, 13740, 229], ![-9618, 6412, 229]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![108, 1, 0]]], ![![![-88, 60, 1]], ![![-42, 28, 1]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28, -3, -2]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![28, -3, -2]] 
 ![![233, 0, 0], ![0, 233, 0], ![219, 118, 1]] where
  M :=![![![28, -3, -2], ![345, -12, -8], ![676, 94, -15]]]
  hmulB := by decide  
  f := ![![![-4, 1, 0]], ![![1, -4, 2]], ![![-4, -1, 1]]]
  g := ![![![2, 1, -2], ![9, 4, -8], ![17, 8, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [188, 227, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 232], [0, 1]]
 g := ![![[171, 170], [226], [71], [90, 9], [208], [158, 37], [6, 1]], ![[26, 63], [226], [71], [144, 224], [208], [147, 196], [12, 232]]]
 h' := ![![[6, 232], [115, 50], [165, 61], [89, 49], [227, 230], [120, 21], [37, 81], [0, 1]], ![[0, 1], [182, 183], [65, 172], [150, 184], [209, 3], [13, 212], [57, 152], [6, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [151]]
 b := ![[], [123, 192]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [188, 227, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2186, -384, -489]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![469, 246, -489]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-4, 1, 0]] 
 ![![233, 0, 0], ![229, 1, 0], ![109, 0, 1]] where
  M :=![![![-4, 1, 0], ![1, -4, 2], ![-174, 20, -3]]]
  hmulB := by decide  
  f := ![![![28, -3, -2]], ![![29, -3, -2]], ![![16, -1, -1]]]
  g := ![![![-1, 1, 0], ![3, -4, 2], ![-19, 20, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![28, -3, -2]] ![![-4, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![233, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB235I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 234 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 234 (by omega)

def PB235I4 : PrimesBelowBoundCertificateInterval O 193 234 235 where
  m := 7
  g := ![2, 1, 2, 2, 1, 2, 2]
  P := ![197, 199, 211, 223, 227, 229, 233]
  hP := PB235I4_primes
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
  β := ![I197N1, I211N1, I223N1, I229N1, I233N1]
  Il := ![[I197N1], [], [I211N1], [I223N1], [], [I229N1], [I233N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
