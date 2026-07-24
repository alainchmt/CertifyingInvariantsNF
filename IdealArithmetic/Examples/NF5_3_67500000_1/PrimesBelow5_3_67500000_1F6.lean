
import IdealArithmetic.Examples.NF5_3_67500000_1.RI5_3_67500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -53, -5, 19, 30]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![-10, -53, -5, 19, 30]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![58, 56, 1, 0, 0], ![175, 132, 0, 1, 0], ![27, 121, 0, 0, 1]] where
  M :=![![![-10, -53, -5, 19, 30], ![-33, -48, -1, 17, 24], ![-21, -55, -10, 25, 30], ![9, 1, -7, 4, 18], ![3, 25, 11, -15, -31]]]
  hmulB := by decide  
  f := ![![![10, -5, 23, 55, 60]], ![![-15, 18, 65, 151, 150]], ![![-1, 3, 20, 47, 48]], ![![-1, 6, 50, 117, 120]], ![![-6, 8, 33, 77, 77]]]
  g := ![![![-15, -23, -5, 19, 30], ![-14, -20, -1, 17, 24], ![-18, -25, -10, 25, 30], ![-3, -9, -7, 4, 18], ![11, 20, 11, -15, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [65, 199, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 256], [0, 1]]
 g := ![![[94, 190], [120], [222], [195], [242], [159], [23], [1]], ![[63, 67], [120], [222], [195], [242], [159], [23], [1]]]
 h' := ![![[58, 256], [27, 226], [84, 67], [76, 215], [71, 130], [102, 146], [160, 219], [192, 58], [0, 1]], ![[0, 1], [28, 31], [115, 190], [210, 42], [158, 127], [89, 111], [12, 38], [215, 199], [58, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [154]]
 b := ![[], [80, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [65, 199, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-949, -1355, 803, -1108, -1194]
  a := ![-5, -7, 2, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![695, 951, 803, -1108, -1194]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28, -33, -3, 13, 18]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-28, -33, -3, 13, 18]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![127, 86, 1, 0, 0], ![193, 221, 0, 1, 0], ![23, 167, 0, 0, 1]] where
  M :=![![![-28, -33, -3, 13, 18], ![-15, -46, -5, 15, 24], ![-27, -47, -4, 11, 18], ![-3, -3, -5, -4, -6], ![15, 25, 3, -11, -13]]]
  hmulB := by decide  
  f := ![![![-20, 7, 1, -3, -12]], ![![27, 8, -23, 5, 18]], ![![-1, 6, -7, 0, 0]], ![![8, 12, -19, 2, 6]], ![![16, 6, -15, 3, 11]]]
  g := ![![![-10, -22, -3, 13, 18], ![-11, -27, -5, 15, 24], ![-8, -20, -4, 11, 18], ![6, 9, -5, -4, -6], ![8, 17, 3, -11, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P1 : CertificateIrreducibleZModOfList' 257 2 2 8 [225, 191, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 256], [0, 1]]
 g := ![![[243, 8], [168], [190], [67], [239], [111], [244], [1]], ![[0, 249], [168], [190], [67], [239], [111], [244], [1]]]
 h' := ![![[66, 256], [47, 120], [117, 164], [132, 31], [72, 239], [52, 204], [94, 25], [32, 66], [0, 1]], ![[0, 1], [0, 137], [147, 93], [122, 226], [169, 18], [152, 53], [202, 232], [19, 191], [66, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [195, 181]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N1 : CertifiedPrimeIdeal' SI257N1 257 where
  n := 2
  hpos := by decide
  P := [225, 191, 1]
  hirr := P257P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6723, 6699, -18967, 55496, 8436]
  a := ![6, -59, -1, -60, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-33032, -46831, -18967, 55496, 8436]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N1 B_one_repr
lemma NI257N1 : Nat.card (O ⧸ I257N1) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N1

def I257N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30, 72, 6, -27, -40]] i)))

def SI257N2: IdealEqSpanCertificate' Table ![![30, 72, 6, -27, -40]] 
 ![![257, 0, 0, 0, 0], ![115, 1, 0, 0, 0], ![139, 0, 1, 0, 0], ![174, 0, 0, 1, 0], ![251, 0, 0, 0, 1]] where
  M :=![![![30, 72, 6, -27, -40], ![39, 75, 6, -29, -42], ![39, 84, 7, -33, -48], ![3, 8, 0, -4, -6], ![-22, -48, -4, 18, 27]]]
  hmulB := by decide  
  f := ![![![-48, 24, -8, -9, -50]], ![![-21, 11, -4, -4, -22]], ![![-27, 12, -3, -6, -28]], ![![-33, 16, -6, -6, -36]], ![![-46, 24, -8, -9, -47]]]
  g := ![![![22, 72, 6, -27, -40], ![24, 75, 6, -29, -42], ![28, 84, 7, -33, -48], ![5, 8, 0, -4, -6], ![-15, -48, -4, 18, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N2 : Nat.card (O ⧸ I257N2) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N2)

lemma isPrimeI257N2 : Ideal.IsPrime I257N2 := prime_ideal_of_norm_prime hp257.out _ NI257N2
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![-10, -53, -5, 19, 30]] ![![-28, -33, -3, 13, 18]]
  ![![1603, 3696, 310, -1386, -2046]] where
 M := ![![![1603, 3696, 310, -1386, -2046]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI257N1 : IdealMulLeCertificate' Table 
  ![![1603, 3696, 310, -1386, -2046]] ![![30, 72, 6, -27, -40]]
  ![![257, 0, 0, 0, 0]] where
 M := ![![![245178, 505776, 42148, -191979, -281158]]]
 hmul := by decide  
 g := ![![![![954, 1968, 164, -747, -1094]]]]
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
instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 8, -12, 4, 20]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![27, 8, -12, 4, 20]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![53, 198, 236, 1, 0], ![188, 66, 110, 0, 1]] where
  M :=![![![27, 8, -12, 4, 20], ![-48, -33, 60, -32, -36], ![12, 24, -77, 60, -84], ![240, 200, -204, 71, 324], ![-232, -200, 224, -88, -273]]]
  hmulB := by decide  
  f := ![![![21, 8, 4, 4, 4]], ![![0, 25, 12, 16, 12]], ![![12, 24, 29, 60, 60]], ![![15, 42, 36, 67, 64]], ![![20, 22, 18, 32, 31]]]
  g := ![![![-15, -8, -12, 4, 20], ![32, 33, 44, -32, -36], ![48, -24, -19, 60, -84], ![-245, -134, -200, 71, 324], ![212, 134, 194, -88, -273]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [32, 134, 69, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [190, 125, 100], [4, 137, 163], [0, 1]]
 g := ![![[142, 181, 31], [202, 200, 6], [208, 184, 149], [168, 31], [47, 49], [249, 140], [194, 1], []], ![[104, 212, 246, 190], [78, 259, 99, 46], [177, 46, 222, 86], [31, 234], [93, 218], [176, 51], [183, 96], [127, 6]], ![[133, 221, 95, 238], [151, 71, 8, 116], [43, 61, 259, 21], [67, 129], [120, 128], [119, 69], [234, 108], [64, 6]]]
 h' := ![![[190, 125, 100], [111, 182, 174], [182, 32, 100], [172, 204, 181], [258, 154, 174], [218, 57, 7], [104, 9, 156], [0, 0, 1], [0, 1]], ![[4, 137, 163], [217, 72, 221], [210, 84, 68], [163, 244, 224], [41, 254, 51], [178, 76, 84], [63, 255, 180], [213, 45, 137], [190, 125, 100]], ![[0, 1], [217, 9, 131], [146, 147, 95], [81, 78, 121], [252, 118, 38], [161, 130, 172], [63, 262, 190], [72, 218, 125], [4, 137, 163]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [180, 57], []]
 b := ![[], [223, 219, 102], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [32, 134, 69, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2833, -2136, -58, 1205, -8214]
  a := ![-1, -5, 1, -6, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5618, 1146, 2354, 1205, -8214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, 122, 140, 278, 272]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![33, 122, 140, 278, 272]] 
 ![![263, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![126, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![123, 0, 0, 0, 1]] where
  M :=![![![33, 122, 140, 278, 272], ![18, 191, 382, 842, 852], ![-30, 370, 1063, 2438, 2496], ![-96, 334, 1300, 3051, 3144], ![-34, -46, 54, 162, 177]]]
  hmulB := by decide  
  f := ![![![963, -110, -280, 126, 760]], ![![66, -13, -14, 6, 52]], ![![468, -46, -149, 70, 360]], ![![189, 0, -64, 25, 168]], ![![425, -72, -110, 52, 321]]]
  g := ![![![-251, 122, 140, 278, 272], ![-740, 191, 382, 842, 852], ![-2122, 370, 1063, 2438, 2496], ![-2641, 334, 1300, 3051, 3144], ![-133, -46, 54, 162, 177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, -26, -4, 6, 12]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![41, -26, -4, 6, 12]] 
 ![![263, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![159, 0, 1, 0, 0], ![173, 0, 0, 1, 0], ![197, 0, 0, 0, 1]] where
  M :=![![![41, -26, -4, 6, 12], ![-18, 19, -2, -2, 0], ![-6, -26, 23, -10, -12], ![12, 2, -20, 15, -12], ![-6, 6, 10, -10, 17]]]
  hmulB := by decide  
  f := ![![![331, 798, 360, 430, 324]], ![![44, 107, 50, 62, 48]], ![![201, 488, 227, 280, 216]], ![![217, 528, 248, 309, 240]], ![![247, 596, 270, 324, 245]]]
  g := ![![![-7, -26, -4, 6, 12], ![0, 19, -2, -2, 0], ![5, -26, 23, -10, -12], ![11, 2, -20, 15, -12], ![-13, 6, 10, -10, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![27, 8, -12, 4, 20]] ![![33, 122, 140, 278, 272]]
  ![![331, 798, 360, 430, 324]] where
 M := ![![![331, 798, 360, 430, 324]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![331, 798, 360, 430, 324]] ![![41, -26, -4, 6, 12]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![263, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1, I263N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
    exact isPrimeI263N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0 ⊙ MulI263N1)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-571, 2570, -1574, 568, 612]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![-571, 2570, -1574, 568, 612]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![264, 74, 170, 1, 0], ![107, 12, 157, 0, 1]] where
  M :=![![![-571, 2570, -1574, 568, 612], ![-132, -2277, 3270, -2056, 1572], ![-10884, -7746, 6551, -1200, -17052], ![23844, 22750, -29886, 14305, 21192], ![-18642, -18554, 25898, -13150, -13663]]]
  hmulB := by decide  
  f := ![![![-3983, -2674, 13078, 34240, 36300]], ![![-6180, 2915, 37746, 92576, 96540]], ![![-11892, 19674, 107383, 256680, 265836]], ![![-13164, 10732, 91576, 222449, 231384]], ![![-8795, 10570, 69583, 167606, 173945]]]
  g := ![![![-803, -174, -722, 568, 612], ![1392, 487, 394, -2056, 1572], ![7920, 1062, 10735, -1200, -17052], ![-22380, -4796, -21520, 14305, 21192], ![18271, 4158, 16381, -13150, -13663]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [145, 164, 215, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 187, 39], [193, 81, 230], [0, 1]]
 g := ![![[231, 193, 244], [15, 244], [237, 100, 64], [81, 28, 36], [146, 24], [134, 78], [54, 1], []], ![[184, 261, 211, 94], [154, 133], [223, 36, 53, 221], [249, 246, 112, 33], [31, 1], [243, 164], [134, 105], [149, 176]], ![[25, 76, 228, 243], [78, 66], [112, 105, 182, 129], [148, 156, 14, 193], [262, 220], [53, 172], [77, 268], [227, 176]]]
 h' := ![![[130, 187, 39], [162, 171, 128], [67, 105, 141], [91, 8, 261], [58, 70, 263], [241, 268, 37], [240, 145, 62], [0, 0, 1], [0, 1]], ![[193, 81, 230], [116, 42, 90], [216, 191, 183], [35, 79, 202], [266, 124, 92], [69, 146, 268], [146, 235, 186], [137, 9, 81], [130, 187, 39]], ![[0, 1], [152, 56, 51], [83, 242, 214], [50, 182, 75], [207, 75, 183], [82, 124, 233], [226, 158, 21], [30, 260, 187], [193, 81, 230]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [109, 256], []]
 b := ![[], [15, 19, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [145, 164, 215, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1500585, 1881266, -224430, 4362526, 5292294]
  a := ![8, 26, -3, 25, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6380973, -1429194, -5846632, 4362526, 5292294]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![760, 767, -1147, 613, 426]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![760, 767, -1147, 613, 426]] 
 ![![269, 0, 0, 0, 0], ![222, 1, 0, 0, 0], ![212, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![128, 0, 0, 0, 1]] where
  M :=![![![760, 767, -1147, 613, 426], ![561, 174, 819, -881, 2400], ![-9843, -8463, 9136, -3405, -12486], ![13341, 13181, -19965, 10712, 7314], ![-8913, -9287, 15475, -8875, -2177]]]
  hmulB := by decide  
  f := ![![![57632, 167459, 128813, 223369, 207540]], ![![47739, 139070, 107583, 187019, 173946]], ![![45449, 133457, 105036, 183955, 171624]], ![![5909, 19176, 18164, 34105, 32700]], ![![27239, 79381, 61459, 106877, 99421]]]
  g := ![![![5, 767, -1147, 613, 426], ![-1834, 174, 819, -881, 2400], ![6056, -8463, 9136, -3405, -12486], ![271, 13181, -19965, 10712, 7314], ![-2572, -9287, 15475, -8875, -2177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-612, 401, 43, -79, -194]] i)))

def SI269N2: IdealEqSpanCertificate' Table ![![-612, 401, 43, -79, -194]] 
 ![![269, 0, 0, 0, 0], ![245, 1, 0, 0, 0], ![231, 0, 1, 0, 0], ![94, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-612, 401, 43, -79, -194], ![345, -224, -23, 43, 108], ![-195, 127, 14, -25, -66], ![-111, 83, 1, -12, -30], ![133, -97, -3, 15, 39]]]
  hmulB := by decide  
  f := ![![![-192, 733, 2755, 6441, 6632]], ![![-177, 675, 2538, 5934, 6110]], ![![-171, 650, 2447, 5722, 5892]], ![![-75, 281, 1063, 2486, 2560]], ![![-11, 42, 158, 370, 381]]]
  g := ![![![-366, 401, 43, -79, -194], ![204, -224, -23, 43, 108], ![-116, 127, 14, -25, -66], ![-71, 83, 1, -12, -30], ![84, -97, -3, 15, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![-571, 2570, -1574, 568, 612]] ![![760, 767, -1147, 613, 426]]
  ![![18623624, 15133149, -13489717, 3398193, 28399746]] where
 M := ![![![18623624, 15133149, -13489717, 3398193, 28399746]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI269N1 : IdealMulLeCertificate' Table 
  ![![18623624, 15133149, -13489717, 3398193, 28399746]] ![![-612, 401, 43, -79, -194]]
  ![![269, 0, 0, 0, 0]] where
 M := ![![![-146259873, -107671554, 182096322, -98080090, -82637338]]]
 hmul := by decide  
 g := ![![![![-543717, -400266, 676938, -364610, -307202]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1, I269N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
    exact isPrimeI269N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0 ⊙ MulI269N1)
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0, 0, 0]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0, 0, 0]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![0, 0, 0, 271, 0], ![0, 0, 0, 0, 271]] where
  M :=![![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![0, 0, 0, 271, 0], ![0, 0, 0, 0, 271]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 5 2 8 [137, 150, 100, 77, 21, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 136, 36, 84, 142], [221, 86, 105, 5, 230], [35, 190, 38, 105, 113], [132, 129, 92, 77, 57], [0, 1]]
 g := ![![[92, 197, 122, 39, 2], [89, 234, 1, 2, 79], [50, 23, 217, 249, 180], [229, 261, 151, 179, 69], [248, 103, 80, 37], [106, 93, 250, 1], [], []], ![[223, 113, 119, 247, 116, 68, 267, 94], [158, 1, 55, 263, 258, 44, 267, 27], [86, 249, 69, 118, 21, 87, 129, 239], [104, 166, 63, 263, 227, 111, 131, 188], [224, 5, 61, 245], [49, 245, 141, 138], [121, 189, 162, 163], [155, 242, 137, 110]], ![[8, 160, 18, 238, 270, 133, 197, 181], [188, 1, 61, 189, 117, 92, 163, 152], [249, 32, 145, 182, 69, 266, 186, 137], [239, 100, 139, 187, 165, 118, 118, 66], [59, 8, 126, 74], [19, 225, 192, 57], [168, 157, 58, 229], [250, 262, 61, 55]], ![[8, 42, 20, 142, 228, 53, 263, 54], [63, 233, 11, 249, 225, 57, 128, 135], [110, 152, 58, 54, 198, 43, 180, 38], [221, 84, 180, 100, 196, 150, 26, 116], [12, 57, 263, 5], [133, 225, 112, 18], [18, 4, 4, 154], [25, 135, 23, 32]], ![[124, 149, 252, 32, 239, 232, 96, 217], [183, 218, 118, 152, 56, 145, 168, 187], [208, 35, 245, 170, 148, 18, 264, 67], [7, 235, 245, 32, 206, 128, 144, 112], [93, 67, 20, 129], [175, 266, 111, 170], [242, 70, 172, 35], [158, 91, 169, 268]]]
 h' := ![![[133, 136, 36, 84, 142], [2, 54, 178, 224, 175], [196, 93, 54, 77, 185], [63, 69, 117, 74, 73], [248, 249, 130, 230, 152], [112, 85, 7, 185, 151], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[221, 86, 105, 5, 230], [118, 78, 125, 69, 211], [251, 61, 177, 214, 5], [173, 146, 163, 166, 236], [64, 191, 69, 72, 69], [20, 76, 103, 248, 40], [212, 4, 20, 162, 42], [248, 97, 50, 218, 71], [133, 136, 36, 84, 142]], ![[35, 190, 38, 105, 113], [120, 106, 24, 151, 236], [190, 218, 250, 121, 119], [38, 65, 37, 49, 162], [115, 135, 138, 31, 33], [135, 217, 96, 206, 133], [242, 238, 75, 147, 190], [228, 119, 119, 140, 59], [221, 86, 105, 5, 230]], ![[132, 129, 92, 77, 57], [226, 195, 19, 174, 169], [216, 191, 216, 154, 52], [145, 105, 9, 94, 166], [96, 144, 32, 105, 120], [188, 240, 151, 249, 238], [184, 132, 88, 126, 17], [239, 269, 122, 157, 69], [35, 190, 38, 105, 113]], ![[0, 1], [92, 109, 196, 195, 22], [196, 250, 116, 247, 181], [243, 157, 216, 159, 176], [33, 94, 173, 104, 168], [120, 195, 185, 196, 251], [167, 168, 88, 107, 21], [114, 57, 250, 27, 72], [132, 129, 92, 77, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [193, 52, 245, 69], [], [], []]
 b := ![[], [7, 11, 83, 162, 177], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 5
  hpos := by decide
  P := [137, 150, 100, 77, 21, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12668283343, 9271140892, -4547226343, -1471340842, 25209053327]
  a := ![-10, -8, 5, -6, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![46746433, 34210852, -16779433, -5429302, 93022337]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 1461660310351 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def PBC271 : ContainsPrimesAboveP 271 ![I271N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![271, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 271 (by decide) 𝕀

instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8112, 10017, -15343, -44213, -47912]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![8112, 10017, -15343, -44213, -47912]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![110, 84, 146, 1, 0], ![86, 22, 222, 0, 1]] where
  M :=![![![8112, 10017, -15343, -44213, -47912], ![11097, 3866, -45293, -115413, -121542], ![18387, -15809, -129934, -315283, -327852], ![13305, -38853, -161753, -381226, -393300], ![-4091, -11489, -8167, -13649, -12483]]]
  hmulB := by decide  
  f := ![![![-5856, 3941, 337, -729, -1778]], ![![3147, -2372, 65, 265, 960]], ![![-2085, 1127, -22, -35, -1290]], ![![-2469, 1447, 137, -226, -1090]], ![![-3239, 1931, 97, -235, -1513]]]
  g := ![![![32462, 17249, 61647, -44213, -47912], ![83607, 44666, 158077, -115413, -121542], ![227057, 121591, 428464, -315283, -327852], ![273545, 146703, 515559, -381226, -393300], ![9281, 5089, 17169, -13649, -12483]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 3 2 8 [245, 59, 234, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 36, 44], [264, 240, 233], [0, 1]]
 g := ![![[71, 33, 213], [40, 160], [142, 258, 62], [227, 76], [196, 190, 213], [76, 41], [43, 1], []], ![[252, 103, 189, 37], [9, 268], [248, 32, 221, 20], [23, 92], [232, 275, 19, 111], [126, 1], [257, 261], [269, 274]], ![[125, 260, 219, 251], [178, 84], [190, 204, 119, 216], [206, 71], [88, 229, 24, 94], [200, 63], [117, 188], [80, 274]]]
 h' := ![![[56, 36, 44], [251, 13, 203], [112, 125, 161], [168, 133, 93], [178, 179, 195], [20, 91, 74], [268, 265, 128], [0, 0, 1], [0, 1]], ![[264, 240, 233], [41, 28, 263], [169, 82, 97], [118, 63, 195], [74, 102, 107], [237, 115, 158], [103, 97, 276], [110, 253, 240], [56, 36, 44]], ![[0, 1], [69, 236, 88], [196, 70, 19], [166, 81, 266], [105, 273, 252], [235, 71, 45], [162, 192, 150], [236, 24, 36], [264, 240, 233]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 162], []]
 b := ![[], [16, 31, 160], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 3
  hpos := by decide
  P := [245, 59, 234, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1121855, 905140, -608326, 219086, 2026356]
  a := ![6, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-712073, -224108, -1741682, 219086, 2026356]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 21253933 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, -31, -107, -249, -256]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![6, -31, -107, -249, -256]] 
 ![![277, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![101, 0, 0, 1, 0], ![49, 0, 0, 0, 1]] where
  M :=![![![6, -31, -107, -249, -256], ![21, -80, -301, -705, -726], ![63, -217, -848, -1991, -2052], ![81, -261, -1045, -2456, -2532], ![5, -9, -47, -113, -117]]]
  hmulB := by decide  
  f := ![![![-1458, 821, 173, -205, -502]], ![![-81, 46, 9, -11, -28]], ![![-111, 64, 13, -16, -36]], ![![-537, 296, 68, -77, -188]], ![![-253, 148, 26, -34, -85]]]
  g := ![![![146, -31, -107, -249, -256], ![413, -80, -301, -705, -726], ![1166, -217, -848, -1991, -2052], ![1438, -261, -1045, -2456, -2532], ![66, -9, -47, -113, -117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1

def I277N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![465, 4866, 9722, 21426, 21680]] i)))

def SI277N2: IdealEqSpanCertificate' Table ![![465, 4866, 9722, 21426, 21680]] 
 ![![277, 0, 0, 0, 0], ![246, 1, 0, 0, 0], ![147, 0, 1, 0, 0], ![78, 0, 0, 1, 0], ![152, 0, 0, 0, 1]] where
  M :=![![![465, 4866, 9722, 21426, 21680], ![-762, 9425, 27054, 62042, 63516], ![-4422, 21870, 75889, 176718, 181704], ![-7098, 23542, 93246, 219093, 225840], ![-1150, -642, 4098, 10614, 11223]]]
  hmulB := by decide  
  f := ![![![-10431, -11226, 22350, -14010, 3752]], ![![-9456, -10119, 19950, -12446, 2988]], ![![-4515, -5028, 10687, -6900, 3000]], ![![-3552, -3874, 7686, -4819, 1320]], ![![-5530, -5838, 11390, -7062, 1423]]]
  g := ![![![-27409, 4866, 9722, 21426, 21680], ![-75054, 9425, 27054, 62042, 63516], ![-209181, 21870, 75889, 176718, 181704], ![-256038, 23542, 93246, 219093, 225840], ![-10756, -642, 4098, 10614, 11223]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N2 : Nat.card (O ⧸ I277N2) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N2)

lemma isPrimeI277N2 : Ideal.IsPrime I277N2 := prime_ideal_of_norm_prime hp277.out _ NI277N2
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![8112, 10017, -15343, -44213, -47912]] ![![6, -31, -107, -249, -256]]
  ![![-4528393, 14247400, 57582212, 135467224, 139687842]] where
 M := ![![![-4528393, 14247400, 57582212, 135467224, 139687842]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI277N1 : IdealMulLeCertificate' Table 
  ![![-4528393, 14247400, 57582212, 135467224, 139687842]] ![![465, 4866, 9722, 21426, 21680]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![-1389778137261, 4471059353946, 17915498154942, 42125292445418, 43431315066334]]]
 hmul := by decide  
 g := ![![![![-5017249593, 16141008498, 64676888646, 152076868034, 156791751142]]]]
 hle2 := by decide  


def PBC277 : ContainsPrimesAboveP 277 ![I277N0, I277N1, I277N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
    exact isPrimeI277N1
    exact isPrimeI277N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 277 (by decide) (𝕀 ⊙ MulI277N0 ⊙ MulI277N1)
instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16274, 38311, 14213, 12991, 7548]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![16274, 38311, 14213, 12991, 7548]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![0, 0, 0, 281, 0], ![260, 48, 248, 92, 1]] where
  M :=![![![16274, 38311, 14213, 12991, 7548], ![16329, 46816, 34973, 59851, 55302], ![13647, 64949, 93020, 194197, 193200], ![-6669, 31421, 110591, 257790, 265140], ![-12093, -22979, 2995, 20985, 25625]]]
  hmulB := by decide  
  f := ![![![-74, 71, 9, -21, 18]], ![![-117, -182, 167, -63, -180]], ![![351, 401, -596, 325, 162]], ![![303, 213, 35, -158, 822]], ![![319, 457, -477, 205, 395]]]
  g := ![![![-6926, -1153, -6611, -2425, 7548], ![-51111, -9280, -48683, -17893, 55302], ![-178713, -32771, -170180, -62563, 193200], ![-245349, -45179, -233609, -85890, 265140], ![-23753, -4459, -22605, -8315, 25625]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 4 2 8 [200, 46, 81, 195, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [161, 193, 149, 148], [141, 145, 56, 217], [65, 223, 76, 197], [0, 1]]
 g := ![![[113, 248, 275, 98], [141, 143, 118], [230, 134, 236], [33, 34, 16, 56], [200, 232, 88, 2], [53, 271, 90], [1], []], ![[275, 140, 61, 43, 231, 243], [45, 2, 2], [268, 252, 39], [98, 90, 64, 178, 247, 84], [25, 153, 110, 255, 0, 110], [43, 92, 217], [189, 209, 156], [248, 188, 267]], ![[25, 91, 82, 8, 231, 31], [224, 233, 252], [192, 205, 29], [169, 206, 34, 187, 33, 253], [175, 66, 3, 90, 242, 172], [177, 91, 141], [137, 161, 280], [150, 20, 162]], ![[179, 192, 270, 246, 183, 193], [160, 32, 124], [236, 244, 5], [175, 158, 101, 49, 12, 199], [17, 197, 111, 104, 17, 55], [15, 41, 236], [4, 41, 62], [163, 14, 31]]]
 h' := ![![[161, 193, 149, 148], [14, 195, 59, 200], [26, 3, 39, 250], [144, 162, 279, 123], [183, 104, 50, 233], [176, 259, 38, 132], [81, 235, 200, 86], [0, 0, 1], [0, 1]], ![[141, 145, 56, 217], [45, 271, 196, 164], [89, 178, 271, 149], [166, 137, 63, 243], [96, 244, 122, 123], [41, 96, 82, 157], [140, 39, 61, 138], [206, 212, 0, 76], [161, 193, 149, 148]], ![[65, 223, 76, 197], [24, 87, 130, 146], [198, 261, 120, 50], [246, 19, 210, 121], [86, 101, 198, 166], [259, 112, 112, 98], [147, 176, 204, 215], [278, 204, 58, 53], [141, 145, 56, 217]], ![[0, 1], [34, 9, 177, 52], [0, 120, 132, 113], [58, 244, 10, 75], [148, 113, 192, 40], [150, 95, 49, 175], [79, 112, 97, 123], [6, 146, 222, 152], [65, 223, 76, 197]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [194, 192, 271], []]
 b := ![[], [], [239, 62, 204, 114], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 4
  hpos := by decide
  P := [200, 46, 81, 195, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23735442, -13306946, 34677832, 37999381, 8835239]
  a := ![6, 6, 4, 7, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8259422, -1556578, -7674240, -2757447, 8835239]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 6234839521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![74, -71, -9, 21, -18]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![74, -71, -9, 21, -18]] 
 ![![281, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![249, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![74, -71, -9, 21, -18], ![117, 182, -167, 63, 180], ![-351, -401, 596, -325, -162], ![-303, -213, -35, 158, -822], ![429, 351, -195, -25, 845]]]
  hmulB := by decide  
  f := ![![![-16274, -38311, -14213, -12991, -7548]], ![![-811, -1939, -782, -814, -546]], ![![-6535, -15501, -5996, -5869, -3696]], ![![-14397, -34060, -12988, -12429, -7632]], ![![-1289, -3054, -1174, -1138, -709]]]
  g := ![![![-10, -71, -9, 21, -18], ![-12, 182, -167, 63, 180], ![81, -401, 596, -325, -162], ![-50, -213, -35, 158, -822], ![16, 351, -195, -25, 845]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N1 : Nat.card (O ⧸ I281N1) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N1)

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := prime_ideal_of_norm_prime hp281.out _ NI281N1
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![16274, 38311, 14213, 12991, 7548]] ![![74, -71, -9, 21, -18]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![-281, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC281 : ContainsPrimesAboveP 281 ![I281N0, I281N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
    exact isPrimeI281N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 281 (by decide) (𝕀 ⊙ MulI281N0)
instance hp283 : Fact (Nat.Prime 283) := {out := by norm_num}

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1067, 2859, 1783, 2774, 2454]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![1067, 2859, 1783, 2774, 2454]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![244, 165, 266, 1, 0], ![82, 89, 128, 0, 1]] where
  M :=![![![1067, 2859, 1783, 2774, 2454], ![960, 3810, 4673, 9434, 9282], ![456, 6089, 12788, 28366, 28758], ![-1068, 4129, 15479, 36241, 37320], ![-867, -1507, 563, 2291, 2639]]]
  hmulB := by decide  
  f := ![![![-217, 33, 91, -56, -114]], ![![174, 48, -197, 128, 6]], ![![366, 343, -190, -16, 750]], ![![254, 375, -210, 9, 606]], ![![161, 183, -126, 19, 311]]]
  g := ![![![-3099, -2379, -3711, 2774, 2454], ![-10820, -8406, -13049, 9434, 9282], ![-32788, -25561, -39624, 28366, 28758], ![-42064, -32852, -50889, 36241, 37320], ![-2743, -2171, -3345, 2291, 2639]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 3 2 8 [154, 259, 148, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [157, 152, 106], [261, 130, 177], [0, 1]]
 g := ![![[78, 213, 248], [153, 49, 244], [213, 54], [196, 208, 266], [65, 113, 52], [76, 91], [135, 1], []], ![[39, 262, 270, 62], [234, 234, 243, 236], [57, 66], [143, 174, 184, 93], [105, 252, 268, 71], [192, 54], [192, 203], [225, 199]], ![[132, 240, 198, 19], [187, 231, 239, 27], [262, 81], [41, 31, 154, 149], [113, 136, 176, 31], [153, 38], [19, 181], [154, 199]]]
 h' := ![![[157, 152, 106], [210, 248, 75], [96, 218, 216], [97, 111, 232], [178, 180, 242], [80, 261, 202], [152, 256, 137], [0, 0, 1], [0, 1]], ![[261, 130, 177], [250, 93, 97], [2, 140, 248], [63, 26, 42], [112, 161, 166], [157, 115, 156], [24, 3, 232], [187, 125, 130], [157, 152, 106]], ![[0, 1], [162, 225, 111], [155, 208, 102], [113, 146, 9], [114, 225, 158], [123, 190, 208], [14, 24, 197], [257, 158, 152], [261, 130, 177]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [225, 180], []]
 b := ![[], [129, 42, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 3
  hpos := by decide
  P := [154, 259, 148, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4507, 8632, -13114, 23553, -2610]
  a := ![2, -2, -1, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19535, -12881, -21004, 23553, -2610]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 22665187 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, -3, -6, -6]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![1, -1, -3, -6, -6]] 
 ![![283, 0, 0, 0, 0], ![143, 1, 0, 0, 0], ![210, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![100, 0, 0, 0, 1]] where
  M :=![![![1, -1, -3, -6, -6], ![0, -2, -7, -18, -18], ![0, -7, -20, -50, -54], ![6, -3, -31, -59, -60], ![-3, -3, 3, -5, -5]]]
  hmulB := by decide  
  f := ![![![1, -715, -59, 236, 378]], ![![-1, -363, -30, 120, 192]], ![![0, -533, -44, 176, 282]], ![![0, -137, -11, 45, 72]], ![![1, -251, -21, 83, 133]]]
  g := ![![![6, -1, -3, -6, -6], ![16, -2, -7, -18, -18], ![47, -7, -20, -50, -54], ![57, -3, -31, -59, -60], ![2, -3, 3, -5, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N1 : Nat.card (O ⧸ I283N1) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N1)

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := prime_ideal_of_norm_prime hp283.out _ NI283N1

def I283N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, -114, -22, 30, 48]] i)))

def SI283N2: IdealEqSpanCertificate' Table ![![181, -114, -22, 30, 48]] 
 ![![283, 0, 0, 0, 0], ![174, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![268, 0, 0, 0, 1]] where
  M :=![![![181, -114, -22, 30, 48], ![-54, 105, -30, -2, 36], ![-114, -198, 217, -102, -120], ![54, 26, -162, 125, -144], ![6, 42, 70, -78, 187]]]
  hmulB := by decide  
  f := ![![![-10349, 34950, 137506, 322950, 332856]], ![![-6468, 21833, 85914, 201782, 207972]], ![![-481, 1584, 6291, 14784, 15240]], ![![-1978, 6622, 26138, 61401, 63288]], ![![-9818, 33150, 130434, 306342, 315739]]]
  g := ![![![21, -114, -22, 30, 48], ![-98, 105, -30, -2, 36], ![247, -198, 217, -102, -120], ![104, 26, -162, 125, -144], ![-192, 42, 70, -78, 187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N2 : Nat.card (O ⧸ I283N2) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N2)

lemma isPrimeI283N2 : Ideal.IsPrime I283N2 := prime_ideal_of_norm_prime hp283.out _ NI283N2
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![1067, 2859, 1783, 2774, 2454]] ![![1, -1, -3, -6, -6]]
  ![![10349, -34950, -137506, -322950, -332856]] where
 M := ![![![10349, -34950, -137506, -322950, -332856]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI283N1 : IdealMulLeCertificate' Table 
  ![![10349, -34950, -137506, -322950, -332856]] ![![181, -114, -22, 30, 48]]
  ![![283, 0, 0, 0, 0]] where
 M := ![![![-283, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC283 : ContainsPrimesAboveP 283 ![I283N0, I283N1, I283N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
    exact isPrimeI283N1
    exact isPrimeI283N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 283 (by decide) (𝕀 ⊙ MulI283N0 ⊙ MulI283N1)
instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4568, -2990, -324, 591, 1452]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![4568, -2990, -324, 591, 1452]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![60, 249, 233, 1, 0], ![145, 168, 92, 0, 1]] where
  M :=![![![4568, -2990, -324, 591, 1452], ![-2583, 1661, 184, -327, -810], ![1449, -950, -115, 197, 468], ![885, -570, -62, 110, 294], ![-1044, 678, 78, -136, -349]]]
  hmulB := by decide  
  f := ![![![-2, -10, -14, -31, -30]], ![![-3, -19, -38, -91, -96]], ![![15, -26, -125, -253, -258]], ![![9, -39, -135, -286, -294]], ![![2, -24, -68, -147, -151]]]
  g := ![![![-824, -1345, -927, 591, 1452], ![459, 748, 515, -327, -810], ![-267, -439, -304, 197, 468], ![-165, -264, -180, 110, 294], ![197, 318, 218, -136, -349]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 3 2 8 [23, 4, 211, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 77, 86], [35, 215, 207], [0, 1]]
 g := ![![[240, 276, 153], [194, 257], [12, 189, 209], [122, 88], [217, 96], [144, 162, 68], [82, 1], []], ![[176, 86, 107, 136], [68, 240], [214, 117, 70, 79], [232, 123], [174, 49], [146, 216, 282, 103], [53, 224], [21, 71]], ![[173, 199, 18, 155], [211, 77], [165, 89, 272, 75], [280, 196], [120, 153], [14, 253, 278, 66], [143, 69], [193, 71]]]
 h' := ![![[47, 77, 86], [222, 124, 175], [17, 140, 51], [124, 125, 217], [0, 171, 214], [204, 69, 125], [165, 235, 274], [0, 0, 1], [0, 1]], ![[35, 215, 207], [157, 33, 237], [277, 230, 151], [227, 229, 270], [17, 100, 65], [33, 149, 286], [98, 217, 10], [261, 247, 215], [47, 77, 86]], ![[0, 1], [277, 136, 174], [102, 216, 91], [6, 232, 99], [0, 22, 14], [228, 75, 175], [15, 134, 9], [9, 46, 77], [35, 215, 207]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [268, 47], []]
 b := ![[], [112, 197, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 3
  hpos := by decide
  P := [23, 4, 211, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![182703, 188296, -253440, 205224, 148616]
  a := ![10, 6, 0, 2, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-114949, -258976, -210728, 205224, 148616]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 25153757 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 10, 14, 31, 30]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![2, 10, 14, 31, 30]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![132, 120, 1, 0, 0], ![284, 45, 0, 1, 0], ![231, 142, 0, 0, 1]] where
  M :=![![![2, 10, 14, 31, 30], ![3, 19, 38, 91, 96], ![-15, 26, 125, 253, 258], ![-9, 38, 128, 330, 324], ![0, -2, 10, 12, 29]]]
  hmulB := by decide  
  f := ![![![-4568, 2990, 324, -591, -1452]], ![![2583, -1661, -184, 327, 810]], ![![-1005, 670, 71, -133, -324]], ![![-4034, 2645, 286, -523, -1284]], ![![-2346, 1550, 166, -307, -751]]]
  g := ![![![-60, -25, 14, 31, 30], ![-181, -76, 38, 91, 96], ![-505, -215, 125, 253, 258], ![-633, -260, 128, 330, 324], ![-39, -20, 10, 12, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P1 : CertificateIrreducibleZModOfList' 293 2 2 8 [112, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [201, 292], [0, 1]]
 g := ![![[95, 153], [96], [83, 17], [203], [247], [270, 10], [260], [1]], ![[83, 140], [96], [277, 276], [203], [247], [229, 283], [260], [1]]]
 h' := ![![[201, 292], [43, 175], [80, 168], [268, 137], [83, 221], [232, 213], [125, 204], [181, 201], [0, 1]], ![[0, 1], [58, 118], [153, 125], [263, 156], [261, 72], [267, 80], [109, 89], [148, 92], [201, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106]]
 b := ![[], [94, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N1 : CertifiedPrimeIdeal' SI293N1 293 where
  n := 2
  hpos := by decide
  P := [112, 92, 1]
  hirr := P293P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29, -16, 617, 264, 703]
  a := ![6, 6, -3, 5, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1088, -634, 617, 264, 703]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N1 B_one_repr
lemma NI293N1 : Nat.card (O ⧸ I293N1) = 85849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N1
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![4568, -2990, -324, 591, 1452]] ![![2, 10, 14, 31, 30]]
  ![![293, 0, 0, 0, 0]] where
 M := ![![![-293, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC293 : ContainsPrimesAboveP 293 ![I293N0, I293N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI293N0
    exact isPrimeI293N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 293 (by decide) (𝕀 ⊙ MulI293N0)
instance hp307 : Fact (Nat.Prime 307) := {out := by norm_num}

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![307, 0, 0, 0, 0]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![307, 0, 0, 0, 0]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![0, 0, 0, 307, 0], ![0, 0, 0, 0, 307]] where
  M :=![![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![0, 0, 0, 307, 0], ![0, 0, 0, 0, 307]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 5 2 8 [258, 72, 226, 151, 127, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [183, 29, 66, 62, 114], [42, 267, 102, 239, 237], [62, 185, 102, 283, 267], [200, 132, 37, 30, 303], [0, 1]]
 g := ![![[10, 126, 280, 216, 146], [249, 179, 275, 129, 289], [178, 106, 138, 49], [178, 287, 137, 104], [202, 255, 271, 47, 39], [71, 288, 14, 180, 1], [], []], ![[220, 130, 143, 9, 245, 15, 290, 165], [155, 242, 177, 246, 265, 268, 160, 287], [43, 93], [85, 81, 213, 64], [33, 82, 99, 182, 231, 93, 209, 294], [292, 147, 224, 127, 54, 88, 110, 81], [254, 23, 149, 110], [81, 122, 261, 102]], ![[213, 9, 88, 305, 22, 234, 18, 30], [82, 286, 295, 32, 251, 264, 280, 12], [261, 191, 202, 104], [107, 78, 159, 264], [146, 236, 152, 27, 60, 113, 159, 197], [184, 268, 77, 233, 159, 43, 16, 301], [116, 207, 196, 216], [134, 233, 299, 295]], ![[105, 182, 201, 132, 50, 237, 177, 126], [199, 232, 131, 229, 60, 61, 0, 221], [215, 163, 294, 164], [153, 299, 112, 273], [182, 142, 203, 23, 279, 217, 175, 95], [230, 180, 301, 15, 113, 103, 61, 123], [147, 268, 278, 36], [225, 305, 112, 65]], ![[90, 75, 69, 124, 87, 136, 120, 254], [49, 180, 28, 235, 0, 253, 85, 23], [57, 14, 236, 168], [203, 163, 29, 146], [195, 182, 115, 2, 21, 123, 213, 245], [120, 142, 262, 249, 269, 296, 110, 72], [224, 300, 222, 181], [305, 301, 184, 16]]]
 h' := ![![[183, 29, 66, 62, 114], [228, 209, 117, 228, 266], [69, 262, 212, 235, 290], [76, 270, 184, 257, 7], [74, 66, 62, 277, 59], [102, 97, 130, 157, 188], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[42, 267, 102, 239, 237], [231, 51, 231, 30, 66], [232, 209, 291, 14, 123], [46, 240, 26, 287], [250, 181, 19, 227, 299], [163, 158, 287, 207, 122], [182, 151, 264, 114, 273], [4, 15, 258, 246, 73], [183, 29, 66, 62, 114]], ![[62, 185, 102, 283, 267], [259, 80, 251, 27, 92], [299, 179, 279, 147, 101], [158, 147, 246, 261, 248], [21, 74, 129, 306, 195], [184, 197, 260, 283, 285], [304, 269, 296, 29, 72], [41, 251, 170, 105, 38], [42, 267, 102, 239, 237]], ![[200, 132, 37, 30, 303], [258, 183, 68, 33, 83], [276, 159, 198, 183, 204], [57, 191, 98, 294, 85], [34, 148, 207, 169, 102], [286, 42, 295, 249, 6], [25, 79, 42, 78, 251], [133, 195, 120, 46, 6], [62, 185, 102, 283, 267]], ![[0, 1], [192, 91, 254, 296, 107], [176, 112, 248, 35, 203], [41, 73, 60, 129, 274], [292, 145, 197, 249, 266], [296, 120, 256, 25, 13], [295, 115, 12, 86, 17], [299, 153, 65, 217, 190], [200, 132, 37, 30, 303]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 2, 188, 290], [], [], []]
 b := ![[], [50, 271, 2, 182, 19], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 5
  hpos := by decide
  P := [258, 72, 226, 151, 127, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![100730384, 126791000, -37363128, 303152062, 333738472]
  a := ![3, 4, 0, 5, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![328112, 413000, -121704, 987466, 1087096]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 2727042318307 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def PBC307 : ContainsPrimesAboveP 307 ![I307N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI307N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![307, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 307 (by decide) 𝕀



lemma PB402I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB402I6 : PrimesBelowBoundCertificateInterval O 251 307 402 where
  m := 9
  g := ![3, 3, 3, 1, 3, 2, 3, 2, 1]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB402I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1, I257N2]
    · exact ![I263N0, I263N1, I263N2]
    · exact ![I269N0, I269N1, I269N2]
    · exact ![I271N0]
    · exact ![I277N0, I277N1, I277N2]
    · exact ![I281N0, I281N1]
    · exact ![I283N0, I283N1, I283N2]
    · exact ![I293N0, I293N1]
    · exact ![I307N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC257
    · exact PBC263
    · exact PBC269
    · exact PBC271
    · exact PBC277
    · exact PBC281
    · exact PBC283
    · exact PBC293
    · exact PBC307
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![66049, 66049, 257]
    · exact ![18191447, 263, 263]
    · exact ![19465109, 269, 269]
    · exact ![1461660310351]
    · exact ![21253933, 277, 277]
    · exact ![6234839521, 281]
    · exact ![22665187, 283, 283]
    · exact ![25153757, 85849]
    · exact ![2727042318307]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
      exact NI257N2
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
      exact NI263N2
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
      exact NI269N2
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
      exact NI277N2
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
      exact NI281N1
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
      exact NI283N1
      exact NI283N2
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
  β := ![I257N2, I263N1, I263N2, I269N1, I269N2, I277N1, I277N2, I281N1, I283N1, I283N2]
  Il := ![[I257N2], [I263N1, I263N2], [I269N1, I269N2], [], [I277N1, I277N2], [I281N1], [I283N1, I283N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
