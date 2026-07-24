
import IdealArithmetic.Examples.NF5_1_72900000_2.RI5_1_72900000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0, 0, 0]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![0, 0, 0, 0, 67]] where
  M :=![![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![0, 0, 0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 5 2 6 [51, 41, 16, 13, 63, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 8, 13, 42, 23], [65, 30, 36, 65, 9], [42, 23, 40, 42, 63], [2, 5, 45, 52, 39], [0, 1]]
 g := ![![[6, 54, 40, 11, 60], [53, 45, 60, 63, 60], [39, 17, 64, 17], [11, 3, 4, 1], [], []], ![[25, 45, 38, 33, 34, 42, 49, 35], [13, 58, 30, 47, 45, 7, 57, 26], [31, 10, 19, 22], [46, 7, 15, 23], [30, 35, 12, 4], [11, 19, 28, 60]], ![[19, 61, 22, 32, 56, 21, 12, 64], [30, 50, 21, 24, 4, 65, 9, 26], [64, 44, 37, 40], [52, 19, 15, 10], [15, 21, 34, 9], [35, 14, 20, 14]], ![[66, 48, 56, 41, 49, 51, 46, 63], [39, 18, 66, 34, 11, 50, 26, 57], [4, 44, 26, 10], [55, 53, 52, 40], [58, 22, 18, 25], [13, 14, 63, 16]], ![[40, 51, 50, 57, 10, 60, 8, 55], [48, 38, 32, 65, 1, 27, 12, 25], [58, 37, 2, 16], [6, 13, 1, 1], [42, 54], [66, 0, 23, 47]]]
 h' := ![![[29, 8, 13, 42, 23], [44, 61, 0, 46, 23], [43, 63, 64, 18, 23], [42, 66, 33, 63, 34], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[65, 30, 36, 65, 9], [0, 23, 36, 9, 32], [64, 58, 39, 14, 21], [38, 48, 46, 8, 25], [21, 37, 35, 65, 36], [12, 49, 43, 66, 2], [29, 8, 13, 42, 23]], ![[42, 23, 40, 42, 63], [8, 11, 28, 7, 25], [54, 54, 31, 51, 16], [54, 22, 1, 10, 24], [19, 24, 28, 15, 55], [28, 9, 9, 22, 3], [65, 30, 36, 65, 9]], ![[2, 5, 45, 52, 39], [55, 32, 18, 36, 66], [65, 44, 33, 62, 61], [1, 20, 40, 62, 55], [27, 50, 39, 19, 43], [29, 15, 28, 35, 62], [42, 23, 40, 42, 63]], ![[0, 1], [22, 7, 52, 36, 55], [37, 49, 34, 56, 13], [39, 45, 14, 58, 63], [12, 23, 32, 35, 66], [55, 61, 53, 11], [2, 5, 45, 52, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 66, 17, 61], [], [], []]
 b := ![[], [39, 47, 10, 8, 9], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 5
  hpos := by decide
  P := [51, 41, 16, 13, 63, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3211581505105, -4730008335043, -3270502758000, 3543808453361, -6985397282846]
  a := ![10, -11, -18, 14, -145]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-47934052315, -70597139329, -48813474000, 52892663483, -104259660938]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 1350125107 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-337, 275, -100, 43, -288]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-337, 275, -100, 43, -288]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![53, 22, 23, 1, 0], ![15, 8, 6, 0, 1]] where
  M :=![![![-337, 275, -100, 43, -288], ![-172, -453, 288, -70, 766], ![280, 314, -177, -58, 536], ![232, 584, 444, -365, -148], ![4, 49, 4, 25, -533]]]
  hmulB := by decide  
  f := ![![![-511795, -1625315, -1778280, 265407, -3921262]], ![![-1061628, -3371429, -3688728, 550540, -8133966]], ![![-2202160, -6993434, -7651615, 1141998, -16872476]], ![![-1488713, -4727729, -5172675, 772018, -11406198]], ![![-418523, -1329110, -1454198, 217038, -3206633]]]
  g := ![![![24, 23, 9, 43, -288], ![-112, -71, -38, -70, 766], ![-66, -38, -29, -58, 536], ![307, 138, 137, -365, -148], ![94, 53, 37, 25, -533]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [47, 19, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 64, 55], [9, 6, 16], [0, 1]]
 g := ![![[2, 21, 48], [43, 45, 20], [30, 17, 15], [26, 18], [57, 1], []], ![[12, 29, 15, 46], [42, 17, 13, 51], [54, 0, 29, 47], [60, 3], [43, 36], [48, 43]], ![[34, 32, 16, 19], [39, 56, 38, 3], [13, 13, 42, 57], [47, 49], [35, 49], [16, 43]]]
 h' := ![![[48, 64, 55], [38, 8, 30], [10, 61, 37], [62, 24, 21], [19, 6, 35], [0, 0, 1], [0, 1]], ![[9, 6, 16], [16, 69, 52], [28, 23, 27], [21, 26, 26], [70, 21, 43], [48, 16, 6], [48, 64, 55]], ![[0, 1], [2, 65, 60], [14, 58, 7], [32, 21, 24], [18, 44, 64], [39, 55, 64], [9, 6, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 33], []]
 b := ![[], [37, 70, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [47, 19, 14, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5815687, -1336936, 2164092, -3271530, 43359624]
  a := ![-9, -52, 17, -13, 132]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6800267, -3890708, -2573922, -3271530, 43359624]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![217, 222, 113, -109, -294]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![217, 222, 113, -109, -294]] 
 ![![71, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![217, 222, 113, -109, -294], ![436, -513, -835, 1061, -8086], ![-4244, -3406, -1172, 885, 13022], ![-3540, 12318, 15811, -19504, 129462], ![1476, 2562, 1933, -2147, 6247]]]
  hmulB := by decide  
  f := ![![![-867897, -2755810, -3015357, 450051, -6649138]], ![![-147594, -468661, -512791, 76535, -1130750]], ![![-565994, -1797214, -1966470, 293501, -4336246]], ![![-182438, -579334, -633873, 94606, -1397746]], ![![-81278, -258082, -282387, 42147, -622689]]]
  g := ![![![-61, 222, 113, -109, -294], ![1166, -513, -835, 1061, -8086], ![-62, -3406, -1172, 885, 13022], ![-20430, 12318, 15811, -19504, 129462], ![-1830, 2562, 1933, -2147, 6247]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3621, -1057, 1065, -1736, 25766]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-3621, -1057, 1065, -1736, 25766]] 
 ![![71, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![-3621, -1057, 1065, -1736, 25766], ![6944, 15201, 12557, -14285, 53908], ![57140, 3712, -30886, 44359, -505082], ![-177436, -270506, -190857, 208042, -457670], ![-40328, -26155, -4255, 112, 172369]]]
  hmulB := by decide  
  f := ![![![-492214523055, -1563133404539, -1710246330377, 255253030452, -3771241856828]], ![![-277819211238, -882274839867, -965309360599, 144071725365, -2128591069496]], ![![-355661858571, -1129480959647, -1235781066963, 184439432329, -2725004698346]], ![![-477832400560, -1517459871866, -1660274273339, 247794737006, -3661049126210]], ![![-302601946775, -960977763002, -1051419340138, 156923577662, -2318471061261]]]
  g := ![![![-14328, -1057, 1065, -1736, 25766], ![-36927, 15201, 12557, -14285, 53908], ![287672, 3712, -30886, 44359, -505082], ![369991, -270506, -190857, 208042, -457670], ![-88240, -26155, -4255, 112, 172369]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-337, 275, -100, 43, -288]] ![![217, 222, 113, -109, -294]]
  ![![-106137, -83471, -27337, 19672, 340958]] where
 M := ![![![-106137, -83471, -27337, 19672, 340958]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-106137, -83471, -27337, 19672, 340958]] ![![-3621, -1057, 1065, -1736, 25766]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![-18998011943, -15497281328, -5522165864, 4294784604, 56340251286]]]
 hmul := by decide  
 g := ![![![![-267577633, -218271568, -77776984, 60489924, 793524666]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 11, 9, -2, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![7, 11, 9, -2, 0]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![33, 31, 32, 1, 0], ![38, 61, 14, 0, 1]] where
  M :=![![![7, 11, 9, -2, 0], ![8, -1, -3, 21, -116], ![-84, -24, 30, -13, 522], ![52, 386, 407, -414, 2378], ![44, 57, 37, -34, 23]]]
  hmulB := by decide  
  f := ![![![-189, 47, 17, -2, 58]], ![![8, -139, 91, -29, 232]], ![![116, 124, -110, 33, -290]], ![![-33, 16, -1, 1, 0]], ![![-70, -68, 64, -19, 169]]]
  g := ![![![1, 1, 1, -2, 0], ![51, 88, 13, 21, -116], ![-267, -431, -94, -13, 522], ![-1050, -1806, -269, -414, 2378], ![4, -4, 11, -34, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [4, 70, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 8], [51, 64], [0, 1]]
 g := ![![[29, 37, 65], [22, 16], [59, 46], [35, 48, 36], [8, 1], []], ![[71, 33, 72], [64, 55], [52, 3], [3, 71, 41], [38, 8], []], ![[15, 3, 9], [35, 2], [69, 24], [51, 27, 69], [59, 64], []]]
 h' := ![![[30, 8], [54, 31, 24], [19, 68, 69], [6, 61, 22], [41, 20, 67], [0, 0, 1], [0, 1]], ![[51, 64], [27, 15, 3], [65, 11, 36], [28, 25, 21], [59, 54, 54], [24, 42, 64], [30, 8]], ![[0, 1], [38, 27, 46], [18, 67, 41], [41, 60, 30], [55, 72, 25], [46, 31, 8], [51, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19], []]
 b := ![[], [34, 11, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [4, 70, 65, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3368, -151864, -169260, 207582, -1224322]
  a := ![3, -5, -5, 4, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![543526, 932832, 141488, 207582, -1224322]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-189, 47, 17, -2, 58]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-189, 47, 17, -2, 58]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![59, 41, 1, 0, 0], ![63, 57, 0, 1, 0], ![37, 26, 0, 0, 1]] where
  M :=![![![-189, 47, 17, -2, 58], ![8, -139, 91, -29, 232], ![116, 124, -110, 33, -290], ![-132, -42, 65, -18, 174], ![-40, -7, 15, -4, 41]]]
  hmulB := by decide  
  f := ![![![7, 11, 9, -2, 0]], ![![8, -1, -3, 21, -116]], ![![9, 8, 6, 10, -58]], ![![13, 14, 11, 9, -58]], ![![7, 6, 4, 6, -41]]]
  g := ![![![-44, -28, 17, -2, 58], ![-166, -113, 91, -29, 232], ![209, 141, -110, 33, -290], ![-127, -85, 65, -18, 174], ![-30, -20, 15, -4, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [2, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 72], [0, 1]]
 g := ![![[43, 37], [4], [48], [44, 54], [23], [1]], ![[0, 36], [4], [48], [72, 19], [23], [1]]]
 h' := ![![[60, 72], [62, 16], [56, 71], [58, 62], [31, 45], [71, 60], [0, 1]], ![[0, 1], [0, 57], [9, 2], [55, 11], [30, 28], [21, 13], [60, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [4, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [2, 13, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2360, 23725, 28184, -32025, 202186]
  a := ![-15, 35, 27, -23, 218]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-97651, -62510, 28184, -32025, 202186]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![7, 11, 9, -2, 0]] ![![-189, 47, 17, -2, 58]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0, 0, 0]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]] where
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [17, 45, 67, 9, 28, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 14, 3, 35, 5], [45, 14, 36, 72, 64], [42, 49, 53, 48, 56], [20, 1, 66, 3, 33], [0, 1]]
 g := ![![[73, 63, 22, 29, 51], [70, 43, 73, 50, 67], [50, 35, 33, 75, 8], [36, 52, 64, 51, 1], [], []], ![[14, 6, 56, 27, 28, 60, 46, 76], [65, 77, 58, 2, 47, 69, 20, 21], [9, 13, 18, 22, 45, 46, 2, 36], [53, 52, 10, 0, 64, 12, 0, 55], [70, 5, 5, 42], [49, 7, 45, 25]], ![[2, 50, 76, 76, 62, 9, 67, 40], [60, 48, 74, 75, 42, 5, 20, 44], [8, 47, 5, 17, 63, 69, 8, 9], [25, 76, 25, 56, 9, 62, 74, 76], [3, 7, 67, 65], [75, 63, 72, 67]], ![[77, 47, 64, 11, 25, 39, 44, 57], [76, 3, 35, 49, 41, 30, 56, 56], [17, 39, 69, 49, 48, 72, 4, 6], [32, 10, 67, 11, 15, 49, 24, 69], [47, 45, 63, 44], [64, 35, 44, 55]], ![[66, 19, 33, 9, 16, 52, 72, 7], [35, 67, 73, 53, 41, 54], [61, 48, 17, 42, 44, 53, 65, 63], [73, 65, 70, 19, 27, 1, 34, 74], [70, 0, 2, 9], [77, 24, 42, 62]]]
 h' := ![![[23, 14, 3, 35, 5], [74, 35, 28, 28, 50], [19, 4, 56, 1, 15], [20, 24, 6, 29, 61], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[45, 14, 36, 72, 64], [9, 17, 68, 73, 49], [60, 50, 24, 29, 40], [55, 19, 34, 37, 55], [60, 53, 23, 61, 66], [12, 58, 0, 72, 68], [23, 14, 3, 35, 5]], ![[42, 49, 53, 48, 56], [69, 26, 16, 39, 34], [44, 77, 24, 14, 23], [2, 68, 61, 74, 49], [48, 9, 8, 68, 75], [39, 53, 40, 30, 67], [45, 14, 36, 72, 64]], ![[20, 1, 66, 3, 33], [37, 23, 39, 29, 5], [37, 12, 48, 31, 1], [2, 77, 73, 54, 12], [31, 45, 43, 37, 32], [44, 9, 5, 72, 26], [42, 49, 53, 48, 56]], ![[0, 1], [8, 57, 7, 68, 20], [11, 15, 6, 4], [20, 49, 63, 43, 60], [15, 51, 5, 71, 63], [39, 38, 33, 63, 76], [20, 1, 66, 3, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 52, 7, 22], [], [], []]
 b := ![[], [48, 24, 36, 1, 43], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [17, 45, 67, 9, 28, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-154486793258215, -95799288577816, -11436761684276, -5429548347268, 694578507897282]
  a := ![19, -20, -33, 30, -276]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1955529028585, -1212649222504, -144769135244, -68728460092, 8792133011358]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 3077056399 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀

instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -4, -4, 4, -22]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-1, -4, -4, 4, -22]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![35, 27, 1, 0, 0], ![51, 53, 0, 1, 0], ![52, 20, 0, 0, 1]] where
  M :=![![![-1, -4, -4, 4, -22], ![-16, -7, 2, -6, 100], ![24, 60, 51, -62, 252], ![248, 28, -122, 171, -2084], ![12, -24, -34, 42, -299]]]
  hmulB := by decide  
  f := ![![![-331, 132, -8, 8, 6]], ![![-32, -293, 194, -62, 500]], ![![-147, -37, 57, -16, 158]], ![![-227, -107, 120, -35, 326]], ![![-216, 12, 42, -10, 125]]]
  g := ![![![13, 4, -4, 4, -22], ![-60, -21, 2, -6, 100], ![-141, -37, 51, -62, 252], ![1255, 433, -122, 171, -2084], ![176, 56, -34, 42, -299]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [82, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 82], [0, 1]]
 g := ![![[14, 4], [52, 37], [68], [25], [33, 30], [1]], ![[70, 79], [72, 46], [68], [25], [38, 53], [1]]]
 h' := ![![[14, 82], [52, 81], [48, 28], [35, 20], [33, 78], [1, 14], [0, 1]], ![[0, 1], [24, 2], [25, 55], [66, 63], [46, 5], [31, 69], [14, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [59, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [82, 69, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26670, 29956, 16950, -17032, -16646]
  a := ![-12, 12, 22, -28, 174]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14068, 9734, 16950, -17032, -16646]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5302131971, -16838063915, -18422763494, 2749584155, -40623795282]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-5302131971, -16838063915, -18422763494, 2749584155, -40623795282]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![78, 81, 1, 0, 0], ![73, 74, 0, 1, 0], ![76, 59, 0, 0, 1]] where
  M :=![![![-5302131971, -16838063915, -18422763494, 2749584155, -40623795282], ![-10998336620, -34927590633, -38214770112, 5703526858, -84266890702], ![-22814107432, -72451119890, -79269793329, 11830959442, -174796786448], ![-47323837768, -150287056112, -164431190244, 24541236467, -362585071052], ![-3441800032, -10930178509, -11958862648, 1784851619, -26370331909]]]
  hmulB := by decide  
  f := ![![![-1445, -1225, 1650, -789, 6052]], ![![3156, 1451, -696, 332, -9450]], ![![1706, 205, 803, -336, -3986]], ![![1217, 75, 890, -504, -1084]], ![![892, -78, 1052, -531, -797]]]
  g := ![![![52028460466, 44201692449, -18422763494, 2749584155, -40623795282], ![107923854998, 91688606655, -38214770112, 5703526858, -84266890702], ![223868981964, 190191825801, -79269793329, 11830959442, -174796786448], ![464376676375, 394519362014, -164431190244, 24541236467, -362585071052], ![33773500523, 28692870588, -11958862648, 1784851619, -26370331909]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [10, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 82], [0, 1]]
 g := ![![[60, 25], [51, 10], [63], [61], [78, 29], [1]], ![[0, 58], [27, 73], [63], [61], [25, 54], [1]]]
 h' := ![![[64, 82], [71, 78], [63, 50], [64, 48], [50, 71], [73, 64], [0, 1]], ![[0, 1], [0, 5], [26, 33], [65, 35], [29, 12], [19, 19], [64, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [47, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [10, 19, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5266, 851, -2146, 5295, -48426]
  a := ![1, 11, 2, 9, -8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![41765, 31807, -2146, 5295, -48426]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5034344953, 15987648469, 17492311946, -2610714933, 38572068720]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![5034344953, 15987648469, 17492311946, -2610714933, 38572068720]] 
 ![![83, 0, 0, 0, 0], ![58, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![62, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![5034344953, 15987648469, 17492311946, -2610714933, 38572068720], ![10442859732, 33163553941, 36284712658, -5415467176, 80010946206], ![21661868704, 68791937234, 75266229915, -11233430492, 165968581028], ![44933721968, 142696727764, 156126504818, -23301768161, 344272517632], ![3267970076, 10378143983, 11354873878, -1694706731, 25038484157]]]
  hmulB := by decide  
  f := ![![![-8281, -6857, 6518, -2173, 21342]], ![![-5682, -4739, 4546, -1540, 14938]], ![![-3805, -3179, 2989, -925, 8926]], ![![-6570, -5754, 4482, -1171, 14900]], ![![-6381, -5278, 4948, -1650, 16585]]]
  g := ![![![-46658137779, 15987648469, 17492311946, -2610714933, 38572068720], ![-96784068778, 33163553941, 36284712658, -5415467176, 80010946206], ![-200761462311, 68791937234, 75266229915, -11233430492, 165968581028], ![-416444206760, 142696727764, 156126504818, -23301768161, 344272517632], ![-30287435503, 10378143983, 11354873878, -1694706731, 25038484157]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-1, -4, -4, 4, -22]] ![![-5302131971, -16838063915, -18422763494, 2749584155, -40623795282]]
  ![![26976157811, 85668608757, 93731234538, -13989319105, 206685521672]] where
 M := ![![![26976157811, 85668608757, 93731234538, -13989319105, 206685521672]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![26976157811, 85668608757, 93731234538, -13989319105, 206685521672]] ![![5034344953, 15987648469, 17492311946, -2610714933, 38572068720]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![3107676169418908238191, 9869096102076733758944, 10797917403393674596708, -1611581379144061442918, 23810346705591034634070]]]
 hmul := by decide  
 g := ![![![![37441881559263954677, 118904772314177515168, 130095390402333428876, -19416643122217607746, 286871647055313670290]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0, 0, 0]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]] where
  M :=![![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 5 2 6 [74, 38, 38, 4, 18, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 41, 34, 42, 19], [17, 34, 73, 51, 66], [24, 8, 11, 75, 67], [65, 5, 60, 10, 26], [0, 1]]
 g := ![![[57, 41, 17, 4, 17], [68, 16, 53, 21], [46, 25, 28, 47], [76, 37, 33, 8, 57], [1], []], ![[29, 69, 50, 60, 18, 58, 43, 58], [69, 87, 80, 85], [64, 8, 22, 69], [37, 46, 11, 25, 21, 20, 41, 63], [86, 15, 67, 8, 58, 84, 35, 43], [24, 47, 82, 5]], ![[70, 32, 29, 18, 31, 44, 33, 60], [68, 78, 37, 85], [37, 39, 31, 44], [15, 44, 52, 28, 43, 17, 50, 65], [62, 82, 52, 27, 71, 87, 2, 27], [73, 88, 58, 84]], ![[44, 55, 53, 14, 14, 25, 72, 67], [50, 28, 61, 42], [80, 5, 81, 71], [87, 28, 18, 47, 61, 2, 67, 22], [35, 79, 18, 77, 36, 72, 35, 8], [46, 36, 3, 39]], ![[36, 31, 87, 7, 65, 84, 75, 65], [3, 8, 42, 11], [39, 31, 62, 8], [74, 31, 58, 58, 73, 11, 69, 59], [83, 41, 44, 64, 56, 17, 21, 7], [86, 51, 11, 53]]]
 h' := ![![[54, 41, 34, 42, 19], [41, 59, 38, 47, 62], [0, 78, 2, 78, 33], [72, 28, 45, 41, 15], [15, 51, 51, 85, 71], [0, 0, 1], [0, 1]], ![[17, 34, 73, 51, 66], [57, 38, 55, 51, 16], [88, 79, 17, 68, 21], [14, 25, 7, 6, 46], [75, 3, 2, 73, 50], [72, 38, 58, 87, 56], [54, 41, 34, 42, 19]], ![[24, 8, 11, 75, 67], [9, 22, 79, 86, 86], [71, 59, 72, 14, 21], [36, 32, 81, 5, 20], [6, 26, 77, 87, 11], [49, 58, 81, 71, 63], [17, 34, 73, 51, 66]], ![[65, 5, 60, 10, 26], [4, 39, 18, 86, 88], [77, 22, 49, 30, 24], [52, 33, 65, 80, 58], [68, 21, 87, 5, 55], [20, 66, 13, 25, 11], [24, 8, 11, 75, 67]], ![[0, 1], [44, 20, 77, 86, 15], [34, 29, 38, 77, 79], [28, 60, 69, 46, 39], [50, 77, 50, 17, 80], [86, 16, 25, 84, 48], [65, 5, 60, 10, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 33, 3], [], [], []]
 b := ![[], [28, 15, 15, 42], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 5
  hpos := by decide
  P := [74, 38, 38, 4, 18, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![157400537307, -32500622081, -132436045139, 179263348859, -1725586918696]
  a := ![-5, 1, 9, -9, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1768545363, -365175529, -1488045451, 2014194931, -19388617064]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 5584059449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, -109, -120, 17, -260]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-35, -109, -120, 17, -260]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![77, 72, 0, 1, 0], ![38, 54, 90, 0, 1]] where
  M :=![![![-35, -109, -120, 17, -260], ![-68, -227, -250, 38, -574], ![-152, -490, -535, 96, -1240], ![-384, -1008, -1058, 129, -1872], ![-28, -67, -70, 1, -87]]]
  hmulB := by decide  
  f := ![![![-167, -69, 88, -25, 238]], ![![100, -29, -6, 0, -22]], ![![0, 78, -51, 16, -132]], ![![-59, -77, 66, -20, 174]], ![![-10, 29, -16, 5, -41]]]
  g := ![![![88, 131, 240, 17, -260], ![194, 289, 530, 38, -574], ![408, 614, 1145, 96, -1240], ![627, 936, 1726, 129, -1872], ![33, 47, 80, 1, -87]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [50, 29, 91, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 96, 29], [48, 0, 68], [0, 1]]
 g := ![![[28, 88, 86], [58, 33], [52, 33], [21, 6], [62, 36], [1]], ![[27, 6, 22, 60], [14, 25], [68, 94], [72, 88], [6, 54], [23, 42, 57, 42]], ![[75, 83, 64, 46], [68, 72], [26, 64], [29, 47], [32, 86], [75, 45, 39, 55]]]
 h' := ![![[55, 96, 29], [19, 72, 59], [94, 47, 79], [50, 66, 18], [79, 78, 54], [47, 68, 6], [0, 1]], ![[48, 0, 68], [6, 33, 51], [67, 64, 5], [84, 17, 71], [80, 74, 31], [34, 89, 32], [55, 96, 29]], ![[0, 1], [39, 89, 84], [23, 83, 13], [16, 14, 8], [37, 42, 12], [45, 37, 59], [48, 0, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 51], []]
 b := ![[], [29, 40, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [50, 29, 91, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27904559, 46478376, 34403676, -37831432, 102404160]
  a := ![-17, 20, 34, -28, 248]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9798281, -28448280, -94659492, -37831432, 102404160]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 69, -88, 25, -238]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![167, 69, -88, 25, -238]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![40, 0, 1, 0, 0], ![0, 40, 0, 1, 0], ![11, 41, 0, 0, 1]] where
  M :=![![![167, 69, -88, 25, -238], ![-100, 29, 6, 0, 22], ![0, -78, 51, -16, 132], ![64, 68, -58, 15, -136], ![24, 19, -18, 5, -47]]]
  hmulB := by decide  
  f := ![![![35, 109, 120, -17, 260]], ![![68, 227, 250, -38, 574]], ![![16, 50, 55, -8, 120]], ![![32, 104, 114, -17, 256]], ![![33, 109, 120, -18, 273]]]
  g := ![![![65, 91, -88, 25, -238], ![-6, -9, 6, 0, 22], ![-36, -50, 51, -16, 132], ![40, 52, -58, 15, -136], ![13, 18, -18, 5, -47]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [74, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 96], [0, 1]]
 g := ![![[92, 73], [75], [75], [16], [32], [79, 1]], ![[39, 24], [75], [75], [16], [32], [61, 96]]]
 h' := ![![[79, 96], [49, 48], [78, 50], [83, 47], [54, 4], [71, 56], [0, 1]], ![[0, 1], [58, 49], [51, 47], [13, 50], [79, 93], [33, 41], [79, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [34, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [74, 18, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2963, 11120, 14211, -16992, 113792]
  a := ![-11, 13, 19, -17, 160]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18795, -40976, 14211, -16992, 113792]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-35, -109, -120, 17, -260]] ![![167, 69, -88, 25, -238]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![-97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4270037031801, -13560423779086, -14836651138708, 2214359474210, -32716105741954]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-4270037031801, -13560423779086, -14836651138708, 2214359474210, -32716105741954]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![94, 57, 76, 21, 1]] where
  M :=![![![-4270037031801, -13560423779086, -14836651138708, 2214359474210, -32716105741954], ![-8857437896840, -28128704876915, -30776013201570, 4593297757986, -67863784947544], ![-18373191031944, -58348031812440, -63839405518557, 9527985198058, -140771439722076], ![-38111940792232, -121032689961788, -132423575148110, 19764123015171, -292005496845092], ![-2771830967764, -8802547211534, -9630991201862, 1437418485784, -21237172972143]]]
  hmulB := by decide  
  f := ![![![-129509, -7122, 71464, -102278, 1154862]], ![![409112, 616241, 431794, -469730, 997048]], ![![1878920, -472760, -1674821, 2253126, -21262052]], ![![-9012504, -10370628, -5962930, 6068475, 3108996]], ![![-365682, -2178205, -2188222, 2592909, -13623263]]]
  g := ![![![30406375274375, 18329283203092, 24471162230196, 6824282970844, -32716105741954], ![63072656902696, 38020861753793, 50761105374374, 14155770115410, -67863784947544], ![130833090523200, 78867564676692, 105294950627319, 29363645736254, -140771439722076], ![271390146164816, 163596837922856, 218415784010682, 60909698581803, -292005496845092], ![19737845825878, 11898181308917, 15885090640406, 4429881692087, -21237172972143]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 4 2 6 [75, 88, 80, 13, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 83, 68, 24], [46, 19, 79, 79], [95, 99, 55, 99], [0, 1]]
 g := ![![[64, 77], [74, 10, 100], [50, 1, 32, 33], [3, 31, 9], [89, 88, 1], []], ![[71, 54, 6, 74, 86, 56], [59, 56, 78], [8, 78, 74, 81, 18, 71], [36, 2, 54], [0, 90, 65], [32, 70, 19, 63, 8, 88]], ![[71, 63, 49, 29, 58, 21], [49, 27, 95], [91, 42, 63, 49, 7, 56], [43, 91, 47], [15, 39, 37], [70, 49, 46, 59, 26, 58]], ![[15, 30, 75, 50, 42, 27], [83, 88, 77], [39, 50, 55, 53, 59, 26], [96, 8, 96], [9, 75, 58], [96, 92, 69, 6, 57, 93]]]
 h' := ![![[48, 83, 68, 24], [73, 10, 28], [88, 0, 86, 91], [58, 41, 53, 72], [92, 11, 9, 98], [0, 0, 0, 1], [0, 1]], ![[46, 19, 79, 79], [35, 99, 82, 6], [4, 88, 20, 52], [83, 78, 60, 78], [37, 65, 22, 16], [21, 30, 12, 60], [48, 83, 68, 24]], ![[95, 99, 55, 99], [63, 88, 46, 74], [1, 31, 92, 87], [12, 91, 24, 5], [56, 27, 30, 42], [75, 81, 22, 21], [46, 19, 79, 79]], ![[0, 1], [41, 5, 46, 21], [99, 83, 4, 73], [1, 93, 65, 47], [63, 99, 40, 46], [58, 91, 67, 19], [95, 99, 55, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [90, 57, 74], []]
 b := ![[], [], [97, 68, 20, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 4
  hpos := by decide
  P := [75, 88, 80, 13, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20039479, -64311980, -83331535, 104025147, -692811198]
  a := ![-2, 6, 4, 0, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![644992991, 390355706, 520498213, 145079805, -692811198]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 104060401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5033, -17786, 13084, -4072, 33850]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-5033, -17786, 13084, -4072, 33850]] 
 ![![101, 0, 0, 0, 0], ![89, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![90, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![-5033, -17786, 13084, -4072, 33850], ![16288, 12529, -12440, 3666, -33076], ![-14664, -2124, 5115, -1360, 14172], ![5440, -5932, 2528, -897, 6152], ![924, -2310, 1300, -432, 3281]]]
  hmulB := by decide  
  f := ![![![-7040508389, -22358653254, -24462918244, 3651072892, -53942861670]], ![![-6348609289, -20161378397, -22058848796, 3292267262, -48641679514]], ![![-4343005058, -13792149488, -15090185509, 2252199296, -33275171072]], ![![-6895894650, -21899401128, -23960444008, 3576078975, -52834862292]], ![![-4227730144, -13426069130, -14689651820, 2192419932, -32391959463]]]
  g := ![![![-8371, -17786, 13084, -4072, 33850], ![12647, 12529, -12440, 3666, -33076], ![-8418, -2124, 5115, -1360, 14172], ![974, -5932, 2528, -897, 6152], ![-266, -2310, 1300, -432, 3281]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-4270037031801, -13560423779086, -14836651138708, 2214359474210, -32716105741954]] ![![-5033, -17786, 13084, -4072, 33850]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-547319, 959904, -483184, 165034, -1196244]]]
 hmul := by decide  
 g := ![![![![-5419, 9504, -4784, 1634, -11844]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-119571, -379837, -415636, 62037, -916526]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-119571, -379837, -415636, 62037, -916526]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![20, 56, 1, 0, 0], ![13, 77, 0, 1, 0], ![54, 71, 0, 0, 1]] where
  M :=![![![-119571, -379837, -415636, 62037, -916526], ![-248148, -787949, -862104, 128668, -1901010], ![-514672, -1634486, -1788283, 266898, -3943316], ![-1067592, -3390396, -3709516, 553645, -8179812], ![-77640, -246575, -269792, 40267, -594917]]]
  hmulB := by decide  
  f := ![![![351, 1173, 1088, -1267, 5920]], ![![5068, 1203, -1776, 2770, -37966]], ![![2716, 670, -923, 1450, -20144]], ![![3073, 1048, -724, 1254, -20526]], ![![3654, 1534, -540, 1105, -22145]]]
  g := ![![![552224, 807692, -415636, 62037, -916526], ![1145396, 1675283, -862104, 128668, -1901010], ![2375926, 3475084, -1788283, 266898, -3943316], ![4928497, 7208529, -3709516, 553645, -8179812], ![358449, 524275, -269792, 40267, -594917]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [22, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 102], [0, 1]]
 g := ![![[31, 100], [83, 9], [27, 4], [82], [56], [39, 1]], ![[17, 3], [22, 94], [80, 99], [82], [56], [78, 102]]]
 h' := ![![[39, 102], [28, 10], [24, 3], [58, 101], [27, 59], [69, 57], [0, 1]], ![[0, 1], [6, 93], [38, 100], [83, 2], [62, 44], [26, 46], [39, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [30, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [22, 64, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8261, 128816, 146929, -175890, 1075386]
  a := ![39, -30, -79, 62, -562]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-570205, -688428, 146929, -175890, 1075386]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![327, 223, 42, -13, -1316]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![327, 223, 42, -13, -1316]] 
 ![![103, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![327, 223, 42, -13, -1316], ![52, -1041, -1184, 1436, -8650], ![-5744, -2854, 361, -1150, 31388], ![4600, 21044, 20484, -24127, 121628], ![2852, 3121, 1708, -1705, -2245]]]
  hmulB := by decide  
  f := ![![![-136675659, -434043023, -474892550, 70877367, -1047179354]], ![![-20002845, -63523348, -69501786, 10373091, -153257480]], ![![-54806697, -174050483, -190431073, 28421699, -419917070]], ![![-56959826, -180888210, -197912328, 29538271, -436413888]], ![![-14130850, -44875561, -49098980, 7327987, -108267519]]]
  g := ![![![92, 223, 42, -13, -1316], ![923, -1041, -1184, 1436, -8650], ![-2493, -2854, 361, -1150, 31388], ![-13814, 21044, 20484, -24127, 121628], ![-199, 3121, 1708, -1705, -2245]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1923, -6102, -6679, 997, -14728]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![-1923, -6102, -6679, 997, -14728]] 
 ![![103, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![94, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![-1923, -6102, -6679, 997, -14728], ![-3988, -12663, -13851, 2067, -30542], ![-8268, -26262, -28736, 4289, -63366], ![-17156, -54478, -59605, 8896, -131434], ![-1248, -3962, -4335, 647, -9559]]]
  hmulB := by decide  
  f := ![![![-157, -46, 59, -63, 864]], ![![-57, -13, 26, -28, 342]], ![![-20, -10, 4, -1, 50]], ![![-198, -122, -1, 2, 674]], ![![-41, -16, 10, -12, 213]]]
  g := ![![![5655, -6102, -6679, 997, -14728], ![11731, -12663, -13851, 2067, -30542], ![24334, -26262, -28736, 4289, -63366], ![50476, -54478, -59605, 8896, -131434], ![3671, -3962, -4335, 647, -9559]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2

def I103N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -4, -3, 3, -4]] i)))

def SI103N3: IdealEqSpanCertificate' Table ![![-3, -4, -3, 3, -4]] 
 ![![103, 0, 0, 0, 0], ![98, 1, 0, 0, 0], ![78, 0, 1, 0, 0], ![81, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-3, -4, -3, 3, -4], ![-12, 5, 13, -17, 150], ![68, 70, 36, -35, -86], ![140, -158, -261, 332, -2546], ![-16, -44, -39, 45, -195]]]
  hmulB := by decide  
  f := ![![![-397, -876, -329, 7, -612]], ![![-378, -843, -327, 9, -614]], ![![-310, -686, -274, 9, -518]], ![![-327, -738, -310, 13, -594]], ![![-32, -72, -29, 1, -55]]]
  g := ![![![4, -4, -3, 3, -4], ![-13, 5, 13, -17, 150], ![-59, 70, 36, -35, -86], ![286, -158, -261, 332, -2546], ![51, -44, -39, 45, -195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N3 : Nat.card (O ⧸ I103N3) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N3)

lemma isPrimeI103N3 : Ideal.IsPrime I103N3 := prime_ideal_of_norm_prime hp103.out _ NI103N3
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-119571, -379837, -415636, 62037, -916526]] ![![327, 223, 42, -13, -1316]]
  ![![-9, 110, -70, 22, -176]] where
 M := ![![![-9, 110, -70, 22, -176]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-9, 110, -70, 22, -176]] ![![-1923, -6102, -6679, 997, -14728]]
  ![![-397, -876, -329, 7, -612]] where
 M := ![![![-397, -876, -329, 7, -612]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N2 : IdealMulLeCertificate' Table 
  ![![-397, -876, -329, 7, -612]] ![![-3, -4, -3, 3, -4]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2, I103N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
    exact isPrimeI103N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1 ⊙ MulI103N2)


lemma PB532I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB532I2 : PrimesBelowBoundCertificateInterval O 61 103 532 where
  m := 9
  g := ![1, 3, 2, 1, 3, 1, 2, 2, 4]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB532I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2, I103N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1350125107]
    · exact ![357911, 71, 71]
    · exact ![389017, 5329]
    · exact ![3077056399]
    · exact ![6889, 6889, 83]
    · exact ![5584059449]
    · exact ![912673, 9409]
    · exact ![104060401, 101]
    · exact ![10609, 103, 103, 103]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
      exact NI103N3
  β := ![I71N1, I71N2, I83N2, I101N1, I103N1, I103N2, I103N3]
  Il := ![[], [I71N1, I71N2], [], [], [I83N2], [], [], [I101N1], [I103N1, I103N2, I103N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
