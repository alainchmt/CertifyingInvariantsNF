
import IdealArithmetic.Examples.NF5_1_25000000_1.RI5_1_25000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59, 97, 389, 280, -599]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-59, 97, 389, 280, -599]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![57, 39, 1, 0, 0], ![162, 162, 0, 1, 0], ![165, 168, 0, 0, 1]] where
  M :=![![![-59, 97, 389, 280, -599], ![1836, -230, -245, 1354, 163], ![-3360, -1117, -6136, -8076, 9967], ![-4708, 2280, 7858, 2675, -11682], ![1136, 638, 3190, 3680, -5105]]]
  hmulB := by decide  
  f := ![![![-348905, 402533, 11647, 110494, -176317]], ![![484280, -558246, -16149, -153248, 244507]], ![![-8403, 9786, 284, 2684, -4289]], ![![112454, -129356, -3740, -35517, 56648]], ![![118973, -136863, -3957, -37578, 59936]]]
  g := ![![![157, 202, 389, 280, -599], ![-1158, -1193, -245, 1354, 163], ![51, -643, -6136, -8076, 9967], ![5234, 6156, 7858, 2675, -11682], ![329, 692, 3190, 3680, -5105]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [157, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 198], [0, 1]]
 g := ![![[135, 90], [106, 36], [6, 9], [187], [178], [80], [98, 1]], ![[0, 109], [52, 163], [92, 190], [187], [178], [80], [196, 198]]]
 h' := ![![[98, 198], [74, 182], [53, 193], [146, 196], [75, 171], [165, 175], [136, 94], [0, 1]], ![[0, 1], [0, 17], [62, 6], [51, 3], [117, 28], [2, 24], [194, 105], [98, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [71, 161]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [157, 101, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-35641, -3253, -22469, -47608, 39361]
  a := ![26, 17, 31, 30, -91]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![12377, 9914, -22469, -47608, 39361]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4847, 5588, 162, 1534, -2447]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-4847, 5588, 162, 1534, -2447]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![194, 124, 1, 0, 0], ![58, 73, 0, 1, 0], ![62, 174, 0, 0, 1]] where
  M :=![![![-4847, 5588, 162, 1534, -2447], ![6720, -7753, -224, -2128, 3397], ![-9332, 10752, 311, 2950, -4705], ![6216, -7168, -206, -1967, 3137], ![-1588, 1826, 54, 502, -799]]]
  hmulB := by decide  
  f := ![![![387, 154, -40, 28, -185]], ![![684, 291, -38, 70, -359]], ![![810, 334, -63, 72, -407]], ![![362, 151, -26, 33, -184]], ![![722, 304, -46, 70, -373]]]
  g := ![![![133, 1504, 162, 1534, -2447], ![-186, -2089, -224, -2128, 3397], ![256, 2892, 311, 2950, -4705], ![-172, -1929, -206, -1967, 3137], ![42, 490, 54, 502, -799]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P1 : CertificateIrreducibleZModOfList' 199 2 2 7 [131, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [125, 198], [0, 1]]
 g := ![![[75, 79], [40, 53], [94, 172], [155], [50], [187], [125, 1]], ![[0, 120], [98, 146], [102, 27], [155], [50], [187], [51, 198]]]
 h' := ![![[125, 198], [133, 26], [24, 124], [110, 42], [52, 126], [45, 100], [142, 171], [0, 1]], ![[0, 1], [0, 173], [2, 75], [186, 157], [81, 73], [8, 99], [25, 28], [125, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104]]
 b := ![[], [133, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N1 : CertifiedPrimeIdeal' SI199N1 199 where
  n := 2
  hpos := by decide
  P := [131, 74, 1]
  hirr := P199P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2295554, -819682, -2898761, -3890014, 5355582]
  a := ![239, 117, 236, 172, -835]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2279592, -1453636, -2898761, -3890014, 5355582]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N1 B_one_repr
lemma NI199N1 : Nat.card (O ⧸ I199N1) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-267, -67, 25, -14, 110]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![-267, -67, 25, -14, 110]] 
 ![![199, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![97, 0, 1, 0, 0], ![164, 0, 0, 1, 0], ![192, 0, 0, 0, 1]] where
  M :=![![![-267, -67, 25, -14, 110], ![-412, -214, 39, -50, 232], ![-828, -273, 64, -58, 346], ![200, 28, -20, 5, -73], ![-484, -192, 36, -42, 217]]]
  hmulB := by decide  
  f := ![![![643, 19, 333, 830, -598]], ![![120, 0, 47, 142, -88]], ![![249, 16, 165, 352, -288]], ![![584, 24, 332, 779, -589]], ![![652, 16, 324, 830, -585]]]
  g := ![![![-96, -67, 25, -14, 110], ![-165, -214, 39, -50, 232], ![-272, -273, 64, -58, 346], ![72, 28, -20, 5, -73], ![-160, -192, 36, -42, 217]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-59, 97, 389, 280, -599]] ![![-4847, 5588, 162, 1534, -2447]]
  ![![-643, -19, -333, -830, 598]] where
 M := ![![![-643, -19, -333, -830, 598]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![-643, -19, -333, -830, 598]] ![![-267, -67, 25, -14, 110]]
  ![![199, 0, 0, 0, 0]] where
 M := ![![![-199, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1, I199N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
    exact isPrimeI199N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0 ⊙ MulI199N1)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0, 0, 0]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![0, 0, 0, 211, 0], ![0, 0, 0, 0, 211]] where
  M :=![![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![0, 0, 0, 211, 0], ![0, 0, 0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 5 2 7 [135, 57, 21, 69, 81, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 196, 167, 55, 150], [139, 4, 184, 206, 7], [169, 65, 96, 181, 137], [196, 156, 186, 191, 128], [0, 1]]
 g := ![![[145, 20, 5, 176, 43], [133, 159, 206, 84, 45], [125, 105], [26, 53, 205, 93], [147, 137, 134, 43, 80], [130, 1], []], ![[99, 16, 142, 36, 54, 104, 178, 185], [56, 141, 142, 198, 206, 191, 87, 151], [188, 157, 124, 96], [30, 119, 66, 209], [90, 79, 0, 160, 122, 186, 169, 188], [116, 93, 109, 70], [173, 1, 206, 17, 14, 20, 142, 55]], ![[132, 106, 196, 76, 54, 67, 97, 92], [118, 141, 25, 150, 143, 150, 96, 85], [98, 134, 210, 71], [158, 157, 199, 45], [130, 191, 10, 132, 170, 142, 149, 18], [62, 6, 46, 134], [184, 92, 165, 56, 28, 38, 178, 132]], ![[78, 23, 82, 68, 50, 25, 117, 66], [114, 59, 154, 43, 0, 105, 101, 69], [106, 0, 78, 16], [60, 120, 107, 172], [90, 63, 21, 175, 192, 111, 78, 43], [196, 180, 26, 188], [140, 132, 170, 168, 93, 18, 40, 107]], ![[115, 193, 121, 124, 95, 176, 120, 35], [165, 124, 145, 48, 178, 119, 54, 28], [200, 1, 55, 180], [159, 190, 153, 96], [188, 178, 101, 118, 80, 189, 165, 124], [98, 146, 88, 47], [65, 200, 143, 11, 179, 99, 45, 23]]]
 h' := ![![[48, 196, 167, 55, 150], [191, 175, 8, 115, 26], [174, 171, 38, 44, 16], [198, 75, 184, 59], [200, 26, 156, 72, 127], [174, 51, 167, 82, 162], [0, 0, 0, 1], [0, 1]], ![[139, 4, 184, 206, 7], [0, 148, 156, 160, 95], [91, 49, 99, 59, 154], [183, 2, 87, 201, 27], [151, 40, 70, 122, 93], [139, 81, 41, 134, 74], [94, 53, 190, 77, 80], [48, 196, 167, 55, 150]], ![[169, 65, 96, 181, 137], [91, 117, 156, 117, 163], [3, 201, 127, 140, 68], [28, 189, 89, 82, 156], [141, 9, 52, 41, 16], [189, 154, 157, 159, 127], [69, 54, 173, 34, 61], [139, 4, 184, 206, 7]], ![[196, 156, 186, 191, 128], [6, 179, 41, 111, 143], [133, 176, 15, 175, 54], [112, 105, 183, 92, 207], [48, 67, 179, 5, 159], [86, 23, 106, 147, 109], [63, 203, 82, 59, 140], [169, 65, 96, 181, 137]], ![[0, 1], [81, 14, 61, 130, 206], [55, 36, 143, 4, 130], [70, 51, 90, 199, 32], [151, 69, 176, 182, 27], [0, 113, 162, 111, 161], [88, 112, 188, 40, 141], [196, 156, 186, 191, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [151, 41, 77, 18], [], [], []]
 b := ![[], [138, 147, 42, 207, 194], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 5
  hpos := by decide
  P := [135, 57, 21, 69, 81, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1965041260094, -1161734911049, -5763302152099, -6572282536326, 9216765650534]
  a := ![19, 11, 21, 18, -66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9312991754, -5505852659, -27314228209, -31148258466, 43681353794]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 418227202051 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀

instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![135, -19, -27, 92, 26]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![135, -19, -27, 92, 26]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![37, 50, 1, 0, 0], ![188, 140, 0, 1, 0], ![116, 79, 0, 0, 1]] where
  M :=![![![135, -19, -27, 92, 26], ![-288, -76, -441, -620, 722], ![-1648, 511, 1522, -108, -2174], ![3124, -214, 346, 2953, -913], ![924, -236, -636, 246, 881]]]
  hmulB := by decide  
  f := ![![![641, 1287, -47, 320, -858]], ![![2792, -46, -87, -72, -334]], ![![739, 216, -27, 40, -224]], ![![2292, 1050, -94, 223, -929]], ![![1328, 658, -55, 142, -567]]]
  g := ![![![-86, -61, -27, 92, 26], ![219, 232, -441, -620, 722], ![962, 499, 1522, -108, -2174], ![-2058, -1609, 346, 2953, -913], ![-556, -325, -636, 246, 881]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [206, 168, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 222], [0, 1]]
 g := ![![[200, 164], [113, 41], [149, 136], [28, 72], [85, 143], [156], [55, 1]], ![[77, 59], [138, 182], [47, 87], [197, 151], [145, 80], [156], [110, 222]]]
 h' := ![![[55, 222], [137, 155], [80, 34], [30, 164], [107, 90], [41, 139], [43, 143], [0, 1]], ![[0, 1], [188, 68], [166, 189], [130, 59], [151, 133], [104, 84], [103, 80], [55, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [177]]
 b := ![[], [75, 200]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [206, 168, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-88469, 7254, -10154, -84010, 22726]
  a := ![35, 28, 52, 60, -123]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![60291, 47000, -10154, -84010, 22726]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2095, 901, -145, 198, -953]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![2095, 901, -145, 198, -953]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![93, 42, 1, 0, 0], ![92, 119, 0, 1, 0], ![3, 45, 0, 0, 1]] where
  M :=![![![2095, 901, -145, 198, -953], ![3416, 1554, -181, 336, -1473], ![5220, 2563, -152, 542, -2067], ![-1668, -674, 144, -151, 800], ![2952, 1510, -46, 316, -1111]]]
  hmulB := by decide  
  f := ![![![101, -167, -19, -96, 101]], ![![-212, 274, 179, 202, -369]], ![![7, -20, 25, 0, -26]], ![![-76, 78, 85, 63, -151]], ![![-43, 53, 36, 38, -73]]]
  g := ![![![1, 118, -145, 198, -953], ![-28, 159, -181, 336, -1473], ![-109, 168, -152, 542, -2067], ![-16, -111, 144, -151, 800], ![-83, 71, -46, 316, -1111]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P1 : CertificateIrreducibleZModOfList' 223 2 2 7 [54, 166, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 222], [0, 1]]
 g := ![![[160, 115], [154, 69], [4, 28], [21, 39], [89, 33], [200], [57, 1]], ![[25, 108], [73, 154], [39, 195], [14, 184], [186, 190], [200], [114, 222]]]
 h' := ![![[57, 222], [158, 195], [7, 192], [204, 171], [100, 183], [56, 207], [44, 73], [0, 1]], ![[0, 1], [123, 28], [24, 31], [139, 52], [50, 40], [36, 16], [191, 150], [57, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [203]]
 b := ![[], [62, 213]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N1 : CertifiedPrimeIdeal' SI223N1 223 where
  n := 2
  hpos := by decide
  P := [54, 166, 1]
  hirr := P223P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-86714, 12112, 32328, -48088, -38500]
  a := ![-28, -30, -56, -78, 98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6486, 27396, 32328, -48088, -38500]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N1 B_one_repr
lemma NI223N1 : Nat.card (O ⧸ I223N1) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1257, 1450, 42, 398, -635]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![-1257, 1450, 42, 398, -635]] 
 ![![223, 0, 0, 0, 0], ![131, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-1257, 1450, 42, 398, -635], ![1744, -2011, -58, -552, 881], ![-2420, 2790, 81, 766, -1221], ![1612, -1860, -54, -511, 815], ![-412, 474, 14, 130, -207]]]
  hmulB := by decide  
  f := ![![![277, 160, 20, 36, -145]], ![![165, 95, 12, 22, -86]], ![![14, 8, -1, 0, -3]], ![![27, 18, 4, 3, -18]], ![![9, 6, 2, 2, -6]]]
  g := ![![![-884, 1450, 42, 398, -635], ![1226, -2011, -58, -552, 881], ![-1701, 2790, 81, 766, -1221], ![1134, -1860, -54, -511, 815], ![-289, 474, 14, 130, -207]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![135, -19, -27, 92, 26]] ![![2095, 901, -145, 198, -953]]
  ![![277, 160, 20, 36, -145]] where
 M := ![![![277, 160, 20, 36, -145]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![277, 160, 20, 36, -145]] ![![-1257, 1450, 42, 398, -635]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0, 0, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0, 0, 0]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![0, 0, 0, 227, 0], ![0, 0, 0, 0, 227]] where
  M :=![![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![0, 0, 0, 227, 0], ![0, 0, 0, 0, 227]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 5 2 7 [153, 177, 154, 92, 76, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 61, 12, 199, 151], [45, 35, 67, 102, 92], [29, 53, 176, 124, 158], [214, 77, 199, 29, 53], [0, 1]]
 g := ![![[173, 22, 150, 60, 169], [9, 12, 63, 212, 30], [172, 79, 144, 203], [10, 214, 198, 44], [108, 125, 81, 171], [9, 151, 1], []], ![[41, 137, 158, 65, 216, 53, 221, 164], [66, 107, 114, 27, 89, 74, 163, 60], [154, 138, 56, 21], [120, 172, 159, 205], [186, 91, 137, 7], [104, 85, 97, 215, 193, 0, 52, 107], [68, 225, 207, 10, 18, 156, 128, 42]], ![[56, 10, 137, 171, 38, 25, 135, 116], [111, 80, 99, 177, 148, 183, 194, 209], [116, 104, 89, 48], [111, 95, 53, 81], [115, 166, 147, 186], [96, 37, 99, 201, 222, 124, 81, 3], [159, 89, 151, 135, 170, 54, 115, 78]], ![[198, 105, 129, 209, 48, 147, 8, 39], [52, 126, 198, 47, 201, 171, 196, 15], [169, 7, 79, 141], [44, 71, 142, 64], [21, 70, 55, 19], [48, 202, 167, 99, 92, 99, 82, 137], [95, 67, 166, 151, 40, 102, 127, 187]], ![[140, 177, 165, 2, 16, 12, 214, 132], [95, 120, 93, 75, 212, 154, 213, 77], [87, 122, 211, 192], [132, 45, 65, 79], [84, 23, 160, 75], [82, 46, 47, 51, 33, 24, 194, 40], [190, 44, 182, 151, 202, 84, 67, 192]]]
 h' := ![![[90, 61, 12, 199, 151], [212, 63, 198, 45, 214], [108, 128, 210, 36, 22], [41, 69, 142, 164, 89], [45, 74, 226, 42, 80], [212, 47, 109, 30, 25], [0, 0, 0, 1], [0, 1]], ![[45, 35, 67, 102, 92], [191, 93, 137, 14, 125], [193, 34, 63, 110, 156], [104, 21, 22, 176, 193], [109, 86, 20, 149, 81], [54, 155, 73, 98, 37], [141, 64, 79, 121, 70], [90, 61, 12, 199, 151]], ![[29, 53, 176, 124, 158], [169, 218, 222, 143, 193], [134, 140, 87, 194, 62], [67, 107, 8, 162, 200], [5, 92, 42, 46, 218], [216, 52, 2, 129, 58], [60, 161, 124, 61, 32], [45, 35, 67, 102, 92]], ![[214, 77, 199, 29, 53], [12, 210, 147, 137, 73], [207, 118, 130, 155, 115], [58, 92, 13, 2, 145], [175, 145, 128, 56, 219], [133, 135, 164, 40, 84], [93, 190, 36, 222, 217], [29, 53, 176, 124, 158]], ![[0, 1], [218, 97, 204, 115, 76], [129, 34, 191, 186, 99], [71, 165, 42, 177, 54], [219, 57, 38, 161, 83], [86, 65, 106, 157, 23], [59, 39, 215, 49, 135], [214, 77, 199, 29, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [210, 56, 216, 87], [], [], []]
 b := ![[], [39, 56, 165, 149, 34], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 5
  hpos := by decide
  P := [153, 177, 154, 92, 76, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54930017152205, -7281216573926, -8972390249572, 39124098132670, 7411316812661]
  a := ![17, 23, 43, 61, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![241982454415, -32075843938, -39525948236, 172352855210, 32648972743]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 602738989907 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def PBC227 : ContainsPrimesAboveP 227 ![I227N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![227, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 227 (by decide) 𝕀

instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-94473, 108952, 3152, 29908, -47722]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-94473, 108952, 3152, 29908, -47722]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![175, 119, 1, 0, 0], ![145, 51, 0, 1, 0], ![106, 43, 0, 0, 1]] where
  M :=![![![-94473, 108952, 3152, 29908, -47722], ![131072, -151137, -4376, -41488, 66190], ![-181784, 209672, 6063, 57556, -91846], ![121192, -139760, -4044, -38365, 61214], ![-30872, 35628, 1028, 9780, -15613]]]
  hmulB := by decide  
  f := ![![![-205, -32, -56, -172, 146]], ![![-240, 83, 544, 344, -766]], ![![-271, 17, 239, 56, -286]], ![![-193, -3, 76, -49, -62]], ![![-146, 1, 76, -20, -75]]]
  g := ![![![331, 1138, 3152, 29908, -47722], ![-452, -1575, -4376, -41488, 66190], ![643, 2193, 6063, 57556, -91846], ![-423, -1459, -4044, -38365, 61214], ![114, 375, 1028, 9780, -15613]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [56, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [190, 228], [0, 1]]
 g := ![![[152, 45], [130], [180, 103], [25], [91], [104, 37], [190, 1]], ![[0, 184], [130], [56, 126], [25], [91], [35, 192], [151, 228]]]
 h' := ![![[190, 228], [64, 31], [225, 78], [27, 65], [125, 224], [130, 70], [123, 91], [0, 1]], ![[0, 1], [0, 198], [160, 151], [11, 164], [91, 5], [148, 159], [9, 138], [190, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [173, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [56, 39, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![484, 108, 2518, 2612, -3785]
  a := ![-1, -5, -8, -15, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1824, -1179, 2518, 2612, -3785]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-109, 125, 3, 34, -54]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![-109, 125, 3, 34, -54]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![35, 151, 1, 0, 0], ![207, 130, 0, 1, 0], ![41, 54, 0, 0, 1]] where
  M :=![![![-109, 125, 3, 34, -54], ![148, -174, -5, -50, 76], ![-204, 243, 16, 78, -122], ![148, -164, -16, -47, 87], ![-36, 40, -4, 6, -11]]]
  hmulB := by decide  
  f := ![![![-209, -111, 1, -22, 74]], ![![-252, -164, -21, -34, 68]], ![![-199, -126, -14, -26, 56]], ![![-331, -193, -11, -39, 105]], ![![-97, -59, -5, -12, 29]]]
  g := ![![![-22, -8, 3, 34, -54], ![33, 13, -5, -50, 76], ![-52, -25, 16, 78, -122], ![30, 16, -16, -47, 87], ![-3, 2, -4, 6, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P1 : CertificateIrreducibleZModOfList' 229 2 2 7 [184, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [175, 228], [0, 1]]
 g := ![![[182, 173], [192], [166, 20], [76], [103], [45, 27], [175, 1]], ![[0, 56], [192], [2, 209], [76], [103], [190, 202], [121, 228]]]
 h' := ![![[175, 228], [179, 33], [142, 110], [56, 97], [206, 63], [193, 65], [89, 213], [0, 1]], ![[0, 1], [0, 196], [156, 119], [85, 132], [10, 166], [118, 164], [37, 16], [175, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [217, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N1 : CertifiedPrimeIdeal' SI229N1 229 where
  n := 2
  hpos := by decide
  P := [184, 54, 1]
  hirr := P229P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-134569, -9332, -60357, -155134, 124026]
  a := ![-45, -32, -57, -62, 159]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![126662, 98579, -60357, -155134, 124026]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N1 B_one_repr
lemma NI229N1 : Nat.card (O ⧸ I229N1) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, -96, -2, -26, 41]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![83, -96, -2, -26, 41]] 
 ![![229, 0, 0, 0, 0], ![188, 1, 0, 0, 0], ![151, 0, 1, 0, 0], ![223, 0, 0, 1, 0], ![133, 0, 0, 0, 1]] where
  M :=![![![83, -96, -2, -26, 41], ![-112, 133, 4, 40, -59], ![156, -188, -19, -66, 103], ![-120, 128, 18, 35, -75], ![28, -30, 6, -2, 3]]]
  hmulB := by decide  
  f := ![![![5603, 1518, -976, 392, -3411]], ![![4656, 1263, -810, 326, -2833]], ![![3817, 1040, -661, 268, -2318]], ![![5445, 1476, -948, 381, -3314]], ![![3335, 908, -578, 234, -2026]]]
  g := ![![![82, -96, -2, -26, 41], ![-117, 133, 4, 40, -59], ![172, -188, -19, -66, 103], ![-108, 128, 18, 35, -75], ![21, -30, 6, -2, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-94473, 108952, 3152, 29908, -47722]] ![![-109, 125, 3, 34, -54]]
  ![![31923821, -36814629, -1065387, -10105834, 16124288]] where
 M := ![![![31923821, -36814629, -1065387, -10105834, 16124288]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![31923821, -36814629, -1065387, -10105834, 16124288]] ![![83, -96, -2, -26, 41]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![8270895363, -9538015109, -276023089, -2618241730, 4177515325]]]
 hmul := by decide  
 g := ![![![![36117447, -41650721, -1205341, -11433370, 18242425]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0, 0, 0]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![0, 0, 0, 233, 0], ![0, 0, 0, 0, 233]] where
  M :=![![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![0, 0, 0, 233, 0], ![0, 0, 0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 5 2 7 [204, 96, 120, 9, 187, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [130, 188, 149, 196, 184], [127, 98, 31, 140, 161], [85, 52, 133, 88, 170], [170, 127, 153, 42, 184], [0, 1]]
 g := ![![[125, 153, 161, 168, 135], [20, 141, 53, 207], [89, 51, 76, 9], [174, 30, 70, 220, 49], [34, 134, 119, 117], [10, 46, 1], []], ![[192, 27, 4, 3, 102, 85, 182, 46], [29, 16, 58, 55], [159, 196, 47, 29], [66, 30, 167, 192, 95, 120, 66, 113], [141, 196, 98, 112], [63, 137, 211, 102, 195, 109, 154, 7], [205, 54, 87, 60, 177, 67, 78, 16]], ![[130, 91, 126, 227, 194, 101, 207, 19], [135, 57, 126, 32], [231, 187, 115, 18], [143, 163, 146, 54, 59, 143, 163, 110], [88, 141, 21, 74], [27, 38, 138, 8, 7, 29, 192, 220], [168, 44, 144, 25, 227, 55, 24, 18]], ![[209, 68, 49, 102, 0, 64, 154, 144], [144, 119, 41, 110], [124, 102, 27, 29], [205, 80, 92, 29, 178, 53, 138, 19], [218, 97, 11, 2], [124, 225, 69, 38, 194, 62, 102, 218], [153, 210, 176, 130, 43, 97, 131, 195]], ![[104, 7, 140, 203, 90, 25, 110, 170], [123, 1, 182, 224], [198, 1, 194, 159], [128, 58, 155, 157, 16, 109, 88, 126], [46, 170, 10, 7], [58, 41, 230, 210, 203, 187, 205, 196], [115, 85, 133, 122, 145, 188, 129, 16]]]
 h' := ![![[130, 188, 149, 196, 184], [166, 73, 33, 204, 64], [127, 111, 156, 30, 48], [153, 60, 136, 134, 230], [41, 153, 201, 112, 226], [57, 141, 5, 119, 159], [0, 0, 0, 1], [0, 1]], ![[127, 98, 31, 140, 161], [150, 41, 107, 69, 117], [63, 224, 182, 166, 88], [47, 139, 190, 17, 202], [114, 176, 71, 16, 192], [174, 7, 191, 90, 47], [163, 96, 87, 187, 191], [130, 188, 149, 196, 184]], ![[85, 52, 133, 88, 170], [172, 188, 192, 165, 87], [43, 28, 78, 218, 107], [164, 184, 95, 138, 211], [230, 116, 162, 51, 218], [170, 44, 118, 218, 105], [59, 203, 98, 58, 123], [127, 98, 31, 140, 161]], ![[170, 127, 153, 42, 184], [199, 58, 95, 110, 168], [110, 40, 150, 143, 24], [3, 22, 159, 133, 31], [81, 44, 87, 180, 55], [41, 122, 163, 201, 85], [180, 102, 75, 84, 97], [85, 52, 133, 88, 170]], ![[0, 1], [43, 106, 39, 151, 30], [37, 63, 133, 142, 199], [179, 61, 119, 44, 25], [170, 210, 178, 107, 8], [232, 152, 222, 71, 70], [35, 65, 206, 136, 55], [170, 127, 153, 42, 184]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 30, 180, 191], [], [], []]
 b := ![[], [181, 212, 141, 111, 99], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 5
  hpos := by decide
  P := [204, 96, 120, 9, 187, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26866084730207, -1328928799873, 5162268496206, 27255335666781, -11259142951554]
  a := ![-23, -17, -32, -35, 81]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![115305084679, -5703557081, 22155658782, 116975689557, -48322501938]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 686719856393 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def PBC233 : ContainsPrimesAboveP 233 ![I233N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![233, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 233 (by decide) 𝕀

instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, 8, 22, -12, -29]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-37, 8, 22, -12, -29]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![109, 231, 1, 0, 0], ![44, 135, 0, 1, 0], ![74, 218, 0, 0, 1]] where
  M :=![![![-37, 8, 22, -12, -29], ![140, 9, 100, 206, -171], ![272, -172, -615, -288, 929], ![-956, 142, 220, -627, -229], ![-188, 82, 282, 82, -415]]]
  hmulB := by decide  
  f := ![![![1185, -350, -96, -106, -95]], ![![592, 1301, -118, 336, -1027]], ![![1127, 1097, -159, 276, -1039]], ![![548, 673, -84, 171, -598]], ![![914, 1080, -138, 274, -969]]]
  g := ![![![1, 12, 22, -12, -29], ![-30, -57, 100, 206, -171], ![47, -91, -615, -288, 929], ![82, 351, 220, -627, -229], ![-16, 60, 282, 82, -415]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [56, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [158, 238], [0, 1]]
 g := ![![[74, 142], [50, 170], [111, 134], [70, 216], [32], [97, 75], [158, 1]], ![[44, 97], [142, 69], [12, 105], [21, 23], [32], [236, 164], [77, 238]]]
 h' := ![![[158, 238], [68, 57], [237, 130], [143, 96], [43, 132], [65, 157], [234, 52], [0, 1]], ![[0, 1], [231, 182], [223, 109], [15, 143], [106, 107], [15, 82], [85, 187], [158, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [11, 136]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [56, 81, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-116, 834, 3584, 3728, -4287]
  a := ![2, 5, 9, 15, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-994, -1656, 3584, 3728, -4287]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![367, 139, -39, 32, -188]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![367, 139, -39, 32, -188]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![232, 145, 1, 0, 0], ![78, 107, 0, 1, 0], ![56, 173, 0, 0, 1]] where
  M :=![![![367, 139, -39, 32, -188], ![688, 264, -67, 60, -340], ![1240, 501, -110, 112, -600], ![-248, -90, 30, -21, 131], ![764, 312, -64, 70, -365]]]
  hmulB := by decide  
  f := ![![![-39, 25, -7, -12, 4]], ![![8, -22, 59, 24, -72]], ![![-32, 11, 29, 4, -40]], ![![-10, -2, 23, 5, -29]], ![![-4, -10, 41, 14, -51]]]
  g := ![![![73, 146, -39, 32, -188], ![128, 261, -67, 60, -340], ![216, 453, -110, 112, -600], ![-54, -104, 30, -21, 131], ![128, 273, -64, 70, -365]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P1 : CertificateIrreducibleZModOfList' 239 2 2 7 [190, 150, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 238], [0, 1]]
 g := ![![[114, 12], [211, 161], [154, 93], [47, 85], [67], [81, 197], [89, 1]], ![[226, 227], [200, 78], [66, 146], [203, 154], [67], [167, 42], [178, 238]]]
 h' := ![![[89, 238], [62, 27], [137, 20], [152, 103], [169, 221], [145, 28], [59, 83], [0, 1]], ![[0, 1], [75, 212], [5, 219], [237, 136], [1, 18], [8, 211], [37, 156], [89, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [176, 133]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N1 : CertifiedPrimeIdeal' SI239N1 239 where
  n := 2
  hpos := by decide
  P := [190, 150, 1]
  hirr := P239P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-956939, -62506, -469646, -1149866, 899416]
  a := ![127, 90, 156, 164, -441]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![616415, 148422, -469646, -1149866, 899416]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N1 B_one_repr
lemma NI239N1 : Nat.card (O ⧸ I239N1) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, -175, -5, -48, 77]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![149, -175, -5, -48, 77]] 
 ![![239, 0, 0, 0, 0], ![102, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![117, 0, 0, 0, 1]] where
  M :=![![![149, -175, -5, -48, 77], ![-212, 240, 7, 66, -105], ![288, -337, -10, -92, 147], ![-192, 224, 6, 61, -98], ![48, -58, -2, -16, 25]]]
  hmulB := by decide  
  f := ![![![-25, -23, 17, 18, -49]], ![![-10, -10, 7, 8, -21]], ![![-12, -11, 6, 6, -21]], ![![-6, -4, 6, 5, -14]], ![![-11, -11, 9, 10, -26]]]
  g := ![![![50, -175, -5, -48, 77], ![-69, 240, 7, 66, -105], ![97, -337, -10, -92, 147], ![-64, 224, 6, 61, -98], ![17, -58, -2, -16, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-37, 8, 22, -12, -29]] ![![367, 139, -39, 32, -188]]
  ![![25, 23, -17, -18, 49]] where
 M := ![![![25, 23, -17, -18, 49]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![25, 23, -17, -18, 49]] ![![149, -175, -5, -48, 77]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![-239, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0, 0, 0]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]] where
  M :=![![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 5 2 7 [149, 156, 108, 135, 141, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 34, 13, 194, 150], [225, 168, 131, 74, 37], [228, 7, 193, 77, 65], [117, 31, 145, 137, 230], [0, 1]]
 g := ![![[63, 19, 53, 132, 97], [60, 8, 165, 77], [227, 152, 124, 122], [143, 162, 34, 40], [93, 75, 194, 56, 143], [225, 100, 1], []], ![[31, 7, 13, 87, 215, 125, 178, 174], [84, 229, 174, 54], [191, 172, 45, 98], [207, 38, 52, 91], [218, 94, 146, 170, 225, 57, 114, 72], [168, 146, 8, 57, 64, 102, 69, 32], [8, 57, 28, 13, 172, 81, 9, 36]], ![[198, 51, 43, 66, 5, 141, 41, 65], [139, 166, 164, 32], [220, 210, 121, 113], [79, 90, 186, 158], [63, 206, 190, 168, 167, 161, 23, 208], [138, 164, 195, 116, 185, 232, 174, 44], [23, 130, 124, 154, 55, 187, 220, 43]], ![[152, 32, 111, 27, 82, 38, 92, 112], [72, 73, 198, 59], [141, 77, 49, 162], [126, 19, 56, 113], [14, 187, 103, 231, 178, 237, 34, 203], [43, 126, 3, 186, 59, 167, 182, 78], [32, 31, 24, 212, 131, 86, 234, 126]], ![[27, 233, 181, 156, 124, 101, 201, 228], [87, 48, 115, 91], [108, 143, 19, 107], [196, 168, 167, 125], [219, 171, 11, 114, 128, 211, 87, 185], [23, 230, 235, 34, 200, 217, 144, 132], [45, 155, 38, 208, 186, 2, 17, 115]]]
 h' := ![![[12, 34, 13, 194, 150], [99, 211, 46, 192, 196], [134, 113, 190, 127, 199], [82, 124, 176, 124, 134], [121, 57, 52, 86, 47], [215, 128, 198, 121, 216], [0, 0, 0, 1], [0, 1]], ![[225, 168, 131, 74, 37], [22, 240, 16, 10, 163], [214, 27, 154, 57, 81], [41, 109, 206, 99, 154], [235, 182, 102, 35, 36], [79, 79, 16, 39, 74], [54, 127, 46, 169, 210], [12, 34, 13, 194, 150]], ![[228, 7, 193, 77, 65], [231, 238, 203, 215, 100], [162, 144, 145, 43, 88], [86, 32, 50, 236, 178], [17, 49, 56, 70, 188], [39, 179, 68, 120, 195], [189, 26, 232, 84, 67], [225, 168, 131, 74, 37]], ![[117, 31, 145, 137, 230], [97, 213, 60, 139, 91], [170, 206, 139, 189, 78], [137, 166, 26, 185, 198], [178, 44, 177, 204, 178], [83, 192, 232, 112, 165], [24, 204, 204, 177, 26], [228, 7, 193, 77, 65]], ![[0, 1], [50, 62, 157, 167, 173], [177, 233, 95, 66, 36], [107, 51, 24, 79, 59], [106, 150, 95, 87, 33], [171, 145, 209, 90, 73], [211, 125, 0, 51, 179], [117, 31, 145, 137, 230]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 18, 137, 111], [], [], []]
 b := ![[], [237, 59, 162, 77, 33], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 5
  hpos := by decide
  P := [149, 156, 108, 135, 141, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-79247844872958, 3598273300528, -16592959473286, -81553808215824, 35341910935904]
  a := ![31, 23, 39, 42, -108]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-328829231838, 14930594608, -68850454246, -338397544464, 146646933344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 812990017201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0, 0, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0, 0, 0]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![0, 0, 0, 0, 251]] where
  M :=![![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![0, 0, 0, 0, 251]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 5 2 7 [24, 237, 144, 87, 51, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [209, 186, 150, 219, 163], [214, 149, 88, 6, 218], [79, 50, 211, 181, 250], [200, 116, 53, 96, 122], [0, 1]]
 g := ![![[190, 126, 28, 91, 20], [180, 84, 108, 32, 38], [177, 150, 237, 217], [215, 103, 78, 60, 20], [89, 104, 219, 187, 58], [4, 200, 1], []], ![[177, 11, 41, 40, 58, 37, 89, 8], [230, 144, 24, 4, 122, 206, 56, 206], [179, 168, 198, 100], [222, 212, 154, 42, 184, 11, 217, 8], [1, 141, 84, 31, 40, 80, 210, 165], [5, 211, 16, 140, 247, 242, 106, 30], [170, 137, 108, 203, 219, 200, 144, 244]], ![[45, 215, 34, 8, 91, 189, 247, 45], [70, 76, 112, 16, 62, 89, 116, 49], [217, 8, 55, 154], [148, 136, 2, 80, 100, 14, 137, 13], [223, 215, 38, 89, 183, 122, 225, 221], [106, 44, 63, 20, 148, 231, 181, 39], [52, 213, 200, 62, 238, 157, 9, 207]], ![[155, 162, 11, 191, 70, 185, 200, 47], [234, 22, 149, 1, 231, 51, 21, 206], [8, 25, 179, 121], [217, 193, 238, 3, 131, 114, 81, 109], [123, 168, 57, 133, 98, 21, 34, 212], [23, 59, 109, 111, 197, 80, 247, 29], [89, 56, 155, 202, 183, 153, 92, 250]], ![[195, 11, 234, 194, 200, 105, 142, 51], [39, 127, 102, 67, 156, 250, 46, 161], [96, 238, 185, 117], [130, 63, 148, 197, 193, 8, 208, 222], [205, 159, 102, 228, 94, 0, 135, 36], [84, 30, 75, 132, 111, 141, 210, 155], [97, 213, 104, 96, 134, 239, 224, 114]]]
 h' := ![![[209, 186, 150, 219, 163], [198, 177, 191, 186, 32], [41, 100, 173, 134, 234], [111, 105, 64, 243, 172], [123, 185, 170, 111, 32], [155, 25, 192, 233, 73], [0, 0, 0, 1], [0, 1]], ![[214, 149, 88, 6, 218], [33, 119, 94, 188, 214], [124, 124, 144, 200, 7], [116, 217, 182, 39, 10], [172, 98, 234, 108, 37], [189, 226, 168, 36, 197], [144, 237, 105, 34, 157], [209, 186, 150, 219, 163]], ![[79, 50, 211, 181, 250], [142, 180, 232, 232, 188], [10, 149, 138, 10, 132], [169, 220, 228, 112, 144], [72, 241, 174, 88, 69], [147, 108, 225, 108, 158], [56, 139, 215, 48, 27], [214, 149, 88, 6, 218]], ![[200, 116, 53, 96, 122], [179, 60, 157, 120, 188], [148, 67, 221, 166, 203], [66, 124, 36, 243, 11], [185, 183, 144, 133, 49], [228, 185, 193, 72, 87], [198, 73, 14, 230, 184], [79, 50, 211, 181, 250]], ![[0, 1], [225, 217, 79, 27, 131], [69, 62, 77, 243, 177], [37, 87, 243, 116, 165], [42, 46, 31, 62, 64], [169, 209, 226, 53, 238], [59, 53, 168, 189, 134], [200, 116, 53, 96, 122]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [200, 152, 111, 52], [], [], []]
 b := ![[], [180, 72, 21, 47, 12], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 5
  hpos := by decide
  P := [24, 237, 144, 87, 51, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5068427857170, -1130692905361, -6856436207665, -10134819830248, 11296904205727]
  a := ![-17, -5, -8, 4, 61]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20192939670, -4504752611, -27316478915, -40377768248, 45007586477]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 996250626251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def PBC251 : ContainsPrimesAboveP 251 ![I251N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![251, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 251 (by decide) 𝕀



lemma PB312I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB312I5 : PrimesBelowBoundCertificateInterval O 197 251 312 where
  m := 9
  g := ![3, 1, 3, 1, 3, 1, 3, 1, 1]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB312I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0]
    · exact ![I239N0, I239N1, I239N2]
    · exact ![I241N0]
    · exact ![I251N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![39601, 39601, 199]
    · exact ![418227202051]
    · exact ![49729, 49729, 223]
    · exact ![602738989907]
    · exact ![52441, 52441, 229]
    · exact ![686719856393]
    · exact ![57121, 57121, 239]
    · exact ![812990017201]
    · exact ![996250626251]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
      exact NI199N2
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
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
      exact NI239N2
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
  β := ![I199N2, I223N2, I229N2, I239N2]
  Il := ![[I199N2], [], [I223N2], [], [I229N2], [], [I239N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
