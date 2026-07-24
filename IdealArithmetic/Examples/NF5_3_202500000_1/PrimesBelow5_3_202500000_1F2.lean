
import IdealArithmetic.Examples.NF5_3_202500000_1.RI5_3_202500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65, -33, -16, -17, -24]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-65, -33, -16, -17, -24]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![39, 60, 23, 37, 1]] where
  M :=![![![-65, -33, -16, -17, -24], ![-226, -90, -68, -89, -102], ![-994, -349, -289, -395, -534], ![-2094, -691, -534, -760, -1002], ![-684, -238, -156, -216, -301]]]
  hmulB := by decide  
  f := ![![![33, -11, -2, 5, -12]], ![![-86, 28, 6, -13, 30]], ![![214, -75, -17, 35, -78]], ![![-142, 47, 12, -24, 54]], ![![-63, 19, 5, -10, 23]]]
  g := ![![![13, 21, 8, 13, -24], ![56, 90, 34, 55, -102], ![296, 473, 179, 289, -534], ![552, 887, 336, 542, -1002], ![165, 266, 101, 163, -301]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [37, 65, 2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 1, 31, 37], [47, 46, 2, 17], [10, 19, 34, 13], [0, 1]]
 g := ![![[36, 19, 37, 17], [66, 52, 57, 62], [12, 44, 37], [55, 0, 4], [1], []], ![[29, 26, 11, 41, 53, 23], [57, 56, 16, 20, 25, 54], [48, 33, 47], [7, 15, 65], [21, 35, 62], [56, 25, 29]], ![[15, 41, 18, 58, 55, 36], [28, 60, 29, 19, 34, 15], [25, 9, 39], [64, 48, 33], [7, 11, 29], [0, 26, 21]], ![[1, 58, 38, 49, 64, 2], [35, 13, 31, 23, 2, 7], [28, 63, 54], [65, 5, 10], [32, 31, 60], [19, 10, 35]]]
 h' := ![![[8, 1, 31, 37], [37, 23, 63, 33], [41, 35, 28, 14], [4, 29, 28, 38], [30, 2, 65, 65], [0, 0, 1], [0, 1]], ![[47, 46, 2, 17], [26, 10, 13, 8], [52, 12, 41, 5], [32, 23, 42, 39], [31, 48, 55, 47], [2, 7, 32, 14], [8, 1, 31, 37]], ![[10, 19, 34, 13], [42, 62, 29, 12], [23, 15, 34, 44], [12, 18, 41, 46], [13, 28, 66, 10], [65, 12, 38, 30], [47, 46, 2, 17]], ![[0, 1], [59, 39, 29, 14], [51, 5, 31, 4], [22, 64, 23, 11], [22, 56, 15, 12], [0, 48, 63, 23], [10, 19, 34, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [29, 1, 23], []]
 b := ![[], [], [0, 9, 12, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 4
  hpos := by decide
  P := [37, 65, 2, 2, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![111755367527, 39967793529, 29433745958, 39893914159, 54336989598]
  a := ![-17, -10, -24, -5, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-29961003385, -48063456453, -18213686788, -29411562701, 54336989598]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, 11, 2, -5, 12]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-33, 11, 2, -5, 12]] 
 ![![67, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-33, 11, 2, -5, 12], ![86, -28, -6, 13, -30], ![-214, 75, 17, -35, 78], ![142, -47, -12, 24, -54], ![16, -8, 0, 2, -5]]]
  hmulB := by decide  
  f := ![![![65, 33, 16, 17, 24]], ![![48, 24, 12, 13, 18]], ![![42, 19, 11, 13, 18]], ![![72, 31, 18, 22, 30]], ![![17, 7, 4, 5, 7]]]
  g := ![![![-7, 11, 2, -5, 12], ![18, -28, -6, 13, -30], ![-48, 75, 17, -35, 78], ![30, -47, -12, 24, -54], ![5, -8, 0, 2, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-65, -33, -16, -17, -24]] ![![-33, 11, 2, -5, 12]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3899, 1282, 164, -514, 1292]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-3899, 1282, 164, -514, 1292]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![41, 51, 32, 14, 1]] where
  M :=![![![-3899, 1282, 164, -514, 1292], ![9308, -3285, -424, 1270, -3084], ![-22132, 7918, 949, -3086, 7620], ![13988, -4638, -588, 1855, -4660], ![2888, -1104, -108, 432, -1095]]]
  hmulB := by decide  
  f := ![![![-69, 18, 12, -18, 28]], ![![188, -71, -48, 46, -108]], ![![-772, 174, 115, -206, 276]], ![![404, -238, -164, 85, -356]], ![![-175, -9, -8, -54, -7]]]
  g := ![![![-801, -910, -580, -262, 1292], ![1912, 2169, 1384, 626, -3084], ![-4712, -5362, -3421, -1546, 7620], ![2888, 3282, 2092, 945, -4660], ![673, 771, 492, 222, -1095]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [51, 2, 65, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 1, 23, 18], [25, 4, 69, 41], [53, 65, 50, 12], [0, 1]]
 g := ![![[67, 52, 10, 57], [55, 35, 10, 27], [61, 19], [61, 39, 4], [1], []], ![[2, 7, 70, 54, 14, 49], [12, 33, 44, 14, 3, 36], [4, 67, 61, 3, 36, 12], [69, 55, 32], [11, 49, 37], [19, 38, 40]], ![[51, 29, 20, 10, 30, 33], [20, 15, 36, 55, 36, 22], [65, 64, 45, 40, 66, 31], [61, 69, 40], [45, 47, 12], [4, 24, 48]], ![[38, 11, 10, 12, 61, 40], [15, 49, 12, 13, 14, 15], [28, 4, 26, 17, 7, 3], [7, 41, 30], [48, 42, 50], [47, 60, 2]]]
 h' := ![![[62, 1, 23, 18], [35, 49, 60, 46], [13, 1, 68, 13], [58, 10, 44], [20, 69, 6, 69], [0, 0, 1], [0, 1]], ![[25, 4, 69, 41], [7, 2, 60, 57], [35, 38, 64, 12], [17, 30, 44, 30], [25, 41, 35, 23], [35, 65, 70, 45], [62, 1, 23, 18]], ![[53, 65, 50, 12], [31, 53, 27, 52], [5, 32, 4, 2], [17, 1, 51, 5], [2, 23, 14, 18], [66, 33, 0, 15], [25, 4, 69, 41]], ![[0, 1], [49, 38, 66, 58], [9, 0, 6, 44], [43, 30, 3, 36], [20, 9, 16, 32], [57, 44, 0, 11], [53, 65, 50, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [60, 64, 44], []]
 b := ![[], [], [31, 37, 34, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [51, 2, 65, 2, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2721187306387129, 1028512457025108, 756147241385584, 979769273480284, 1403338704151776]
  a := ![-240, -181, -361, -1, -723]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-772052106532897, -993545935981908, -621840722415088, -262915106825980, 1403338704151776]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![69, -18, -12, 18, -28]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![69, -18, -12, 18, -28]] 
 ![![71, 0, 0, 0, 0], ![58, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![59, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![69, -18, -12, 18, -28], ![-188, 71, 48, -46, 108], ![772, -174, -115, 206, -276], ![-404, 238, 164, -85, 356], ![136, -8, -4, 40, -15]]]
  hmulB := by decide  
  f := ![![![3899, -1282, -164, 514, -1292]], ![![3054, -1001, -128, 402, -1012]], ![![2728, -906, -115, 362, -908]], ![![3043, -1000, -128, 401, -1008]], ![![3419, -1122, -144, 450, -1131]]]
  g := ![![![33, -18, -12, 18, -28], ![-148, 71, 48, -46, 108], ![298, -174, -115, 206, -276], ![-547, 238, 164, -85, 356], ![-9, -8, -4, 40, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-3899, 1282, 164, -514, 1292]] ![![69, -18, -12, 18, -28]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![-71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1243, 380, 244, -310, 576]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-1243, 380, 244, -310, 576]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![55, 62, 6, 57, 1]] where
  M :=![![![-1243, 380, 244, -310, 576], ![3988, -1221, -794, 998, -1860], ![-12884, 3920, 2567, -3244, 5988], ![10840, -3336, -2202, 2733, -5112], ![-1520, 450, 312, -394, 709]]]
  hmulB := by decide  
  f := ![![![21, 12, 0, -2, 0]], ![![-4, 19, 6, -2, -12]], ![![-100, -24, 7, 4, -12]], ![![-64, -40, -2, 5, 0]], ![![-45, -8, 4, 1, -11]]]
  g := ![![![-451, -484, -44, -454, 576], ![1456, 1563, 142, 1466, -1860], ![-4688, -5032, -457, -4720, 5988], ![4000, 4296, 390, 4029, -5112], ![-555, -596, -54, -559, 709]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 4 2 6 [29, 62, 19, 51, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 7, 46, 66], [6, 25, 12, 52], [14, 40, 15, 28], [0, 1]]
 g := ![![[10, 24, 19, 18], [55, 9, 70], [69, 8, 12], [6, 47, 30, 46], [1], []], ![[47, 28, 70, 24, 2, 10], [68, 41, 27], [13, 32, 6], [0, 64, 6, 69, 19, 62], [69, 32, 25], [50, 69, 49]], ![[27, 33, 1, 69, 3, 53], [18, 54, 38], [30, 55, 6], [32, 51, 12, 12, 14, 56], [1], [59, 0, 3]], ![[46, 11, 39, 53, 16, 60], [4, 21, 4], [20, 2, 12], [7, 37, 26, 65, 28, 39], [69, 32, 25], [65, 57, 54]]]
 h' := ![![[2, 7, 46, 66], [3, 2, 41, 23], [24, 2, 43, 17], [45, 55, 63, 42], [44, 11, 54, 22], [0, 0, 1], [0, 1]], ![[6, 25, 12, 52], [8, 69, 51, 70], [70, 61, 49, 10], [70, 5, 21, 15], [20, 64, 55, 31], [14, 37, 8, 68], [2, 7, 46, 66]], ![[14, 40, 15, 28], [27, 66, 69, 40], [29, 65, 16, 44], [13, 68, 5, 58], [60, 11, 46, 22], [4, 0, 72], [6, 25, 12, 52]], ![[0, 1], [65, 9, 58, 13], [20, 18, 38, 2], [69, 18, 57, 31], [70, 60, 64, 71], [63, 36, 65, 5], [14, 40, 15, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [49, 56, 67], []]
 b := ![[], [], [31, 48, 51, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 4
  hpos := by decide
  P := [29, 62, 19, 51, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60028983742, 21596676506, 15899721838, 21449213979, 29371911286]
  a := ![-15, -10, -22, -3, -46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21307207356, -24650161962, -2196325286, -22640407251, 29371911286]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 28398241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -12, 0, 2, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-21, -12, 0, 2, 0]] 
 ![![73, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![-21, -12, 0, 2, 0], ![4, -19, -6, 2, 12], ![100, 24, -7, -4, 12], ![64, 40, 2, -5, 0], ![-56, -2, 8, 2, -13]]]
  hmulB := by decide  
  f := ![![![1243, -380, -244, 310, -576]], ![![337, -103, -66, 84, -156]], ![![1113, -340, -219, 278, -516]], ![![158, -48, -30, 39, -72]], ![![753, -230, -148, 188, -349]]]
  g := ![![![3, -12, 0, 2, 0], ![3, -19, -6, 2, 12], ![-7, 24, -7, -4, 12], ![-12, 40, 2, -5, 0], ![1, -2, 8, 2, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-1243, 380, 244, -310, 576]] ![![-21, -12, 0, 2, 0]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![-73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![196243, -59688, -40119, 50009, -92272]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![196243, -59688, -40119, 50009, -92272]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![43, 18, 46, 1, 0], ![18, 4, 23, 0, 1]] where
  M :=![![![196243, -59688, -40119, 50009, -92272], ![-638158, 194099, 130458, -162620, 300054], ![2075192, -631182, -424219, 528808, -975720], ![-1770370, 538472, 361900, -451127, 832394], ![257894, -78442, -52712, 65712, -121251]]]
  hmulB := by decide  
  f := ![![![-141, 70, 41, -3, -70]], ![![-566, -255, 20, 50, -18]], ![![-44, -554, -125, 92, 300]], ![![-223, -344, -47, 64, 136]], ![![-68, -152, -25, 28, 69]]]
  g := ![![![-3712, -7478, -2763, 50009, -92272], ![12070, 24317, 8984, -162620, 300054], ![-39248, -79074, -29213, 528808, -975720], ![33481, 67458, 24920, -451127, 832394], ![-4876, -9826, -3629, 65712, -121251]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [45, 65, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 71, 20], [3, 7, 59], [0, 1]]
 g := ![![[25, 71, 64], [62, 23, 1], [23, 16, 55], [10, 56, 62], [63, 1], []], ![[50, 37, 1, 13], [69, 17, 42, 1], [17, 38, 5, 20], [63, 58, 18, 49], [53, 49], [74, 5]], ![[47, 45, 64, 39], [50, 51, 73, 57], [63, 52, 20, 14], [16, 0, 9, 48], [68, 64], [35, 5]]]
 h' := ![![[60, 71, 20], [54, 55, 71], [71, 20, 78], [24, 71, 23], [9, 47, 33], [0, 0, 1], [0, 1]], ![[3, 7, 59], [9, 41, 17], [53, 68, 77], [66, 34, 1], [47, 0, 65], [33, 9, 7], [60, 71, 20]], ![[0, 1], [28, 62, 70], [38, 70, 3], [6, 53, 55], [59, 32, 60], [14, 70, 71], [3, 7, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 44], []]
 b := ![[], [50, 17, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [45, 65, 16, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9341681119, 4445185433, 3266976622, 3494686129, 6162308140]
  a := ![98, 72, 147, -1, 293]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3187992012, -1052005031, -3787616108, 3494686129, 6162308140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-141, 70, 41, -3, -70]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-141, 70, 41, -3, -70]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![54, 19, 1, 0, 0], ![71, 9, 0, 1, 0], ![78, 12, 0, 0, 1]] where
  M :=![![![-141, 70, 41, -3, -70], ![-566, -255, 20, 50, -18], ![-44, -554, -125, 92, 300], ![658, -112, -86, 53, 278], ![442, 494, 82, -50, -117]]]
  hmulB := by decide  
  f := ![![![196243, -59688, -40119, 50009, -92272]], ![![-638158, 194099, 130458, -162620, 300054]], ![![6928, -2107, -1417, 1766, -3258]], ![![81259, -24715, -16613, 20708, -38208]], ![![100088, -30442, -20462, 25506, -47061]]]
  g := ![![![42, 2, 41, -3, -70], ![-48, -11, 20, 50, -18], ![-294, -33, -125, 92, 300], ![-255, -29, -86, 53, 278], ![110, 10, 82, -50, -117]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [5, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 78], [0, 1]]
 g := ![![[76, 16], [67, 64], [24, 31], [7, 38], [67], [1]], ![[0, 63], [0, 15], [15, 48], [24, 41], [67], [1]]]
 h' := ![![[15, 78], [60, 75], [38, 8], [44, 30], [6, 65], [74, 15], [0, 1]], ![[0, 1], [0, 4], [0, 71], [20, 49], [33, 14], [62, 64], [15, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [2, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [5, 64, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19159, 77515, 60885, 16382, 118195]
  a := ![-32, -24, -50, 8, -95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-172797, -33482, 60885, 16382, 118195]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![196243, -59688, -40119, 50009, -92272]] ![![-141, 70, 41, -3, -70]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2943, 897, 602, -751, 1386]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-2943, 897, 602, -751, 1386]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![59, 64, 1, 0, 0], ![6, 31, 0, 1, 0], ![80, 76, 0, 0, 1]] where
  M :=![![![-2943, 897, 602, -751, 1386], ![9586, -2910, -1958, 2441, -4506], ![-31166, 9479, 6371, -7939, 14646], ![26570, -8087, -5432, 6774, -12498], ![-3868, 1174, 790, -986, 1823]]]
  hmulB := by decide  
  f := ![![![3167, -1093, -136, 431, -1062]], ![![-7634, 2672, 336, -1039, 2586]], ![![-3411, 1206, 153, -464, 1164]], ![![-2758, 967, 122, -375, 936]], ![![-3968, 1404, 178, -540, 1355]]]
  g := ![![![-1745, -1442, 602, -751, 1386], ![5674, 4689, -1958, 2441, -4506], ![-18447, -15244, 6371, -7939, 14646], ![15738, 13005, -5432, 6774, -12498], ![-2294, -1896, 790, -986, 1823]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [26, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 82], [0, 1]]
 g := ![![[61, 16], [78, 64], [40], [36], [71, 81], [1]], ![[0, 67], [0, 19], [40], [36], [6, 2], [1]]]
 h' := ![![[74, 82], [47, 79], [72, 8], [45, 17], [63, 6], [57, 74], [0, 1]], ![[0, 1], [0, 4], [0, 75], [58, 66], [9, 77], [55, 9], [74, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [4, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [26, 9, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-67396, 21974, 20038, -21882, 38790]
  a := ![14, 18, 30, -26, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-50862, -42532, 20038, -21882, 38790]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, -7, -3, 2, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![27, -7, -3, 2, 0]] 
 ![![83, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![27, -7, -3, 2, 0], ![4, 32, 2, -7, 12], ![82, 7, 9, 11, -42], ![-76, 27, 14, 0, 12], ![-22, -24, -4, 4, 17]]]
  hmulB := by decide  
  f := ![![![86639, -26351, -17709, 22076, -40734]], ![![1825, -555, -373, 465, -858]], ![![71580, -21771, -14631, 18239, -33654]], ![![27119, -8248, -5543, 6910, -12750]], ![![64002, -19466, -13082, 16308, -30091]]]
  g := ![![![2, -7, -3, 2, 0], ![-9, 32, 2, -7, 12], ![20, 7, 9, 11, -42], ![-21, 27, 14, 0, 12], ![-10, -24, -4, 4, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1435, 459, 45, -208, 438]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-1435, 459, 45, -208, 438]] 
 ![![83, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![76, 0, 1, 0, 0], ![68, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-1435, 459, 45, -208, 438], ![3088, -1250, -210, 365, -1248], ![-9254, 2415, 55, -1513, 2190], ![2776, -2489, -778, -102, -2712], ![478, -614, -214, -76, -683]]]
  hmulB := by decide  
  f := ![![![1041, -1157, -421, 554, -768]], ![![140, -208, -70, 89, -108]], ![![1238, -1109, -435, 563, -810]], ![![680, -865, -302, 400, -540]], ![![194, -240, -84, 116, -167]]]
  g := ![![![-61, 459, 45, -208, 438], ![412, -1250, -210, 365, -1248], ![190, 2415, 55, -1513, 2190], ![1832, -2489, -778, -102, -2712], ![514, -614, -214, -76, -683]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2

def I83N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![649, -195, -132, 165, -306]] i)))

def SI83N3: IdealEqSpanCertificate' Table ![![649, -195, -132, 165, -306]] 
 ![![83, 0, 0, 0, 0], ![81, 1, 0, 0, 0], ![79, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![649, -195, -132, 165, -306], ![-2118, 640, 432, -537, 990], ![6846, -2097, -1403, 1749, -3222], ![-5850, 1773, 1194, -1490, 2754], ![864, -252, -174, 216, -401]]]
  hmulB := by decide  
  f := ![![![1127, 39, 138, 291, 126]], ![![1119, 55, 144, 294, 144]], ![![1261, 78, 169, 336, 180]], ![![581, 120, 114, 181, 180]], ![![732, 54, 102, 198, 115]]]
  g := ![![![455, -195, -132, 165, -306], ![-1485, 640, 432, -537, 990], ![4843, -2097, -1403, 1749, -3222], ![-4117, 1773, 1194, -1490, 2754], ![594, -252, -174, 216, -401]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N3 : Nat.card (O ⧸ I83N3) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N3)

lemma isPrimeI83N3 : Ideal.IsPrime I83N3 := prime_ideal_of_norm_prime hp83.out _ NI83N3
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-2943, 897, 602, -751, 1386]] ![![27, -7, -3, 2, 0]]
  ![![75, -22, -17, 1, 30]] where
 M := ![![![75, -22, -17, 1, 30]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![75, -22, -17, 1, 30]] ![![-1435, 459, 45, -208, 438]]
  ![![-1127, -39, -138, -291, -126]] where
 M := ![![![-1127, -39, -138, -291, -126]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N2 : IdealMulLeCertificate' Table 
  ![![-1127, -39, -138, -291, -126]] ![![649, -195, -132, 165, -306]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![-83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2, I83N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
    exact isPrimeI83N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1 ⊙ MulI83N2)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7721, -2685, -334, 1053, -2604]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![7721, -2685, -334, 1053, -2604]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![32, 84, 36, 1, 0], ![42, 31, 22, 0, 1]] where
  M :=![![![7721, -2685, -334, 1053, -2604], ![-18726, 6504, 808, -2553, 6318], ![45438, -15769, -1963, 6189, -15318], ![-27818, 9669, 1202, -3794, 9378], ![-6296, 2178, 272, -856, 2117]]]
  hmulB := by decide  
  f := ![![![-59, 19, 12, -15, 24]], ![![162, -62, -38, 45, -90]], ![![-630, 155, 111, -159, 270]], ![![-118, 9, 12, -26, 30]], ![![-128, 26, 20, -31, 47]]]
  g := ![![![937, -117, 214, 1053, -2604], ![-2274, 282, -520, -2553, 6318], ![5514, -683, 1261, 6189, -15318], ![-3374, 423, -770, -3794, 9378], ![-762, 95, -174, -856, 2117]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [57, 0, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 85, 45], [3, 3, 44], [0, 1]]
 g := ![![[5, 9, 81], [18, 40], [2, 39], [19, 87, 8], [47, 74, 1], []], ![[83, 33, 79, 36], [46, 32], [25, 80], [64, 21, 46, 44], [43, 57, 41, 49], [59, 67]], ![[28, 11, 52, 42], [42, 87], [68, 68], [46, 19, 46, 32], [38, 52, 5, 81], [60, 67]]]
 h' := ![![[71, 85, 45], [81, 21, 80], [22, 26, 29], [74, 17, 67], [80, 54, 39], [0, 0, 1], [0, 1]], ![[3, 3, 44], [87, 61, 28], [67, 32, 11], [54, 59, 76], [25, 16, 55], [76, 63, 3], [71, 85, 45]], ![[0, 1], [49, 7, 70], [60, 31, 49], [51, 13, 35], [1, 19, 84], [60, 26, 85], [3, 3, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 24], []]
 b := ![[], [35, 2, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [57, 0, 15, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12608635, 4543271, 3346748, 4507087, 6177476]
  a := ![12, 6, 10, 5, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4394069, -6354537, -3312504, 4507087, 6177476]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, -43, -29, 36, -66]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![139, -43, -29, 36, -66]] 
 ![![89, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  M :=![![![139, -43, -29, 36, -66], ![-456, 138, 94, -117, 216], ![1494, -451, -307, 381, -702], ![-1272, 389, 262, -326, 600], ![186, -58, -38, 48, -89]]]
  hmulB := by decide  
  f := ![![![-211, -49, -41, -66, -84]], ![![-28, -8, -6, -9, -12]], ![![-101, -28, -22, -33, -42]], ![![-225, -62, -49, -74, -96]], ![![-188, -46, -38, -60, -77]]]
  g := ![![![40, -43, -29, 36, -66], ![-131, 138, 94, -117, 216], ![426, -451, -307, 381, -702], ![-364, 389, 262, -326, 600], ![54, -58, -38, 48, -89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, -12, 3, 9, -8]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![57, -12, 3, 9, -8]] 
 ![![89, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![71, 0, 0, 0, 1]] where
  M :=![![![57, -12, 3, 9, -8], ![-46, 55, 12, 10, 54], ![452, 6, 73, 100, 60], ![362, 200, 106, 163, 238], ![74, 68, 40, 38, 87]]]
  hmulB := by decide  
  f := ![![![4591, 2602, 29, -409, -94]], ![![3129, 1829, 35, -285, -92]], ![![647, 432, 22, -65, -46]], ![![3256, 1836, 18, -289, -62]], ![![3803, 2086, 5, -331, -43]]]
  g := ![![![8, -12, 3, 9, -8], ![-91, 55, 12, 10, 54], ![-135, 6, 73, 100, 60], ![-464, 200, 106, 163, 238], ![-151, 68, 40, 38, 87]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![7721, -2685, -334, 1053, -2604]] ![![139, -43, -29, 36, -66]]
  ![![-25177, 8750, 1077, -3423, 8478]] where
 M := ![![![-25177, 8750, 1077, -3423, 8478]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![-25177, 8750, 1077, -3423, 8478]] ![![57, -12, 3, 9, -8]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-1962539, 681740, 84372, -267178, 661448]]]
 hmul := by decide  
 g := ![![![![-22051, 7660, 948, -3002, 7432]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-103, 128, 40, 10, 142]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-103, 128, 40, 10, 142]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![71, 5, 44, 11, 1]] where
  M :=![![![-103, 128, 40, 10, 142], ![1156, 9, 118, 272, 60], ![1024, 1370, 707, 686, 1632], ![5536, 1338, 1182, 1799, 1936], ![1588, 396, 342, 522, 603]]]
  hmulB := by decide  
  f := ![![![-351, 108, 72, -90, 166]], ![![1148, -347, -234, 292, -540]], ![![-3736, 1134, 763, -950, 1752]], ![![3176, -970, -650, 811, -1496]], ![![-1537, 467, 314, -391, 721]]]
  g := ![![![-105, -6, -64, -16, 142], ![-32, -3, -26, -4, 60], ![-1184, -70, -733, -178, 1632], ![-1360, -86, -866, -201, 1936], ![-425, -27, -270, -63, 603]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [58, 75, 29, 68, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 55, 95, 61], [59, 39, 48, 46], [74, 2, 51, 87], [0, 1]]
 g := ![![[62, 96, 43, 33], [75, 24, 1], [8, 8, 24], [58, 71, 88], [36, 29, 1], []], ![[37, 72, 64, 40, 9, 25], [26, 54, 48], [42, 35, 24], [71, 75, 72], [26, 37, 75], [18, 29, 6, 65, 13, 1]], ![[87, 6, 65, 70, 49, 92], [59, 50, 65], [21, 5, 66], [89, 66, 8], [9, 20, 93], [16, 64, 37, 89, 71, 45]], ![[43, 13, 66, 27, 79, 58], [63, 94, 50], [19, 39, 66], [19, 28, 79], [19, 89, 16], [45, 42, 87, 82, 74, 67]]]
 h' := ![![[90, 55, 95, 61], [31, 32, 77, 18], [93, 4, 46, 1], [13, 56, 4, 11], [46, 80, 21, 31], [0, 0, 0, 1], [0, 1]], ![[59, 39, 48, 46], [48, 37, 80, 14], [95, 54, 73, 40], [3, 64, 8, 86], [12, 38, 14, 84], [68, 9, 66, 47], [90, 55, 95, 61]], ![[74, 2, 51, 87], [17, 1, 79, 83], [74, 1, 57, 29], [15, 4, 68, 58], [6, 43, 49, 28], [72, 9, 69, 53], [59, 39, 48, 46]], ![[0, 1], [26, 27, 55, 79], [73, 38, 18, 27], [37, 70, 17, 39], [84, 33, 13, 51], [64, 79, 59, 93], [74, 2, 51, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [72, 24, 39], []]
 b := ![[], [], [92, 41, 74, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [58, 75, 29, 68, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3127914762, 1117472720, 822634827, 1116531217, 1518855533]
  a := ![-8, -6, -11, -1, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1079493073, -66771185, -680484625, -160730718, 1518855533]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-351, 108, 72, -90, 166]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-351, 108, 72, -90, 166]] 
 ![![97, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![82, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-351, 108, 72, -90, 166], ![1148, -347, -234, 292, -540], ![-3736, 1134, 763, -950, 1752], ![3176, -970, -650, 811, -1496], ![-460, 140, 94, -118, 219]]]
  hmulB := by decide  
  f := ![![![-103, 128, 40, 10, 142]], ![![-21, 41, 14, 6, 46]], ![![1, 26, 11, 8, 30]], ![![-30, 122, 46, 27, 140]], ![![10, 12, 6, 6, 15]]]
  g := ![![![21, 108, 72, -90, 166], ![-69, -347, -234, 292, -540], ![223, 1134, 763, -950, 1752], ![-190, -970, -650, 811, -1496], ![28, 140, 94, -118, 219]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-103, 128, 40, 10, 142]] ![![-351, 108, 72, -90, 166]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67455, 23424, 2913, -9195, 22742]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-67455, 23424, 2913, -9195, 22742]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![4, 20, 98, 1, 0], ![73, 28, 34, 0, 1]] where
  M :=![![![-67455, 23424, 2913, -9195, 22742], ![163546, -56821, -7074, 22286, -55170], ![-396788, 137736, 17111, -54106, 133716], ![242758, -84458, -10552, 33041, -82030], ![54802, -19076, -2386, 7456, -18531]]]
  hmulB := by decide  
  f := ![![![1355, -430, -281, 355, -656]], ![![-4538, 1335, 916, -1144, 2130]], ![![14752, -4468, -3013, 3734, -6864]], ![![13346, -4050, -2728, 3379, -6206]], ![![4705, -1450, -967, 1201, -2203]]]
  g := ![![![-16741, -4252, 1295, -9195, 22742], ![40612, 10319, -3122, 22286, -55170], ![-98432, -24992, 7655, -54106, 133716], ![60384, 15362, -4550, 33041, -82030], ![13641, 3472, -1020, 7456, -18531]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [50, 37, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 81, 68], [85, 19, 33], [0, 1]]
 g := ![![[21, 89, 5], [82, 78], [30, 75, 22], [79, 19], [26, 5], [1]], ![[1, 98, 48, 88], [83, 68], [79, 57, 0, 87], [7, 6], [41, 5], [42, 16, 54, 19]], ![[42, 68, 60, 22], [63, 84], [7, 11, 36, 17], [11, 95], [], [59, 62, 12, 82]]]
 h' := ![![[61, 81, 68], [64, 95, 45], [15, 2, 52], [32, 45, 74], [89, 64, 76], [51, 64, 45], [0, 1]], ![[85, 19, 33], [40, 6, 43], [7, 37, 13], [67, 37, 22], [66, 29, 39], [55, 20, 56], [61, 81, 68]], ![[0, 1], [46, 0, 13], [60, 62, 36], [47, 19, 5], [71, 8, 87], [24, 17], [85, 19, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40], []]
 b := ![[], [2, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [50, 37, 56, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![47365206, 20966738, 15471127, 17476745, 28995498]
  a := ![16, 10, 23, 2, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21180328, -11291506, -26565315, 17476745, 28995498]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1355, -430, -281, 355, -656]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![1355, -430, -281, 355, -656]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![89, 8, 1, 0, 0], ![28, 78, 0, 1, 0], ![23, 69, 0, 0, 1]] where
  M :=![![![1355, -430, -281, 355, -656], ![-4538, 1335, 916, -1144, 2130], ![14752, -4468, -3013, 3734, -6864], ![-12410, 3834, 2550, -3193, 5890], ![1786, -528, -360, 462, -879]]]
  hmulB := by decide  
  f := ![![![-67455, 23424, 2913, -9195, 22742]], ![![163546, -56821, -7074, 22286, -55170]], ![![-50415, 17504, 2176, -6873, 16994]], ![![110006, -38224, -4760, 14989, -37114]], ![![96911, -33673, -4193, 13205, -32695]]]
  g := ![![![312, 192, -281, 355, -656], ![-1020, -631, 916, -1144, 2130], ![3329, 2000, -3013, 3734, -6864], ![-2826, -1722, 2550, -3193, 5890], ![407, 267, -360, 462, -879]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [61, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 100], [0, 1]]
 g := ![![[83, 92], [87], [29, 97], [6], [49], [88, 1]], ![[99, 9], [87], [81, 4], [6], [49], [75, 100]]]
 h' := ![![[88, 100], [23, 30], [49, 17], [94, 81], [64, 62], [86, 7], [0, 1]], ![[0, 1], [37, 71], [30, 84], [51, 20], [66, 39], [96, 94], [88, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [50, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [61, 13, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18241, 44743, 36352, 10863, 70380]
  a := ![24, 18, 37, -5, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-50891, -58907, 36352, 10863, 70380]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-67455, 23424, 2913, -9195, 22742]] ![![1355, -430, -281, 355, -656]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0, 0, 0]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]] where
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 5 2 6 [36, 74, 81, 45, 100, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 1, 48, 81, 20], [75, 27, 59, 45, 34], [44, 98, 24, 74, 1], [54, 79, 75, 6, 48], [0, 1]]
 g := ![![[102, 34, 49, 39, 17], [14, 84, 72, 48, 41], [23, 33, 78, 47, 55], [21, 58, 76, 60], [3, 1], []], ![[65, 36, 31, 89, 47, 1, 22, 99], [73, 35, 100, 92, 36, 60, 2, 62], [56, 33, 19, 7, 72, 93, 48, 42], [61, 97, 66, 52], [47, 24, 3, 38], [94, 29, 9, 101, 63, 12, 72, 69]], ![[66, 27, 47, 29, 80, 79, 87, 2], [64, 99, 79, 2, 30, 72, 48, 64], [73, 98, 34, 9, 20, 34, 25, 29], [27, 38, 100, 32], [47, 41, 75, 63], [100, 67, 12, 18, 73, 101, 95, 61]], ![[93, 29, 70, 29, 24, 23, 70, 92], [94, 14, 11, 78, 82, 15, 53, 41], [67, 1, 74, 94, 13, 52, 66, 33], [44, 74, 67, 50], [85, 4, 82, 61], [46, 44, 49, 88, 38, 32, 19, 1]], ![[88, 50, 48, 4, 43, 14, 46, 35], [86, 7, 72, 69, 4, 65, 84, 31], [35, 41, 15, 45, 63, 16, 69, 88], [45, 57, 89, 19], [81, 16, 75, 26], [8, 54, 0, 98, 11, 77, 79, 73]]]
 h' := ![![[36, 1, 48, 81, 20], [11, 76, 18, 89, 74], [99, 94, 16, 87, 12], [93, 71, 29, 71, 63], [98, 51, 95, 93, 67], [0, 0, 0, 1], [0, 1]], ![[75, 27, 59, 45, 34], [78, 102, 12, 38, 12], [77, 28, 36, 65, 72], [79, 2, 62, 81, 62], [100, 73, 7, 62, 84], [12, 8, 3, 60, 48], [36, 1, 48, 81, 20]], ![[44, 98, 24, 74, 1], [47, 89, 40, 76, 71], [27, 76, 7, 46, 23], [46, 25, 33, 10, 4], [20, 41, 27, 42, 54], [95, 29, 79, 9, 28], [75, 27, 59, 45, 34]], ![[54, 79, 75, 6, 48], [59, 90, 77, 44, 35], [1, 80, 6, 8, 12], [102, 9, 18, 44, 62], [55, 23, 18, 65, 16], [98, 65, 46, 30, 79], [44, 98, 24, 74, 1]], ![[0, 1], [14, 55, 59, 62, 14], [27, 31, 38, 0, 87], [91, 99, 64, 0, 15], [75, 18, 59, 47, 88], [101, 1, 78, 3, 51], [54, 79, 75, 6, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 3, 70, 40], [], [], []]
 b := ![[], [19, 60, 12, 93, 101], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 5
  hpos := by decide
  P := [36, 74, 81, 45, 100, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6812712075349, 2420322110451, 1782833897601, 2429646672126, 3289070859267]
  a := ![11, 7, 14, 1, 29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![66142835683, 23498272917, 17309066967, 23588802642, 31932726789]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 11592740743 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀



lemma PB696I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB696I2 : PrimesBelowBoundCertificateInterval O 61 103 696 where
  m := 9
  g := ![2, 2, 2, 2, 4, 3, 2, 2, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB696I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1, I83N2, I83N3]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
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
    · exact ![20151121, 67]
    · exact ![25411681, 71]
    · exact ![28398241, 73]
    · exact ![493039, 6241]
    · exact ![6889, 83, 83, 83]
    · exact ![704969, 89, 89]
    · exact ![88529281, 97]
    · exact ![1030301, 10201]
    · exact ![11592740743]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
      exact NI83N3
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
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
  β := ![I67N1, I71N1, I73N1, I83N1, I83N2, I83N3, I89N1, I89N2, I97N1]
  Il := ![[I67N1], [I71N1], [I73N1], [], [I83N1, I83N2, I83N3], [I89N1, I89N2], [I97N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
