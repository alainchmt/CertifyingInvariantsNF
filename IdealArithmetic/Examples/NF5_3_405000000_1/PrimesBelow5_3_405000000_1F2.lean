
import IdealArithmetic.Examples.NF5_3_405000000_1.RI5_3_405000000_1
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


def P67P0 : CertificateIrreducibleZModOfList' 67 5 2 6 [49, 14, 33, 51, 37, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 39, 28, 49, 58], [40, 36, 32, 46, 40], [58, 40, 54, 36, 66], [38, 18, 20, 3, 37], [0, 1]]
 g := ![![[9, 63, 63, 25, 56], [45, 11, 8, 40, 6], [28, 1, 9, 6], [55, 45, 30, 1], [], []], ![[6, 3, 15, 9, 15, 63, 1, 52], [47, 47, 56, 29, 18, 35, 25, 32], [12, 26], [54, 23, 18, 62], [61, 1, 15, 16], [66, 53, 7, 14]], ![[48, 18, 54, 56, 30, 62, 56, 36], [37, 0, 47, 36, 44, 46, 21, 9], [8, 20, 15, 14], [27, 37, 55, 4], [65, 61, 26, 22], [49, 12, 23, 59]], ![[37, 4, 26, 66, 13, 38, 44, 7], [9, 63, 11, 44, 2, 4, 55, 45], [34, 40, 34, 40], [0, 21, 27, 40], [22, 33, 37, 9], [16, 11, 25, 1]], ![[48, 17, 31, 13, 28, 4, 43, 49], [63, 20, 20, 53, 18, 45, 59, 49], [18, 53, 29, 54], [24, 20, 15, 54], [7, 55, 20, 56], [20, 7, 20, 29]]]
 h' := ![![[28, 39, 28, 49, 58], [6, 34, 38, 8, 18], [59, 34, 19, 13, 41], [52, 40, 38, 65, 26], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[40, 36, 32, 46, 40], [16, 16, 51, 6, 52], [36, 34, 56, 31, 18], [50, 63, 8, 19], [63, 8, 19, 6, 14], [29, 3, 27, 34, 4], [28, 39, 28, 49, 58]], ![[58, 40, 54, 36, 66], [55, 17, 56, 66, 50], [24, 51, 52, 28, 42], [9, 30, 50, 11, 9], [40, 42, 55, 33, 65], [3, 65, 6, 10, 42], [40, 36, 32, 46, 40]], ![[38, 18, 20, 3, 37], [24, 20, 14, 36, 23], [44, 8, 10, 40, 42], [54, 40, 20, 55, 43], [11, 9, 22, 37, 43], [34, 58, 61, 17, 3], [58, 40, 54, 36, 66]], ![[0, 1], [64, 47, 42, 18, 58], [44, 7, 64, 22, 58], [51, 28, 18, 51, 56], [17, 8, 38, 58, 11], [62, 8, 39, 6, 18], [38, 18, 20, 3, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 9, 41, 57], [], [], []]
 b := ![[], [35, 51, 35, 55, 51], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 5
  hpos := by decide
  P := [49, 14, 33, 51, 37, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![292603396089, 99045209704, -1577198026618, 1145866104524, -1033936590336]
  a := ![5, -6, -8, 4, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4367214867, 1478286712, -23540269054, 17102479172, -15431889408]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-472251, 1205715, -206139, 46276, -153872]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-472251, 1205715, -206139, 46276, -153872]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![2, 62, 68, 20, 1]] where
  M :=![![![-472251, 1205715, -206139, 46276, -153872], ![-92552, 235789, -40305, 9053, -30088], ![-18106, 45906, -7844, 1765, -5858], ![-3530, 8856, -1521, 342, -1126], ![-118804, 303584, -51905, 11647, -38741]]]
  hmulB := by decide  
  f := ![![![41, 491, -1061, -60, -382]], ![![120, 1449, -3127, -177, -1124]], ![![354, 4262, -9198, -525, -3310]], ![![1050, 12544, -27103, -1528, -9770]], ![![750, 9006, -19445, -1103, -7001]]]
  g := ![![![-2317, 151349, 144467, 43996, -153872], ![-456, 29595, 28249, 8603, -30088], ![-90, 5762, 5500, 1675, -5858], ![-18, 1108, 1057, 322, -1126], ![-582, 38106, 36373, 11077, -38741]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [28, 43, 27, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 59, 19, 24], [33, 70], [1, 12, 52, 47], [0, 1]]
 g := ![![[9, 61, 14, 37], [47, 65, 26, 15], [32, 25, 22, 8], [43, 3, 25], [1], []], ![[17, 8, 45, 35, 44, 30], [70, 8, 22, 11, 12, 38], [53, 38, 46, 30, 63, 12], [9, 62, 60], [45, 32, 50], [37, 20, 8]], ![[67, 43, 56, 34], [70, 50, 20, 56], [53, 6, 33, 63], [32, 51, 25], [1], []], ![[7, 28, 11, 21, 24, 41], [35, 31, 61, 6, 34, 33], [23, 34, 60, 63, 55, 59], [16, 25, 60], [29, 5, 50], [37, 20, 8]]]
 h' := ![![[32, 59, 19, 24], [33, 12, 68, 26], [27, 19, 21, 21], [6, 49, 22, 24], [43, 28, 44, 66], [0, 0, 1], [0, 1]], ![[33, 70], [58, 0, 42, 27], [23, 45, 51, 55], [6, 24, 55, 6], [20, 59, 6, 42], [59, 63, 58, 11], [32, 59, 19, 24]], ![[1, 12, 52, 47], [4, 18, 15, 45], [40, 65, 41, 50], [1, 37, 55, 47], [51, 55, 46, 5], [24, 5, 1], [33, 70]], ![[0, 1], [14, 41, 17, 44], [0, 13, 29, 16], [54, 32, 10, 65], [17, 0, 46, 29], [30, 3, 11, 60], [1, 12, 52, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [17], []]
 b := ![[], [], [48, 41, 23, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [28, 43, 27, 5, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-876775804, 3817243960, -5245500485, 563379543, 1294245120]
  a := ![-6, -55, 11, -7, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-48806564, -1076421880, -1313438995, -356641167, 1294245120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 491, -1061, -60, -382]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![41, 491, -1061, -60, -382]] 
 ![![71, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![49, 0, 0, 0, 1]] where
  M :=![![![41, 491, -1061, -60, -382], ![120, 1449, -3127, -177, -1124], ![354, 4262, -9198, -525, -3310], ![1050, 12544, -27103, -1528, -9770], ![656, 7910, -17075, -959, -6139]]]
  hmulB := by decide  
  f := ![![![-472251, 1205715, -206139, 46276, -153872]], ![![-134332, 342959, -58635, 13163, -43768]], ![![-173192, 442176, -75598, 16971, -56430]], ![![-319318, 815256, -139383, 31290, -104042]], ![![-327593, 836389, -142996, 32101, -106739]]]
  g := ![![![555, 491, -1061, -60, -382], ![1634, 1449, -3127, -177, -1124], ![4812, 4262, -9198, -525, -3310], ![14182, 12544, -27103, -1528, -9770], ![8919, 7910, -17075, -959, -6139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-472251, 1205715, -206139, 46276, -153872]] ![![41, 491, -1061, -60, -382]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -67, 328, 23, 112]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-49, -67, 328, 23, 112]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![67, 54, 72, 1, 0], ![21, 2, 9, 0, 1]] where
  M :=![![![-49, -67, 328, 23, 112], ![-46, -451, 1010, 58, 362], ![-116, -1378, 2981, 170, 1072], ![-340, -4064, 8780, 497, 3164], ![-222, -2538, 5526, 312, 1987]]]
  hmulB := by decide  
  f := ![![![-163, 1019, -182, 35, -134]], ![![-70, 443, -82, 16, -58]], ![![-32, 194, -31, 2, -20]], ![![-233, 1455, -258, 46, -186]], ![![-53, 331, -59, 11, -43]]]
  g := ![![![-54, -21, -32, 23, 112], ![-158, -59, -88, 58, 362], ![-466, -174, -259, 170, 1072], ![-1371, -510, -760, 497, 3164], ![-861, -320, -477, 312, 1987]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [71, 1, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 47, 69], [71, 25, 4], [0, 1]]
 g := ![![[69, 64, 41], [44, 2], [13, 27], [1, 69, 19], [63, 1], []], ![[37, 52, 11, 2], [35, 49], [16, 48], [52, 43, 38, 18], [26, 41], [48, 16]], ![[55, 15, 72, 48], [28, 41], [34, 1], [11, 70, 41, 6], [24, 19], [40, 16]]]
 h' := ![![[65, 47, 69], [39, 46, 48], [30, 72, 41], [2, 26, 63], [53, 12, 26], [0, 0, 1], [0, 1]], ![[71, 25, 4], [51, 46, 67], [28, 1, 7], [19, 69, 11], [29, 14, 18], [14, 35, 25], [65, 47, 69]], ![[0, 1], [37, 54, 31], [45, 0, 25], [59, 51, 72], [23, 47, 29], [11, 38, 47], [71, 25, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 50], []]
 b := ![[], [72, 5, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [71, 1, 10, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3335, 16056, -21422, -744, 4318]
  a := ![1, -3, -1, 0, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-605, 652, -92, -744, 4318]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-163, 1019, -182, 35, -134]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-163, 1019, -182, 35, -134]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![25, 1, 1, 0, 0], ![48, 24, 0, 1, 0], ![37, 24, 0, 0, 1]] where
  M :=![![![-163, 1019, -182, 35, -134], ![-70, 443, -82, 16, -58], ![-32, 194, -31, 2, -20], ![-4, 52, 20, 5, -28], ![-18, 132, -42, 18, -29]]]
  hmulB := by decide  
  f := ![![![-49, -67, 328, 23, 112]], ![![-46, -451, 1010, 58, 362]], ![![-19, -48, 167, 11, 58]], ![![-52, -248, 668, 41, 236]], ![![-43, -217, 574, 35, 203]]]
  g := ![![![105, 49, -182, 35, -134], ![46, 21, -82, 16, -58], ![19, 9, -31, 2, -20], ![4, 8, 20, 5, -28], ![17, 6, -42, 18, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [34, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 72], [0, 1]]
 g := ![![[27, 25], [25], [64], [44, 37], [12], [1]], ![[72, 48], [25], [64], [23, 36], [12], [1]]]
 h' := ![![[31, 72], [42, 5], [69, 5], [37, 65], [18, 16], [39, 31], [0, 1]], ![[0, 1], [51, 68], [5, 68], [8, 8], [3, 57], [51, 42], [31, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [18, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [34, 42, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4756, -31733, 55097, -8706, -1415]
  a := ![-8, 28, 13, -9, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12362, 2138, 55097, -8706, -1415]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-49, -67, 328, 23, 112]] ![![-163, 1019, -182, 35, -134]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -28, -7, 5, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![13, -28, -7, 5, 0]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![50, 26, 46, 1, 0], ![28, 55, 23, 0, 1]] where
  M :=![![![13, -28, -7, 5, 0], ![-10, 23, -13, -17, 30], ![34, -164, 242, -39, -42], ![78, 124, -659, 404, -318], ![-118, 466, -593, 23, 203]]]
  hmulB := by decide  
  f := ![![![399, -2476, 441, -85, 324]], ![![170, -1067, 185, -37, 138]], ![![74, -456, 64, -17, 54]], ![![352, -2186, 377, -76, 282]], ![![282, -1757, 304, -61, 227]]]
  g := ![![![-3, -2, -3, 5, 0], ![0, -15, 1, -17, 30], ![40, 40, 38, -39, -42], ![-142, 90, -151, 404, -318], ![-88, -143, -80, 23, 203]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [43, 54, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 3, 25], [63, 75, 54], [0, 1]]
 g := ![![[67, 72, 65], [59, 24, 19], [66, 19, 8], [67, 19, 21], [26, 1], []], ![[64, 28, 77, 21], [59, 48, 48, 8], [67, 40, 48, 2], [76, 50, 69, 4], [22, 16], [47, 72]], ![[21, 71, 5, 28], [25, 61, 50, 27], [42, 56, 57, 75], [22, 52, 60, 61], [57, 9], [18, 72]]]
 h' := ![![[42, 3, 25], [70, 5, 12], [6, 69, 63], [42, 54, 18], [67, 54, 69], [0, 0, 1], [0, 1]], ![[63, 75, 54], [40, 53, 77], [64, 51, 51], [54, 61, 14], [7, 25, 47], [59, 69, 75], [42, 3, 25]], ![[0, 1], [15, 21, 69], [1, 38, 44], [45, 43, 47], [38, 0, 42], [35, 10, 3], [63, 75, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 2], []]
 b := ![[], [62, 29, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [43, 54, 53, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9230805, -1316078, 46370766, -36546272, 31736730]
  a := ![10, -11, -15, 12, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11765245, -10083964, 12627272, -36546272, 31736730]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![399, -2476, 441, -85, 324]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![399, -2476, 441, -85, 324]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![41, 33, 1, 0, 0], ![69, 58, 0, 1, 0], ![14, 38, 0, 0, 1]] where
  M :=![![![399, -2476, 441, -85, 324], ![170, -1067, 185, -37, 138], ![74, -456, 64, -17, 54], ![34, -176, -21, -10, 6], ![54, -302, 21, -13, 29]]]
  hmulB := by decide  
  f := ![![![13, -28, -7, 5, 0]], ![![-10, 23, -13, -17, 30]], ![![3, -7, -6, -5, 12]], ![![5, -6, -24, -3, 18]], ![![-4, 12, -15, -7, 17]]]
  g := ![![![-207, -309, 441, -85, 324], ![-86, -130, 185, -37, 138], ![-27, -46, 64, -17, 54], ![19, 11, -21, -10, 6], ![-4, -17, 21, -13, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [73, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 78], [0, 1]]
 g := ![![[6, 13], [51, 18], [34, 49], [30, 16], [32], [1]], ![[0, 66], [67, 61], [60, 30], [53, 63], [32], [1]]]
 h' := ![![[36, 78], [69, 31], [46, 27], [22, 72], [70, 4], [6, 36], [0, 1]], ![[0, 1], [0, 48], [70, 52], [7, 7], [56, 75], [38, 43], [36, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [74, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [73, 43, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9883, -28546, 24138, 7696, -20670]
  a := ![-6, 6, 10, -16, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15461, -6152, 24138, 7696, -20670]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![13, -28, -7, 5, 0]] ![![399, -2476, 441, -85, 324]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0, 0, 0]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]] where
  M :=![![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 5 2 6 [37, 66, 6, 49, 43, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 9, 36, 52, 30], [10, 57, 46, 37, 42], [17, 32, 7, 44, 67], [7, 67, 77, 33, 27], [0, 1]]
 g := ![![[29, 63, 53, 25, 38], [46, 32, 29, 5, 11], [14, 8, 72, 63], [18, 65, 71, 23], [1], []], ![[51, 60, 54, 60, 66, 27, 5, 31], [12, 24, 35, 4, 5, 34, 61, 29], [44, 81, 34, 30], [29, 43, 44, 70], [53, 5, 68, 2, 2, 47, 74, 41], [15, 24, 27, 70]], ![[76, 65, 8, 46, 73, 15, 26, 18], [22, 42, 58, 49, 54, 27, 44, 79], [50, 80, 76, 75], [36, 39, 28, 69], [41, 65, 47, 77, 2, 79, 51, 72], [40, 25, 47, 21]], ![[43, 0, 37, 0, 30, 68, 32, 18], [69, 17, 1, 23, 76, 78, 18, 66], [37, 7, 25, 49], [34, 49, 13, 28], [38, 35, 77, 43, 55, 49, 13, 57], [57, 73, 34, 7]], ![[28, 43, 32, 8, 12, 54, 80, 36], [1, 36, 10, 2, 79, 34, 24, 3], [82, 12, 21, 78], [10, 55, 63, 9], [61, 61, 59, 63, 35, 62, 34, 81], [15, 54, 66, 65]]]
 h' := ![![[6, 9, 36, 52, 30], [41, 62, 60, 34, 72], [7, 44, 5, 49, 54], [39, 46, 16, 16, 48], [46, 17, 77, 34, 40], [0, 0, 1], [0, 1]], ![[10, 57, 46, 37, 42], [74, 79, 60, 21, 55], [60, 62, 67, 9, 31], [32, 40, 25, 12, 69], [21, 35, 74, 26, 30], [62, 56, 81, 5, 56], [6, 9, 36, 52, 30]], ![[17, 32, 7, 44, 67], [3, 5, 10, 22, 6], [16, 59, 20, 46, 65], [17, 76, 58, 11, 18], [42, 77, 30, 47, 61], [31, 65, 42, 78, 71], [10, 57, 46, 37, 42]], ![[7, 67, 77, 33, 27], [29, 2, 41, 3, 14], [75, 26, 47, 58, 44], [38, 61, 46, 10, 7], [36, 18, 1, 67, 32], [6, 20, 73, 28, 26], [17, 32, 7, 44, 67]], ![[0, 1], [27, 18, 78, 3, 19], [41, 58, 27, 4, 55], [2, 26, 21, 34, 24], [17, 19, 67, 75, 3], [75, 25, 52, 55, 13], [7, 67, 77, 33, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 82, 72, 63], [], [], []]
 b := ![[], [51, 18, 73, 62, 56], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 5
  hpos := by decide
  P := [37, 66, 6, 49, 43, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18583687563529, 45322960772635, -25907164108722, -20581794738306, 43123100201047]
  a := ![-6, 18, 16, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-223899850163, 546059768345, -312134507334, -247973430582, 519555424109]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 3939040643 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10733, -68941, 12349, -2356, 9046]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![10733, -68941, 12349, -2356, 9046]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![75, 80, 55, 1, 0], ![64, 33, 62, 0, 1]] where
  M :=![![![10733, -68941, 12349, -2356, 9046], ![4712, -30163, 5405, -1031, 3956], ![2062, -13174, 2348, -445, 1726], ![890, -5732, 1025, -214, 782], ![1344, -8694, 1593, -309, 1141]]]
  hmulB := by decide  
  f := ![![![-233, -2771, 5993, 340, 2156]], ![![-680, -8177, 17653, 1001, 6352]], ![![-2002, -24086, 51994, 2947, 18710]], ![![-2111, -25367, 54770, 3105, 19708]], ![![-1856, -22305, 48158, 2730, 17329]]]
  g := ![![![-4399, -2011, -4707, -2356, 9046], ![-1923, -879, -2058, -1031, 3956], ![-843, -388, -901, -445, 1726], ![-372, -162, -401, -214, 782], ![-545, -243, -586, -309, 1141]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [50, 84, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 77, 55], [19, 11, 34], [0, 1]]
 g := ![![[44, 48, 88], [87, 88], [42, 42], [48, 40, 67], [72, 44, 1], []], ![[12, 43, 2, 44], [77, 9], [14, 64], [62, 41, 70, 57], [6, 22, 82, 69], [60, 88]], ![[86, 17, 5, 67], [7, 71], [23, 45], [67, 73, 15, 34], [9, 26, 14, 1], [81, 88]]]
 h' := ![![[25, 77, 55], [78, 38, 34], [45, 87, 34], [3, 18, 24], [49, 29, 45], [0, 0, 1], [0, 1]], ![[19, 11, 34], [22, 33, 61], [57, 68, 86], [57, 14, 8], [76, 61, 43], [28, 17, 11], [25, 77, 55]], ![[0, 1], [63, 18, 83], [71, 23, 58], [8, 57, 57], [46, 88, 1], [49, 72, 77], [19, 11, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 76], []]
 b := ![[], [19, 29, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [50, 84, 45, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6908, 184306, -416650, 157836, -57268]
  a := ![-2, -2, 3, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-91904, -118570, -62326, 157836, -57268]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -58, 23, -3, 14]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![7, -58, 23, -3, 14]] 
 ![![89, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![74, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![7, -58, 23, -3, 14], ![6, -55, 59, 1, 10], ![-2, -32, 38, 37, 26], ![-74, -32, 313, -88, 274], ![6, -220, 435, -59, 83]]]
  hmulB := by decide  
  f := ![![![85617379, -218974186, 37442789, -8401675, 27947530]], ![![13656704, -34928255, 5972445, -1340139, 4457870]], ![![68338559, -174782042, 29886295, -6706096, 22307316]], ![![71194756, -182087024, 31135387, -6986376, 23239646]], ![![32949628, -84271652, 14409761, -3233363, 10755535]]]
  g := ![![![-12, -58, 23, -3, 14], ![-43, -55, 59, 1, 10], ![-66, -32, 38, 37, 26], ![-277, -32, 313, -88, 274], ![-295, -220, 435, -59, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![433, -1442, 251, -53, 186]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![433, -1442, 251, -53, 186]] 
 ![![89, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![79, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![433, -1442, 251, -53, 186], ![106, -417, 73, -15, 54], ![30, -140, 24, -5, 18], ![10, -52, 7, -2, 6], ![98, -292, 49, -11, 37]]]
  hmulB := by decide  
  f := ![![![-11, 22, -7, -21, 30]], ![![-2, 3, 1, -5, 6]], ![![-5, 14, -13, -6, 12]], ![![-19, 42, -18, -31, 48]], ![![-5, -2, 26, -22, 19]]]
  g := ![![![155, -1442, 251, -53, 186], ![44, -417, 73, -15, 54], ![15, -140, 24, -5, 18], ![7, -52, 7, -2, 6], ![33, -292, 49, -11, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![10733, -68941, 12349, -2356, 9046]] ![![7, -58, 23, -3, 14]]
  ![![-134593, 859345, -153816, 29387, -112800]] where
 M := ![![![-134593, 859345, -153816, 29387, -112800]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![-134593, 859345, -153816, 29387, -112800]] ![![433, -1442, 251, -53, 186]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![17436791, -111320043, 19936267, -3805640, 14604366]]]
 hmul := by decide  
 g := ![![![![195919, -1250787, 224003, -42760, 164094]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21877, 56290, -9635, 2157, -7188]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-21877, 56290, -9635, 2157, -7188]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![44, 94, 42, 85, 1]] where
  M :=![![![-21877, 56290, -9635, 2157, -7188], ![-4314, 11189, -1931, 427, -1434], ![-854, 2276, -436, 83, -306], ![-166, 536, -229, 10, -114], ![-5486, 14126, -2503, 535, -1831]]]
  hmulB := by decide  
  f := ![![![-1, 6, -5, 1, 0]], ![![-2, 1, 9, -7, 6]], ![![14, -40, 34, 11, -30]], ![![-22, 156, -277, 72, 6]], ![![-16, 124, -222, 61, -1]]]
  g := ![![![3035, 7546, 3013, 6321, -7188], ![606, 1505, 601, 1261, -1434], ![130, 320, 128, 269, -306], ![50, 116, 47, 100, -114], ![774, 1920, 767, 1610, -1831]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [15, 59, 59, 28, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 63, 49, 46], [30, 72, 8, 89], [6, 58, 40, 59], [0, 1]]
 g := ![![[56, 31, 89, 27], [28, 94, 66], [85, 13, 89], [60, 52, 2], [46, 69, 1], []], ![[65, 82, 36, 77], [15, 22, 48], [85, 66, 2], [59, 58, 2], [32, 34, 48], [81, 68, 86, 89, 71, 45]], ![[94, 80, 11, 20, 59, 91], [93], [64, 24, 50], [17, 67, 81], [69, 4, 53], [8, 38, 9, 48, 61, 70]], ![[30, 34, 12, 95, 22, 10], [82, 89, 1], [75, 43, 75], [13, 14, 70], [61, 38, 11], [41, 33, 92, 11, 71, 30]]]
 h' := ![![[33, 63, 49, 46], [90, 68, 6, 30], [92, 75, 5, 39], [94, 73, 73, 63], [86, 34, 87, 14], [0, 0, 0, 1], [0, 1]], ![[30, 72, 8, 89], [2, 1, 28], [18, 23, 29, 57], [41, 12, 39, 14], [21, 60, 11, 14], [93, 8, 24, 57], [33, 63, 49, 46]], ![[6, 58, 40, 59], [59, 37, 56, 5], [75, 42, 53], [68, 35, 85, 70], [56, 78, 5, 88], [11, 37, 20, 76], [30, 72, 8, 89]], ![[0, 1], [47, 88, 7, 62], [93, 54, 10, 1], [32, 74, 94, 47], [79, 22, 91, 78], [86, 52, 53, 60], [6, 58, 40, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [78, 17, 3], []]
 b := ![[], [], [16, 88, 13, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [15, 59, 59, 28, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-32357367495, 83707901775, -55112219904, -34665277986, 72840634875]
  a := ![-10, 13, 20, -14, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-33374693835, -69724863675, -32107411182, -64186796313, 72840634875]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 6, -5, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-1, 6, -5, 1, 0]] 
 ![![97, 0, 0, 0, 0], ![70, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![-1, 6, -5, 1, 0], ![-2, 1, 9, -7, 6], ![14, -40, 34, 11, -30], ![-22, 156, -277, 72, 6], ![-38, 90, -43, -51, 89]]]
  hmulB := by decide  
  f := ![![![-21877, 56290, -9635, 2157, -7188]], ![![-15832, 40737, -6973, 1561, -5202]], ![![-10609, 27298, -4673, 1046, -3486]], ![![-1806, 4648, -797, 178, -594]], ![![-9078, 23358, -3999, 895, -2983]]]
  g := ![![![-2, 6, -5, 1, 0], ![-7, 1, 9, -7, 6], ![24, -40, 34, 11, -30], ![13, 156, -277, 72, 6], ![-77, 90, -43, -51, 89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-21877, 56290, -9635, 2157, -7188]] ![![-1, 6, -5, 1, 0]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]] where
  M :=![![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 5 2 6 [42, 53, 94, 52, 12, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 46, 61, 75, 69], [33, 50, 92, 42, 30], [3, 51, 31, 49, 43], [42, 54, 18, 36, 60], [0, 1]]
 g := ![![[31, 18, 57, 57, 13], [75, 57, 75, 84], [89, 75, 100, 39, 19], [84, 86, 93, 81], [89, 1], []], ![[71, 88, 97, 32, 14, 86, 44, 15], [98, 67, 57, 16], [40, 60, 49, 86, 29, 20, 18, 11], [26, 36], [8, 58, 79, 16], [70, 74, 58, 88, 47, 50, 42, 57]], ![[24, 36, 91, 45, 42, 70, 77, 33], [2, 43, 52, 49], [86, 46, 62, 4, 90, 82, 82, 95], [79, 43, 66, 77], [12, 97, 13, 19], [96, 82, 82, 0, 58, 8, 86, 33]], ![[77, 47, 33, 58, 34, 47, 47, 23], [62, 17, 56, 76], [3, 46, 29, 15, 64, 1, 36, 77], [41, 0, 100, 56], [65, 16, 80, 56], [72, 13, 43, 14, 27, 97, 75, 20]], ![[84, 14, 59, 72, 90, 9, 30, 10], [16, 68, 40, 9], [55, 23, 34, 95, 20, 99, 2, 40], [31, 90, 78, 21], [58, 88, 30, 64], [63, 66, 25, 25, 54, 88, 14, 62]]]
 h' := ![![[11, 46, 61, 75, 69], [83, 46, 67, 59, 66], [100, 75, 57, 6, 65], [8, 40, 16, 29, 76], [100, 89, 65, 25, 92], [0, 0, 0, 1], [0, 1]], ![[33, 50, 92, 42, 30], [44, 25, 26, 35, 98], [76, 7, 69, 32, 97], [73, 41, 92, 71, 59], [16, 19, 55, 6], [7, 83, 51, 97, 4], [11, 46, 61, 75, 69]], ![[3, 51, 31, 49, 43], [94, 16, 54, 8, 71], [73, 81, 62, 12, 94], [52, 28, 11, 64, 90], [21, 64, 94, 79, 28], [90, 86, 91, 23, 25], [33, 50, 92, 42, 30]], ![[42, 54, 18, 36, 60], [53, 14, 6, 66, 24], [58, 5, 52, 42, 50], [14, 31, 98, 57, 65], [76, 65, 77, 66, 64], [33, 45, 35, 69, 64], [3, 51, 31, 49, 43]], ![[0, 1], [36, 0, 49, 34, 44], [1, 34, 63, 9, 98], [12, 62, 86, 82, 13], [1, 66, 12, 26, 18], [35, 89, 25, 12, 8], [42, 54, 18, 36, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 3, 80, 83], [], [], []]
 b := ![[], [19, 23, 59, 40, 31], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 5
  hpos := by decide
  P := [42, 53, 94, 52, 12, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6108109936, -5063860232727, 12269050021992, -4942220133509, 2197539961804]
  a := ![-6, 8, 9, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![60476336, -50137230027, 121475742792, -48932872609, 21757821404]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10510100501 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10787, 27612, -4764, 1056, -3538]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-10787, 27612, -4764, 1056, -3538]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![54, 7, 1, 0, 0], ![34, 5, 0, 1, 0], ![42, 67, 0, 0, 1]] where
  M :=![![![-10787, 27612, -4764, 1056, -3538], ![-2112, 5477, -1062, 200, -740], ![-400, 1248, -583, 18, -280], ![-36, 756, -1218, -59, -452], ![-2684, 7282, -1930, 224, -1153]]]
  hmulB := by decide  
  f := ![![![75, -424, 40, 16, 26]], ![![-32, 3, -142, -44, 148]], ![![38, -229, 23, 2, 24]], ![![30, -147, -8, 21, -4]], ![![6, -151, -108, -16, 111]]]
  g := ![![![3487, 2842, -4764, 1056, -3538], ![772, 597, -1062, 200, -740], ![410, 233, -583, 18, -280], ![842, 387, -1218, -59, -452], ![1382, 941, -1930, 224, -1153]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [31, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 102], [0, 1]]
 g := ![![[39, 81], [26, 98], [81, 58], [32], [14], [27, 1]], ![[63, 22], [97, 5], [102, 45], [32], [14], [54, 102]]]
 h' := ![![[27, 102], [18, 9], [64, 60], [17, 26], [44, 49], [90, 80], [0, 1]], ![[0, 1], [55, 94], [36, 43], [101, 77], [28, 54], [87, 23], [27, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [93, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [31, 76, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-390, -4375, 12230, -3378, 3893]
  a := ![-3, 7, 6, -2, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6888, -3242, 12230, -3378, 3893]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, 167, -8, 7, -14]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-29, 167, -8, 7, -14]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![101, 54, 1, 0, 0], ![5, 69, 0, 1, 0], ![94, 80, 0, 0, 1]] where
  M :=![![![-29, 167, -8, 7, -14], ![-14, 41, 62, 6, 14], ![-12, -58, 185, 22, 64], ![-44, -224, 584, 13, 260], ![-18, -180, 438, 0, 145]]]
  hmulB := by decide  
  f := ![![![378223, -967333, 165406, -37115, 123460]], ![![74230, -189847, 32462, -7284, 24230]], ![![409937, -1048443, 179275, -40227, 133812]], ![![68115, -174208, 29788, -6684, 22234]], ![![403752, -1032624, 176570, -39620, 131793]]]
  g := ![![![20, 12, -8, 7, -14], ![-74, -47, 62, 6, 14], ![-241, -162, 185, 22, 64], ![-811, -519, 584, 13, 260], ![-562, -344, 438, 0, 145]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [55, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 102], [0, 1]]
 g := ![![[32, 15], [61, 64], [50, 17], [83], [58], [94, 1]], ![[0, 88], [0, 39], [0, 86], [83], [58], [85, 102]]]
 h' := ![![[94, 102], [44, 85], [31, 95], [48, 74], [94, 86], [83, 26], [0, 1]], ![[0, 1], [0, 18], [0, 8], [0, 29], [41, 17], [55, 77], [94, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [26, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [55, 9, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14691, -75710, 110852, -8344, -15692]
  a := ![16, -7, -33, 16, -41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-93831, -41074, 110852, -8344, -15692]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, -139, 22, -5, 18]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![57, -139, 22, -5, 18]] 
 ![![103, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![90, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![57, -139, 22, -5, 18], ![10, -25, 8, -4, 6], ![8, -22, 17, 4, -12], ![-8, 64, -118, 33, 0], ![-2, 4, -16, -22, 43]]]
  hmulB := by decide  
  f := ![![![-643, -7271, 16040, 917, 5760]], ![![-280, -3177, 7000, 400, 2514]], ![![-614, -6980, 15369, 878, 5520]], ![![-347, -4035, 8814, 502, 3168]], ![![-365, -4197, 9204, 525, 3307]]]
  g := ![![![32, -139, 22, -5, 18], ![2, -25, 8, -4, 6], ![-2, -22, 17, 4, -12], ![67, 64, -118, 33, 0], ![1, 4, -16, -22, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-10787, 27612, -4764, 1056, -3538]] ![![-29, 167, -8, 7, -14]]
  ![![643, 7271, -16040, -917, -5760]] where
 M := ![![![643, 7271, -16040, -917, -5760]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![643, 7271, -16040, -917, -5760]] ![![57, -139, 22, -5, 18]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)


lemma PB984I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB984I2 : PrimesBelowBoundCertificateInterval O 61 103 984 where
  m := 9
  g := ![1, 2, 2, 2, 1, 3, 2, 1, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB984I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N2]
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
    · exact ![25411681, 71]
    · exact ![389017, 5329]
    · exact ![493039, 6241]
    · exact ![3939040643]
    · exact ![704969, 89, 89]
    · exact ![88529281, 97]
    · exact ![10510100501]
    · exact ![10609, 10609, 103]
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
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
  β := ![I71N1, I89N1, I89N2, I97N1, I103N2]
  Il := ![[], [I71N1], [], [], [], [I89N1, I89N2], [I97N1], [], [I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
