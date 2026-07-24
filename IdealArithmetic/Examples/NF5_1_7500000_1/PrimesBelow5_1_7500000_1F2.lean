
import IdealArithmetic.Examples.NF5_1_7500000_1.RI5_1_7500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, -24, 15, -7, 11]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-33, -24, 15, -7, 11]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![21, 39, 1, 0, 0], ![26, 21, 0, 1, 0], ![58, 25, 0, 0, 1]] where
  M :=![![![-33, -24, 15, -7, 11], ![44, 26, -17, 8, -14], ![-56, -29, 18, -6, 16], ![10, 0, -3, -2, 1], ![-26, -9, 10, -7, 6]]]
  hmulB := by decide  
  f := ![![![-11, -30, -15, -5, -9]], ![![-36, -62, -25, -12, -10]], ![![-25, -47, -20, -9, -9]], ![![-16, -32, -14, -6, -7]], ![![-24, -51, -23, -9, -12]]]
  g := ![![![-12, -11, 15, -7, 11], ![15, 13, -17, 8, -14], ![-18, -15, 18, -6, 16], ![1, 2, -3, -2, 1], ![-6, -6, 10, -7, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [63, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 66], [0, 1]]
 g := ![![[60, 49], [16, 35], [15], [1], [47], [1]], ![[28, 18], [41, 32], [15], [1], [47], [1]]]
 h' := ![![[39, 66], [64, 7], [28, 13], [13, 45], [3, 1], [4, 39], [0, 1]], ![[0, 1], [2, 60], [66, 54], [26, 22], [42, 66], [51, 28], [39, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [7, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [63, 28, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-429, -652, -487, 656, 598]
  a := ![0, -2, 2, -3, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-626, -155, -487, 656, 598]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 154, -95, 43, -71]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![211, 154, -95, 43, -71]] 
 ![![67, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![211, 154, -95, 43, -71], ![-284, -168, 111, -48, 86], ![344, 171, -120, 50, -96], ![-50, 4, 5, 0, 7], ![186, 77, -58, 23, -48]]]
  hmulB := by decide  
  f := ![![![-31, -4, 15, 57, 17]], ![![-5, 0, 2, 11, 5]], ![![-8, 5, 8, 22, 8]], ![![-10, 2, 11, 18, -1]], ![![-18, -7, 6, 27, 6]]]
  g := ![![![27, 154, -95, 43, -71], ![-36, -168, 111, -48, 86], ![43, 171, -120, 50, -96], ![-6, 4, 5, 0, 7], ![23, 77, -58, 23, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 9, -10, -15, 9]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![17, 9, -10, -15, 9]] 
 ![![67, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![17, 9, -10, -15, 9], ![36, 43, 24, -38, -30], ![-120, -60, 81, 108, -76], ![-170, -193, -96, 176, 123], ![186, 83, -144, -165, 138]]]
  hmulB := by decide  
  f := ![![![-549, -1169, -330, -257, -171]], ![![-297, -634, -186, -139, -97]], ![![-424, -892, -255, -196, -132]], ![![-399, -852, -246, -187, -128]], ![![-351, -738, -214, -162, -111]]]
  g := ![![![8, 9, -10, -15, 9], ![5, 43, 24, -38, -30], ![-60, -60, 81, 108, -76], ![-28, -193, -96, 176, 123], ![98, 83, -144, -165, 138]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2

def I67N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, 1, 1, -1]] i)))

def SI67N3: IdealEqSpanCertificate' Table ![![-1, 0, 1, 1, -1]] 
 ![![67, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![-1, 0, 1, 1, -1], ![-4, -4, -1, 4, 2], ![8, 3, -8, -6, 8], ![18, 18, 5, -18, -7], ![-10, -1, 14, 9, -14]]]
  hmulB := by decide  
  f := ![![![-283, -26, 63, -13, 59]], ![![-195, -18, 44, -9, 41]], ![![-10, 1, 2, 0, 2]], ![![-128, -12, 29, -6, 27]], ![![-139, -11, 31, -6, 29]]]
  g := ![![![0, 0, 1, 1, -1], ![0, -4, -1, 4, 2], ![-3, 3, -8, -6, 8], ![-1, 18, 5, -18, -7], ![3, -1, 14, 9, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N3 : Nat.card (O ⧸ I67N3) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N3)

lemma isPrimeI67N3 : Ideal.IsPrime I67N3 := prime_ideal_of_norm_prime hp67.out _ NI67N3
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-33, -24, 15, -7, 11]] ![![211, 154, -95, 43, -71]]
  ![![7409, 2334, -2002, 736, -1738]] where
 M := ![![![7409, 2334, -2002, 736, -1738]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![7409, 2334, -2002, 736, -1738]] ![![17, 9, -10, -15, 9]]
  ![![1829, 861, -620, 263, -503]] where
 M := ![![![1829, 861, -620, 263, -503]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N2 : IdealMulLeCertificate' Table 
  ![![1829, 861, -620, 263, -503]] ![![-1, 0, 1, 1, -1]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-469, -67, 201, -268, 134]]]
 hmul := by decide  
 g := ![![![![-7, -1, 3, -4, 2]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2, I67N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
    exact isPrimeI67N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1 ⊙ MulI67N2)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 6, 6, 2, 2]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![3, 6, 6, 2, 2]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![36, 19, 69, 1, 0], ![1, 55, 5, 0, 1]] where
  M :=![![![3, 6, 6, 2, 2], ![8, 17, 4, 8, 4], ![16, 28, 9, 0, 16], ![28, 36, 12, -11, -2], ![4, 30, 28, 14, -3]]]
  hmulB := by decide  
  f := ![![![29, 6, -6, 2, -6]], ![![-24, -1, 4, 0, 4]], ![![16, -4, -1, 0, 0]], ![![24, -1, -3, 1, -2]], ![![-17, -1, 3, 0, 3]]]
  g := ![![![-1, -2, -2, 2, 2], ![-4, -5, -8, 8, 4], ![0, -12, -1, 0, 16], ![6, 5, 11, -11, -2], ![-7, -1, -13, 14, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [45, 68, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 69, 69], [13, 1, 2], [0, 1]]
 g := ![![[21, 10, 16], [34, 22, 29], [5, 14, 38], [15, 27], [62, 1], []], ![[2, 51, 4, 69], [14, 46, 48, 53], [8, 1, 22, 55], [40, 12], [65, 1], [43, 4]], ![[66, 28, 20, 50], [27, 20, 68, 54], [25, 23, 54, 27], [56, 3], [41, 4], [39, 4]]]
 h' := ![![[49, 69, 69], [32, 37, 4], [59, 39, 10], [50, 8, 40], [50, 70, 13], [0, 0, 1], [0, 1]], ![[13, 1, 2], [17, 3, 1], [27, 8, 3], [54, 44, 24], [24, 57, 15], [40, 37, 1], [49, 69, 69]], ![[0, 1], [62, 31, 66], [42, 24, 58], [46, 19, 7], [9, 15, 43], [47, 34, 69], [13, 1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 25], []]
 b := ![[], [13, 50, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [45, 68, 9, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17344007, -12543063, 5908535, 13102770, -6272340]
  a := ![3, -65, -1, -66, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6799597, 1175817, -12208745, 13102770, -6272340]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -3, 2, -1, 1]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-3, -3, 2, -1, 1]] 
 ![![71, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-3, -3, 2, -1, 1], ![4, 3, -2, 2, -2], ![-8, -6, 1, 0, 4], ![6, 3, -2, -4, 1], ![-2, 1, 4, -3, -2]]]
  hmulB := by decide  
  f := ![![![3, -61, -42, -11, -27]], ![![0, -33, -22, -6, -14]], ![![1, -49, -33, -9, -21]], ![![0, -21, -14, -4, -9]], ![![-1, -22, -14, -4, -9]]]
  g := ![![![0, -3, 2, -1, 1], ![0, 3, -2, 2, -2], ![1, -6, 1, 0, 4], ![1, 3, -2, -4, 1], ![-2, 1, 4, -3, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -3, 4, -1, 3]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-9, -3, 4, -1, 3]] 
 ![![71, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-9, -3, 4, -1, 3], ![12, 7, -2, 2, -2], ![-8, 2, 5, 0, 4], ![2, 3, 2, 0, 1], ![-2, 5, 4, 1, 2]]]
  hmulB := by decide  
  f := ![![![25, 19, -4, 5, -13]], ![![13, 10, -2, 3, -7]], ![![15, 11, -3, 3, -7]], ![![13, 10, -2, 1, -6]], ![![6, 5, 0, 1, -4]]]
  g := ![![![-1, -3, 4, -1, 3], ![-3, 7, -2, 2, -2], ![-5, 2, 5, 0, 4], ![-3, 3, 2, 0, 1], ![-6, 5, 4, 1, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![3, 6, 6, 2, 2]] ![![-3, -3, 2, -1, 1]]
  ![![-25, -19, 4, -5, 13]] where
 M := ![![![-25, -19, 4, -5, 13]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-25, -19, 4, -5, 13]] ![![-9, -3, 4, -1, 3]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![-71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-265, -331, -207, 280, 254]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-265, -331, -207, 280, 254]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![55, 26, 65, 8, 1]] where
  M :=![![![-265, -331, -207, 280, 254], ![1016, 544, -611, -922, 560], ![2240, 2645, 1466, -2342, -1844], ![-4196, -2107, 2799, 3771, -2622], ![-4124, -4620, -2206, 4250, 2849]]]
  hmulB := by decide  
  f := ![![![207, -17, -23, 0, -30]], ![![-120, 64, -17, 14, 0]], ![![0, -137, 50, -34, 28]], ![![116, 49, -43, 15, -34]], ![![125, -108, 17, -24, -1]]]
  g := ![![![-195, -95, -229, -24, 254], ![-408, -192, -507, -74, 560], ![1420, 693, 1662, 170, -1844], ![1918, 905, 2373, 339, -2622], ![-2203, -1078, -2567, -254, 2849]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 4 2 6 [18, 60, 0, 27, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 13, 31, 46], [49, 43, 46, 68], [65, 16, 69, 32], [0, 1]]
 g := ![![[20, 18, 41, 27], [72, 36, 38], [61, 65, 35], [30, 29, 27, 72], [1], []], ![[22, 66, 0, 27, 51, 64], [7, 35, 19], [69, 33, 61], [14, 13, 59, 2, 24, 6], [55, 50, 25], [52, 32, 72]], ![[5, 55, 61, 14, 29, 34], [39, 55, 8], [17, 35, 27], [4, 18, 11, 45, 62, 10], [59, 45, 64], [65, 33, 25]], ![[70, 0, 9, 53, 7, 27], [21, 5, 72], [55, 37, 16], [72, 20, 50, 11, 44, 72], [67, 22, 23], [66, 55, 2]]]
 h' := ![![[5, 13, 31, 46], [2, 6, 71, 63], [35, 21, 27, 44], [44, 46, 7, 20], [55, 13, 0, 46], [0, 0, 1], [0, 1]], ![[49, 43, 46, 68], [4, 2, 20, 66], [35, 63, 40, 47], [6, 53, 44, 39], [16, 67, 67, 4], [38, 11, 37, 68], [5, 13, 31, 46]], ![[65, 16, 69, 32], [63, 33, 66, 57], [53, 9, 11, 9], [33, 55, 9, 10], [60, 9, 23, 61], [63, 12, 58, 65], [49, 43, 46, 68]], ![[0, 1], [68, 32, 62, 33], [64, 53, 68, 46], [18, 65, 13, 4], [0, 57, 56, 35], [44, 50, 50, 13], [65, 16, 69, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [63, 53, 18], []]
 b := ![[], [], [32, 16, 65, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 4
  hpos := by decide
  P := [18, 60, 0, 27, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![566768, 1100497, 1203533, -679612, -1367744]
  a := ![1, -4, 1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1038256, 502217, 1234341, 140580, -1367744]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 28398241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-207, 17, 23, 0, 30]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-207, 17, 23, 0, 30]] 
 ![![73, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![-207, 17, 23, 0, 30], ![120, -64, 17, -14, 0], ![0, 137, -50, 34, -28], ![-116, -49, 43, -15, 34], ![68, 100, -42, 26, -29]]]
  hmulB := by decide  
  f := ![![![265, 331, 207, -280, -254]], ![![193, 251, 170, -206, -206]], ![![100, 127, 82, -106, -100]], ![![72, 47, -27, -67, 22]], ![![238, 290, 172, -250, -213]]]
  g := ![![![-48, 17, 23, 0, 30], ![44, -64, 17, -14, 0], ![-65, 137, -50, 34, -28], ![-7, -49, 43, -15, 34], ![-38, 100, -42, 26, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-265, -331, -207, 280, 254]] ![![-207, 17, 23, 0, 30]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-783, -581, 357, -162, 266]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-783, -581, 357, -162, 266]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![43, 57, 1, 0, 0], ![78, 17, 0, 1, 0], ![51, 57, 0, 0, 1]] where
  M :=![![![-783, -581, 357, -162, 266], ![1064, 638, -419, 182, -324], ![-1296, -651, 456, -190, 364], ![196, -11, -21, 1, -28], ![-704, -294, 222, -88, 183]]]
  hmulB := by decide  
  f := ![![![31, 51, 27, -10, -10]], ![![-40, 18, 61, 74, -20]], ![![-13, 40, 58, 50, -18]], ![![26, 57, 38, 3, -12]], ![![-5, 51, 64, 44, -23]]]
  g := ![![![-216, -422, 357, -162, 266], ![271, 505, -419, 182, -324], ![-312, -559, 456, -190, 364], ![31, 35, -21, 1, -28], ![-161, -277, 222, -88, 183]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [45, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 78], [0, 1]]
 g := ![![[11, 72], [41, 26], [63, 5], [18, 23], [46], [1]], ![[0, 7], [48, 53], [37, 74], [9, 56], [46], [1]]]
 h' := ![![[58, 78], [51, 25], [9, 37], [59, 59], [34, 55], [34, 58], [0, 1]], ![[0, 1], [0, 54], [22, 42], [5, 20], [64, 24], [1, 21], [58, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [9, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [45, 21, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3297, -1124, 1059, 5051, 1369]
  a := ![1, 18, -3, 17, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6489, -2853, 1059, 5051, 1369]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, -1, 0, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![1, 1, -1, 0, 0]] 
 ![![79, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![68, 0, 0, 0, 1]] where
  M :=![![![1, 1, -1, 0, 0], ![0, 0, 1, -2, 0], ![0, 1, 2, 2, -4], ![-8, -7, -1, 7, 2], ![4, 0, -6, -2, 5]]]
  hmulB := by decide  
  f := ![![![-129, -59, 17, -16, 20]], ![![-79, -37, 10, -10, 12]], ![![-80, -37, 10, -10, 12]], ![![-40, -19, 5, -5, 6]], ![![-112, -52, 14, -14, 17]]]
  g := ![![![0, 1, -1, 0, 0], ![0, 0, 1, -2, 0], ![1, 1, 2, 2, -4], ![1, -7, -1, 7, 2], ![0, 0, -6, -2, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -30, -5, -7, -1]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-31, -30, -5, -7, -1]] 
 ![![79, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![69, 0, 1, 0, 0], ![59, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-31, -30, -5, -7, -1], ![-4, -40, -23, -8, -14], ![-56, -83, -32, -18, -16], ![-30, -56, -21, -12, -11], ![-50, -89, -38, -19, -20]]]
  hmulB := by decide  
  f := ![![![15, -8, -47, -1, 43]], ![![13, -4, -34, -3, 31]], ![![13, -5, -37, -1, 33]], ![![1, -14, -34, 9, 32]], ![![2, -5, -14, 1, 14]]]
  g := ![![![31, -30, -5, -7, -1], ![57, -40, -23, -8, -14], ![103, -83, -32, -18, -16], ![69, -56, -21, -12, -11], ![114, -89, -38, -19, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2

def I79N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-901, -262, 234, -84, 206]] i)))

def SI79N3: IdealEqSpanCertificate' Table ![![-901, -262, 234, -84, 206]] 
 ![![79, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![-901, -262, 234, -84, 206], ![824, 157, -178, 56, -168], ![-672, -26, 101, -20, 112], ![-188, -140, 86, -39, 64], ![-208, 64, 0, 12, 17]]]
  hmulB := by decide  
  f := ![![![157, 154, -14, -92, 58]], ![![150, 149, -10, -88, 52]], ![![98, 102, -3, -52, 36]], ![![29, 26, -12, -11, 26]], ![![89, 82, -14, -56, 35]]]
  g := ![![![3, -262, 234, -84, 206], ![46, 157, -178, 56, -168], ![-98, -26, 101, -20, 112], ![51, -140, 86, -39, 64], ![-73, 64, 0, 12, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N3 : Nat.card (O ⧸ I79N3) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N3)

lemma isPrimeI79N3 : Ideal.IsPrime I79N3 := prime_ideal_of_norm_prime hp79.out _ NI79N3
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-783, -581, 357, -162, 266]] ![![1, 1, -1, 0, 0]]
  ![![1577, 708, -518, 210, -422]] where
 M := ![![![1577, 708, -518, 210, -422]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![1577, 708, -518, 210, -422]] ![![-31, -30, -5, -7, -1]]
  ![![-7911, -6838, 4033, -1881, 2929]] where
 M := ![![![-7911, -6838, 4033, -1881, 2929]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N2 : IdealMulLeCertificate' Table 
  ![![-7911, -6838, 4033, -1881, 2929]] ![![-901, -262, 234, -84, 206]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-1472481, 1345054, -388443, 309443, -99777]]]
 hmul := by decide  
 g := ![![![![-18639, 17026, -4917, 3917, -1263]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2, I79N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
    exact isPrimeI79N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1 ⊙ MulI79N2)
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


def P83P0 : CertificateIrreducibleZModOfList' 83 5 2 6 [17, 23, 47, 26, 44, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 48, 76, 61, 37], [43, 21, 66, 65, 49], [71, 28, 15, 27, 32], [61, 68, 9, 13, 48], [0, 1]]
 g := ![![[8, 17, 8, 50, 27], [66, 2, 82, 9, 81], [31, 10, 74, 11], [0, 32, 21, 27], [1], []], ![[2, 17, 60, 54, 18, 75, 20, 36], [80, 34, 43, 22, 38, 10, 63, 12], [52, 60, 26, 12], [37, 21, 50, 17], [9, 46, 35, 52, 41, 21, 38, 17], [6, 10, 54, 41]], ![[52, 67, 75, 15, 51, 57, 52, 31], [21, 44, 2, 50, 76, 13, 60, 81], [7, 41, 79, 75], [64, 33, 40, 11], [14, 17, 41, 61, 50, 8, 33, 48], [18, 74, 77, 77]], ![[70, 19, 34, 8, 72, 32, 28, 34], [5, 69, 24, 15, 43, 58, 13, 5], [37, 61, 31, 28], [33, 56, 1, 27], [13, 57, 54, 8, 59, 62, 65, 66], [2, 53, 81, 28]], ![[10, 51, 78, 75, 64, 11, 70, 29], [2, 45, 66, 27, 44, 48, 18, 49], [67, 59, 30, 40], [29, 81, 17, 27], [66, 82, 72, 37, 61, 68, 74, 12], [13, 51, 53, 63]]]
 h' := ![![[30, 48, 76, 61, 37], [40, 61, 14, 18, 39], [77, 63, 50, 9, 74], [40, 72, 38, 19, 54], [66, 60, 36, 57, 39], [0, 0, 1], [0, 1]], ![[43, 21, 66, 65, 49], [38, 43, 1, 25, 18], [69, 39, 18, 6, 5], [66, 24, 13, 33, 26], [23, 34, 69, 68, 73], [51, 82, 39, 8, 53], [30, 48, 76, 61, 37]], ![[71, 28, 15, 27, 32], [32, 28, 11, 76, 56], [72, 64, 11, 44, 58], [78, 24, 44, 27, 18], [2, 37, 75, 11, 54], [49, 51, 19, 8, 40], [43, 21, 66, 65, 49]], ![[61, 68, 9, 13, 48], [37, 64, 60, 8, 39], [68, 13, 65, 59, 56], [45, 70, 35, 49, 51], [78, 46, 47, 22, 44], [27, 41, 58, 41, 32], [71, 28, 15, 27, 32]], ![[0, 1], [14, 53, 80, 39, 14], [51, 70, 22, 48, 56], [32, 59, 36, 38, 17], [44, 72, 22, 8, 39], [14, 75, 49, 26, 41], [61, 68, 9, 13, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 51, 79, 20], [], [], []]
 b := ![[], [65, 40, 17, 51, 69], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 5
  hpos := by decide
  P := [17, 23, 47, 26, 44, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-32010168274, 10971104838, 73941438515, 22992884100, -77562563677]
  a := ![-1, 2, 5, 4, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-385664678, 132181986, 890860705, 277022700, -934488719]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -43, -78, 13, 85]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-3, -43, -78, 13, 85]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![65, 44, 1, 0, 0], ![83, 44, 0, 1, 0], ![71, 30, 0, 0, 1]] where
  M :=![![![-3, -43, -78, 13, 85], ![340, 259, -56, -326, 26], ![104, 388, 585, -164, -652], ![-1474, -1089, 304, 1400, -177], ![-302, -745, -952, 399, 1074]]]
  hmulB := by decide  
  f := ![![![1285, 2833, 1350, 593, 747]], ![![2988, 5623, 2240, 1206, 1186]], ![![2469, 4961, 2143, 1053, 1159]], ![![2713, 5496, 2398, 1165, 1300]], ![![2093, 4280, 1886, 906, 1025]]]
  g := ![![![-23, 3, -78, 13, 85], ![328, 183, -56, -326, 26], ![247, 16, 585, -164, -652], ![-1403, -795, 304, 1400, -177], ![-537, -97, -952, 399, 1074]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [57, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 88], [0, 1]]
 g := ![![[75, 25], [80], [21], [54, 32], [48, 9], [1]], ![[0, 64], [80], [21], [47, 57], [21, 80], [1]]]
 h' := ![![[86, 88], [15, 5], [83, 76], [37, 56], [23, 11], [32, 86], [0, 1]], ![[0, 1], [0, 84], [33, 13], [47, 33], [79, 78], [41, 3], [86, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [50, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [57, 3, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3897, 3810, 850, -4260, -894]
  a := ![0, -10, -2, -20, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4109, 2030, 850, -4260, -894]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 10, -38, -30, 38]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![35, 10, -38, -30, 38]] 
 ![![89, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![79, 0, 1, 0, 0], ![46, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![35, 10, -38, -30, 38], ![152, 149, 40, -152, -60], ![-240, -48, 301, 200, -304], ![-684, -652, -144, 681, 230], ![340, 22, -516, -274, 529]]]
  hmulB := by decide  
  f := ![![![643, -1402, -1326, -242, -862]], ![![178, -519, -460, -92, -296]], ![![549, -1318, -1213, -230, -786]], ![![310, -772, -708, -135, -458]], ![![87, -352, -290, -64, -185]]]
  g := ![![![39, 10, -38, -30, 38], ![6, 149, 40, -152, -60], ![-299, -48, 301, 200, -304], ![-56, -652, -144, 681, 230], ![495, 22, -516, -274, 529]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 157, 62, 33, 37]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![29, 157, 62, 33, 37]] 
 ![![89, 0, 0, 0, 0], ![41, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![86, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![29, 157, 62, 33, 37], ![148, 239, 124, 50, 66], ![264, 536, 189, 116, 100], ![126, 307, 148, 64, 83], ![298, 571, 216, 123, 114]]]
  hmulB := by decide  
  f := ![![![-923, -839, -118, 909, 227]], ![![-415, -388, -74, 411, 125]], ![![-22, -22, -7, 22, 10]], ![![-928, -797, -28, 904, 129]], ![![-368, -327, -32, 361, 74]]]
  g := ![![![-120, 157, 62, 33, 37], ![-187, 239, 124, 50, 66], ![-402, 536, 189, 116, 100], ![-239, 307, 148, 64, 83], ![-431, 571, 216, 123, 114]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2

def I89N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-241, -452, -198, -96, -106]] i)))

def SI89N3: IdealEqSpanCertificate' Table ![![-241, -452, -198, -96, -106]] 
 ![![89, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![-241, -452, -198, -96, -106], ![-424, -863, -356, -184, -192], ![-768, -1548, -679, -328, -368], ![-524, -1028, -432, -219, -232], ![-848, -1716, -744, -364, -403]]]
  hmulB := by decide  
  f := ![![![695, 588, -6, -680, -66]], ![![489, 421, 10, -480, -62]], ![![220, 188, 1, -216, -24]], ![![288, 212, -64, -275, 40]], ![![423, 352, -14, -412, -29]]]
  g := ![![![485, -452, -198, -96, -106], ![913, -863, -356, -184, -192], ![1664, -1548, -679, -328, -368], ![1092, -1028, -432, -219, -232], ![1839, -1716, -744, -364, -403]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N3 : Nat.card (O ⧸ I89N3) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N3)

lemma isPrimeI89N3 : Ideal.IsPrime I89N3 := prime_ideal_of_norm_prime hp89.out _ NI89N3
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-3, -43, -78, 13, 85]] ![![35, 10, -38, -30, 38]]
  ![![32087, -9299, -70816, -23411, 74133]] where
 M := ![![![32087, -9299, -70816, -23411, 74133]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![32087, -9299, -70816, -23411, 74133]] ![![29, 157, 62, 33, 37]]
  ![![695, 588, -6, -680, -66]] where
 M := ![![![695, 588, -6, -680, -66]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N2 : IdealMulLeCertificate' Table 
  ![![695, 588, -6, -680, -66]] ![![-241, -452, -198, -96, -106]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2, I89N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
    exact isPrimeI89N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1 ⊙ MulI89N2)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![531, -106, -1832, 80, -1138]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![531, -106, -1832, 80, -1138]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![54, 78, 34, 18, 1]] where
  M :=![![![531, -106, -1832, 80, -1138], ![-4552, -5853, -186, -1388, 160], ![640, -4098, -4465, -692, -2776], ![-3276, -4538, -1610, -995, -772], ![-1224, -6036, -4004, -1184, -2383]]]
  hmulB := by decide  
  f := ![![![-101, -38, 92, 88, -90]], ![![-360, -369, -126, 364, 176]], ![![704, 218, -733, -604, 728]], ![![1636, 1626, 474, -1643, -692]], ![![194, 58, -206, -166, 205]]]
  g := ![![![639, 914, 380, 212, -1138], ![-136, -189, -58, -44, 160], ![1552, 2190, 927, 508, -2776], ![396, 574, 254, 133, -772], ![1314, 1854, 794, 430, -2383]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [95, 3, 1, 54, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 76, 3, 16], [79, 9, 16, 36], [65, 11, 78, 45], [0, 1]]
 g := ![![[95, 34, 62, 65], [10, 4, 48], [12, 65, 36], [2, 10, 43], [5, 43, 1], []], ![[9, 22, 96, 42, 58, 61], [56, 65, 86], [58, 27, 89], [46, 80, 9], [61, 68, 9], [35, 92, 32, 66, 49, 22]], ![[73, 13, 80, 93, 32, 16], [2, 3, 75], [48, 56, 81], [34, 27, 1], [85, 88, 43], [15, 71, 49, 45, 85, 96]], ![[64, 28, 61, 60, 12, 10], [52, 8, 85], [8, 15, 70], [70, 60, 50], [33, 30, 44], [39, 11, 46, 70, 65, 42]]]
 h' := ![![[93, 76, 3, 16], [14, 72, 85, 29], [73, 91, 47, 40], [7, 76, 30, 6], [10, 71, 62, 72], [0, 0, 0, 1], [0, 1]], ![[79, 9, 16, 36], [94, 52, 43, 64], [46, 79, 21, 59], [30, 89, 73, 63], [61, 57, 35, 94], [6, 41, 37, 94], [93, 76, 3, 16]], ![[65, 11, 78, 45], [76, 67, 21, 64], [84, 31, 90, 50], [52, 9, 9, 9], [9, 84, 89, 1], [18, 18, 87, 25], [79, 9, 16, 36]], ![[0, 1], [95, 3, 45, 37], [66, 90, 36, 45], [70, 20, 82, 19], [67, 79, 8, 27], [96, 38, 70, 74], [65, 11, 78, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [78, 21, 90], []]
 b := ![[], [], [29, 2, 73, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [95, 3, 1, 54, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17207694, -47359170, -63639140, 23896147, 71297409]
  a := ![13, 0, 4, 1, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-39868740, -57820176, -25646918, -12984095, 71297409]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 38, -92, -88, 90]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![101, 38, -92, -88, 90]] 
 ![![97, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![62, 0, 1, 0, 0], ![67, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![101, 38, -92, -88, 90], ![360, 369, 126, -364, -176], ![-704, -218, 733, 604, -728], ![-1636, -1626, -474, 1643, 692], ![1032, 220, -1268, -864, 1279]]]
  hmulB := by decide  
  f := ![![![-531, 106, 1832, -80, 1138]], ![![-287, 127, 1154, -36, 714]], ![![-346, 110, 1217, -44, 756]], ![![-333, 120, 1282, -45, 794]], ![![-387, 142, 1420, -48, 881]]]
  g := ![![![29, 38, -92, -88, 90], ![75, 369, 126, -364, -176], ![-208, -218, 733, 604, -728], ![-347, -1626, -474, 1643, 692], ![317, 220, -1268, -864, 1279]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![531, -106, -1832, 80, -1138]] ![![101, 38, -92, -88, 90]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1241, 2214, 688, 486, 346]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![1241, 2214, 688, 486, 346]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![36, 8, 9, 1, 0], ![80, 1, 74, 0, 1]] where
  M :=![![![1241, 2214, 688, 486, 346], ![1384, 3313, 1728, 684, 972], ![3888, 7000, 2629, 1512, 1368], ![2044, 4338, 1880, 919, 1026], ![3996, 7514, 3024, 1610, 1603]]]
  hmulB := by decide  
  f := ![![![61, -14, -128, -46, 134]], ![![536, 469, 32, -524, -92]], ![![-368, 200, 993, 248, -1048]], ![![8, 30, 45, -13, -50]], ![![-212, 135, 610, 138, -645]]]
  g := ![![![-435, -20, -290, 486, 346], ![-1000, -31, -756, 684, 972], ![-1584, -64, -1111, 1512, 1368], ![-1120, -40, -815, 919, 1026], ![-1804, -69, -1288, 1610, 1603]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [35, 26, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 19, 34], [69, 81, 67], [0, 1]]
 g := ![![[80, 75, 95], [28, 47], [57, 50, 54], [45, 84], [43, 16], [1]], ![[47, 19, 59, 66], [50, 65], [74, 83, 40, 59], [40, 49], [38, 16], [68, 94, 81, 15]], ![[82, 67, 29, 86], [3, 21], [90, 4, 9, 86], [65, 31], [], [19, 69, 87, 86]]]
 h' := ![![[28, 19, 34], [49, 9, 87], [25, 84, 59], [65, 99, 85], [23, 41, 65], [66, 75, 97], [0, 1]], ![[69, 81, 67], [16, 13, 81], [7, 11, 60], [44, 70, 50], [63, 12, 94], [79, 38, 4], [28, 19, 34]], ![[0, 1], [45, 79, 34], [7, 6, 83], [64, 33, 67], [4, 48, 43], [99, 89], [69, 81, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 86], []]
 b := ![[], [29, 4, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [35, 26, 4, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![45220, 36474, -3543, -44267, -563]
  a := ![-1, -4, -1, -5, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![16672, 3873, 4322, -44267, -563]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 0, 1, -1, 1]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-5, 0, 1, -1, 1]] 
 ![![101, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-5, 0, 1, -1, 1], ![4, 0, 1, 0, -2], ![-8, -3, 0, 6, 0], ![-2, -4, -5, 0, 7], ![10, 9, -2, -9, 0]]]
  hmulB := by decide  
  f := ![![![-177, -330, -151, -69, -81]], ![![-33, -62, -28, -13, -15]], ![![-30, -57, -26, -12, -14]], ![![-46, -86, -39, -18, -21]], ![![-15, -29, -13, -6, -7]]]
  g := ![![![0, 0, 1, -1, 1], ![0, 0, 1, 0, -2], ![-1, -3, 0, 6, 0], ![1, -4, -5, 0, 7], ![1, 9, -2, -9, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 16, 3, -17, -5]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![17, 16, 3, -17, -5]] 
 ![![101, 0, 0, 0, 0], ![66, 1, 0, 0, 0], ![88, 0, 1, 0, 0], ![93, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![17, 16, 3, -17, -5], ![-20, 0, 33, 16, -34], ![-136, -123, -16, 134, 32], ![74, -12, -145, -56, 151], ![234, 205, 14, -229, -40]]]
  hmulB := by decide  
  f := ![![![365, 894, -333, 227, -215]], ![![230, 576, -211, 146, -136]], ![![336, 795, -296, 202, -192]], ![![331, 824, -304, 209, -196]], ![![31, 55, -19, 14, -13]]]
  g := ![![![3, 16, 3, -17, -5], ![-42, 0, 33, 16, -34], ![-32, -123, -16, 134, 32], ![179, -12, -145, -56, 151], ![69, 205, 14, -229, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![1241, 2214, 688, 486, 346]] ![![-5, 0, 1, -1, 1]]
  ![![-365, -894, 333, -227, 215]] where
 M := ![![![-365, -894, 333, -227, 215]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-365, -894, 333, -227, 215]] ![![17, 16, 3, -17, -5]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, 9, -10, 3, -9]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![39, 9, -10, 3, -9]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![15, 53, 1, 0, 0], ![66, 97, 0, 1, 0], ![1, 64, 0, 0, 1]] where
  M :=![![![39, 9, -10, 3, -9], ![-36, -7, 6, -2, 6], ![24, -6, -5, 0, -4], ![10, 5, -6, 0, -3], ![6, -7, 0, -3, -2]]]
  hmulB := by decide  
  f := ![![![-7, -9, 2, 1, -1]], ![![-4, -9, -10, 6, 2]], ![![-3, -6, -5, 3, 1]], ![![-8, -14, -8, 6, 1]], ![![-3, -6, -6, 4, 1]]]
  g := ![![![0, 8, -10, 3, -9], ![0, -5, 6, -2, 6], ![1, 5, -5, 0, -4], ![1, 5, -6, 0, -3], ![2, 4, 0, -3, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [9, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 102], [0, 1]]
 g := ![![[52, 23], [17, 61], [12, 26], [72], [30], [47, 1]], ![[0, 80], [0, 42], [101, 77], [72], [30], [94, 102]]]
 h' := ![![[47, 102], [53, 69], [98, 79], [26, 52], [57, 81], [92, 37], [0, 1]], ![[0, 1], [0, 34], [0, 24], [101, 51], [53, 22], [80, 66], [47, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [15, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [9, 56, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1082, 470, -118, -1518, 555]
  a := ![3, -4, 0, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![995, 1150, -118, -1518, 555]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 69, 28, 15, 15]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![37, 69, 28, 15, 15]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![87, 98, 1, 0, 0], ![63, 83, 0, 1, 0], ![38, 82, 0, 0, 1]] where
  M :=![![![37, 69, 28, 15, 15], ![60, 125, 54, 26, 30], ![120, 234, 99, 48, 52], ![74, 151, 66, 34, 33], ![126, 253, 108, 57, 60]]]
  hmulB := by decide  
  f := ![![![-69, -61, 36, -19, 27]], ![![108, 75, -42, 18, -38]], ![![43, 19, -9, 1, -13]], ![![45, 23, -12, 3, -14]], ![![60, 37, -20, 7, -20]]]
  g := ![![![-38, -50, 28, 15, 15], ![-72, -95, 54, 26, 30], ![-131, -172, 99, 48, 52], ![-88, -115, 66, 34, 33], ![-147, -194, 108, 57, 60]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [60, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 102], [0, 1]]
 g := ![![[52, 91], [10, 66], [64, 76], [92], [50], [73, 1]], ![[0, 12], [90, 37], [50, 27], [92], [50], [43, 102]]]
 h' := ![![[73, 102], [18, 83], [74, 90], [94, 30], [19, 68], [49, 16], [0, 1]], ![[0, 1], [0, 20], [52, 13], [18, 73], [39, 35], [84, 87], [73, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [14, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [60, 30, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![359, -306, -1264, -68, 1734]
  a := ![1, 0, -3, -1, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![473, -126, -1264, -68, 1734]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -4, 2, 0, 2]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![-7, -4, 2, 0, 2]] 
 ![![103, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![65, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![93, 0, 0, 0, 1]] where
  M :=![![![-7, -4, 2, 0, 2], ![8, 3, -4, 0, 0], ![0, 4, 3, -8, 0], ![-4, 0, 8, 3, -8], ![-16, -12, 0, 12, 3]]]
  hmulB := by decide  
  f := ![![![-129, -348, -186, -72, -106]], ![![-73, -193, -102, -40, -58]], ![![-87, -232, -123, -48, -70]], ![![-53, -140, -74, -29, -42]], ![![-123, -328, -174, -68, -99]]]
  g := ![![![-1, -4, 2, 0, 2], ![1, 3, -4, 0, 0], ![-1, 4, 3, -8, 0], ![1, 0, 8, 3, -8], ![-1, -12, 0, 12, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![39, 9, -10, 3, -9]] ![![37, 69, 28, 15, 15]]
  ![![-129, -348, -186, -72, -106]] where
 M := ![![![-129, -348, -186, -72, -106]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-129, -348, -186, -72, -106]] ![![-7, -4, 2, 0, 2]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB171I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB171I2 : PrimesBelowBoundCertificateInterval O 61 103 171 where
  m := 9
  g := ![4, 3, 2, 4, 1, 4, 2, 3, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB171I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2, I67N3]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2, I79N3]
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2, I89N3]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
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
    · exact ![4489, 67, 67, 67]
    · exact ![357911, 71, 71]
    · exact ![28398241, 73]
    · exact ![6241, 79, 79, 79]
    · exact ![3939040643]
    · exact ![7921, 89, 89, 89]
    · exact ![88529281, 97]
    · exact ![1030301, 101, 101]
    · exact ![10609, 10609, 103]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
      exact NI67N3
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
      exact NI79N1
      exact NI79N2
      exact NI79N3
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
      exact NI89N3
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
  β := ![I67N1, I67N2, I67N3, I71N1, I71N2, I73N1, I79N1, I79N2, I79N3, I89N1, I89N2, I89N3, I97N1, I101N1, I101N2, I103N2]
  Il := ![[I67N1, I67N2, I67N3], [I71N1, I71N2], [I73N1], [I79N1, I79N2, I79N3], [], [I89N1, I89N2, I89N3], [I97N1], [I101N1, I101N2], [I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
