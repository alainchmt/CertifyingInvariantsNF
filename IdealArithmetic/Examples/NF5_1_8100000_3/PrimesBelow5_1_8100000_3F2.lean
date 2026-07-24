
import IdealArithmetic.Examples.NF5_1_8100000_3.RI5_1_8100000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-498282, 205371, -27195, -32999, -98222]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-498282, 205371, -27195, -32999, -98222]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![2, 34, 40, 1, 0], ![20, 18, 5, 0, 1]] where
  M :=![![![-498282, 205371, -27195, -32999, -98222], ![163445, -67366, 8927, 10833, 32224], ![-53615, 22085, -2918, -3537, -10558], ![-72933, 30043, -3979, -4824, -14370], ![215843, -88967, 11775, 14289, 42545]]]
  hmulB := by decide  
  f := ![![![36, 137, -143, 107, -20]], ![![147, 100, 97, -159, 234]], ![![-627, -1085, 568, -199, -552]], ![![-293, -575, 367, -184, -212]], ![![6, -22, 43, -42, 27]]]
  g := ![![![22868, 46199, 26625, -32999, -98222], ![-7503, -15160, -8739, 10833, 32224], ![2457, 4961, 2856, -3537, -10558], ![3345, 6757, 3893, -4824, -14370], ![-9905, -20009, -11530, 14289, 42545]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [18, 60, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 46, 49], [66, 20, 18], [0, 1]]
 g := ![![[49, 33, 4], [24, 4, 29], [18, 40], [32, 21], [55, 1], []], ![[32, 23, 26, 59], [50, 14, 6, 21], [11, 22], [48, 19], [29, 65], [17, 56]], ![[29, 11, 63, 32], [55, 30, 26, 61], [62, 1], [14, 56], [23, 39], [48, 56]]]
 h' := ![![[56, 46, 49], [37, 30, 65], [66, 12, 37], [51, 2, 24], [15, 32, 17], [0, 0, 1], [0, 1]], ![[66, 20, 18], [10, 23, 23], [57, 29, 55], [11, 28, 42], [2, 42, 32], [16, 42, 20], [56, 46, 49]], ![[0, 1], [58, 14, 46], [15, 26, 42], [40, 37, 1], [52, 60, 18], [8, 25, 46], [66, 20, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 29], []]
 b := ![[], [37, 24, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [18, 60, 12, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9873, -47063, 50139, -25846, 16506]
  a := ![-5, -7, -3, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4303, 7979, 14947, -25846, 16506]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 164, -74, 16, 96]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![101, 164, -74, 16, 96]] 
 ![![67, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![101, 164, -74, 16, 96], ![-176, -437, 356, -228, -64], ![-100, 272, -565, 548, -392], ![754, 1140, -434, 19, 776], ![-1106, -2204, 1422, -716, -773]]]
  hmulB := by decide  
  f := ![![![-11696385, 4820716, -638430, -774680, -2305648]], ![![-2037612, 839811, -111220, -134956, -401664]], ![![-9969439, 4108948, -544167, -660300, -1965224]], ![![-9452488, 3895884, -515950, -626061, -1863320]], ![![-2019254, 832244, -110218, -133740, -398045]]]
  g := ![![![5, 164, -74, 16, 96], ![-32, -437, 356, -228, -64], ![59, 272, -565, 548, -392], ![22, 1140, -434, 19, 776], ![-116, -2204, 1422, -716, -773]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, 9, -1, -1, -4]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![-22, 9, -1, -1, -4]] 
 ![![67, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-22, 9, -1, -1, -4], ![7, -4, 1, 1, 2], ![-3, -1, 0, 1, 0], ![-3, 1, -1, 0, 0], ![9, -5, 1, -1, 1]]]
  hmulB := by decide  
  f := ![![![-8, -13, -1, -11, -6]], ![![-5, -8, -1, -7, -4]], ![![-5, -8, -1, -8, -4]], ![![-5, -8, 0, -7, -4]], ![![-1, -1, -1, -1, -1]]]
  g := ![![![-4, 9, -1, -1, -4], ![1, -4, 1, 1, 2], ![0, -1, 0, 1, 0], ![0, 1, -1, 0, 0], ![3, -5, 1, -1, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-498282, 205371, -27195, -32999, -98222]] ![![101, 164, -74, 16, 96]]
  ![![8, 13, 1, 11, 6]] where
 M := ![![![8, 13, 1, 11, 6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![8, 13, 1, 11, 6]] ![![-22, 9, -1, -1, -4]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -76, 44, -18, -32]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-41, -76, 44, -18, -32]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![68, 26, 41, 1, 0], ![54, 41, 51, 0, 1]] where
  M :=![![![-41, -76, 44, -18, -32], ![46, 145, -140, 102, -4], ![110, 28, 137, -174, 208], ![-318, -556, 292, -105, -276], ![380, 868, -652, 388, 189]]]
  hmulB := by decide  
  f := ![![![-611, 244, -36, -42, -120]], ![![198, -89, 4, 6, 36]], ![![-66, 28, -17, -22, -24]], ![![-552, 218, -43, -51, -116]], ![![-394, 153, -37, -44, -87]]]
  g := ![![![41, 24, 34, -18, -32], ![-94, -33, -58, 102, -4], ![10, -56, -47, -174, 208], ![306, 190, 263, -105, -276], ![-510, -239, -369, 388, 189]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [50, 17, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 56, 63], [7, 14, 8], [0, 1]]
 g := ![![[48, 2, 1], [47, 68, 16], [20, 5, 57], [8, 4], [21, 1], []], ![[14, 36, 33, 23], [12, 65, 35, 51], [4, 54, 15, 22], [45, 24], [62, 54], [22, 64]], ![[39, 61, 47, 5], [39, 8, 11, 10], [30, 63, 70, 30], [28, 38], [67, 12], [6, 64]]]
 h' := ![![[14, 56, 63], [64, 26, 1], [65, 2, 4], [38, 21, 46], [15, 19, 69], [0, 0, 1], [0, 1]], ![[7, 14, 8], [21, 18, 19], [27, 40, 40], [70, 64, 50], [30, 35, 33], [19, 53, 14], [14, 56, 63]], ![[0, 1], [66, 27, 51], [69, 29, 27], [70, 57, 46], [11, 17, 40], [33, 18, 56], [7, 14, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 62], []]
 b := ![[], [8, 24, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [50, 17, 50, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2074686, -8649550, 11719466, -9128878, 1561274]
  a := ![9, -56, 5, -57, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7526482, 2319564, 4315190, -9128878, 1561274]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, -39, -9, -5, 6]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![26, -39, -9, -5, 6]] 
 ![![71, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![26, -39, -9, -5, 6], ![-17, -18, -27, -29, -16], ![3, 7, -50, -67, -42], ![17, 57, -25, -48, -38], ![1, 67, 21, 11, -5]]]
  hmulB := by decide  
  f := ![![![-252, -561, 407, -235, -140]], ![![-81, -173, 120, -66, -50]], ![![-119, -286, 223, -138, -52]], ![![-161, -354, 254, -145, -92]], ![![-125, -259, 173, -91, -83]]]
  g := ![![![17, -39, -9, -5, 6], ![45, -18, -27, -29, -16], ![85, 7, -50, -67, -42], ![43, 57, -25, -48, -38], ![-36, 67, 21, 11, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18, -7, 1, 1, 4]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![18, -7, 1, 1, 4]] 
 ![![71, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![18, -7, 1, 1, 4], ![-7, 0, 1, -1, -2], ![3, 3, -4, 3, 0], ![5, 1, 1, -2, 4], ![-13, -5, 3, -1, -7]]]
  hmulB := by decide  
  f := ![![![-20, -105, 1, 27, 34]], ![![-11, -57, 0, 14, 18]], ![![-15, -78, -1, 18, 24]], ![![-9, -47, -1, 10, 14]], ![![-3, -16, 0, 4, 5]]]
  g := ![![![2, -7, 1, 1, 4], ![0, 0, 1, -1, -2], ![0, 3, -4, 3, 0], ![-1, 1, 1, -2, 4], ![2, -5, 3, -1, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-41, -76, 44, -18, -32]] ![![26, -39, -9, -5, 6]]
  ![![20, 105, -1, -27, -34]] where
 M := ![![![20, 105, -1, -27, -34]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![20, 105, -1, -27, -34]] ![![18, -7, 1, 1, 4]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![493, -34, -436, -610, -326]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![493, -34, -436, -610, -326]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![22, 1, 30, 48, 1]] where
  M :=![![![493, -34, -436, -610, -326], ![42, 1077, -686, -1156, -894], ![632, 2670, -711, -1634, -1418], ![580, 2150, 260, -241, -478], ![-200, -102, 1028, 1382, 847]]]
  hmulB := by decide  
  f := ![![![33, 26, 16, -30, 50]], ![![-130, -231, 126, -48, -110]], ![![172, 498, -451, 314, 14]], ![![208, 98, 200, -277, 362]], ![![208, 263, -44, -62, 249]]]
  g := ![![![105, 4, 128, 206, -326], ![270, 27, 358, 572, -894], ![436, 56, 573, 910, -1418], ![152, 36, 200, 311, -478], ![-258, -13, -334, -538, 847]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 4 2 6 [43, 13, 53, 39, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 70, 53, 29], [50, 41, 14, 21], [26, 34, 6, 23], [0, 1]]
 g := ![![[57, 3, 65, 65], [29, 64, 64], [30, 18, 65], [6, 35, 3, 61], [1], []], ![[62, 4, 2, 17, 41, 33], [70, 29, 67], [14, 28, 69], [49, 4, 61, 60, 4, 63], [5, 71, 6], [72, 59, 38]], ![[25, 65, 68, 67, 61, 47], [32, 19, 72], [62, 46, 27], [9, 51, 2, 18, 3, 68], [28, 2, 71], [34, 33, 3]], ![[19, 41, 6, 2, 42, 64], [61, 19, 3], [8, 71, 35], [6, 24, 51, 70, 26, 38], [51, 27, 9], [32, 12, 18]]]
 h' := ![![[31, 70, 53, 29], [65, 14, 31, 49], [12, 61, 14, 8], [34, 47, 70, 49], [30, 60, 20, 34], [0, 0, 1], [0, 1]], ![[50, 41, 14, 21], [38, 23, 69, 45], [37, 63, 2, 40], [36, 11, 61, 54], [36, 53, 21, 59], [55, 64, 71, 15], [31, 70, 53, 29]], ![[26, 34, 6, 23], [48, 52, 64, 57], [16, 47, 22, 46], [28, 31, 29, 63], [1, 23, 32, 44], [16, 49, 64, 61], [50, 41, 14, 21]], ![[0, 1], [13, 57, 55, 68], [9, 48, 35, 52], [39, 57, 59, 53], [21, 10, 0, 9], [30, 33, 10, 70], [26, 34, 6, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [19, 0, 64], []]
 b := ![[], [], [45, 16, 6, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 4
  hpos := by decide
  P := [43, 13, 53, 39, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17991, -30260, 67626, -28250, -11718]
  a := ![0, -4, 0, -5, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3285, -254, 5742, 7318, -11718]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 28398241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, 26, 16, -30, 50]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![33, 26, 16, -30, 50]] 
 ![![73, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  M :=![![![33, 26, 16, -30, 50], ![-130, -231, 126, -48, -110], ![172, 498, -451, 314, 14], ![208, 98, 200, -277, 362], ![-556, -786, 240, 58, -609]]]
  hmulB := by decide  
  f := ![![![493, -34, -436, -610, -326]], ![![345, -9, -314, -442, -240]], ![![191, 24, -171, -248, -140]], ![![116, 22, -92, -137, -78]], ![![470, -34, -404, -566, -301]]]
  g := ![![![-65, 26, 16, -30, 50], ![229, -231, 126, -48, -110], ![-261, 498, -451, 314, 14], ![-426, 98, 200, -277, 362], ![1024, -786, 240, 58, -609]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![493, -34, -436, -610, -326]] ![![33, 26, 16, -30, 50]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [23, 18, 37, 64, 69, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 61, 41, 60, 22], [28, 44, 60, 9, 73], [10, 67, 7, 59, 18], [1, 64, 50, 30, 45], [0, 1]]
 g := ![![[15, 41, 38, 56, 19], [25, 59, 18, 63, 50], [19, 26, 68, 76, 73], [63, 78, 36, 10, 1], [], []], ![[60, 34, 48, 59, 6, 75, 69, 73], [8, 19, 44, 31, 43, 50, 60, 52], [38, 28, 52, 43, 66, 32, 20, 21], [75, 37, 77, 42, 53, 62, 20, 55], [69, 25, 13, 32], [17, 11, 54, 10]], ![[33, 56, 49, 27, 27, 22, 35, 76], [17, 72, 53, 16, 54, 61, 63, 26], [5, 30, 33, 21, 38, 19, 19, 67], [10, 9, 23, 55, 47, 35, 5, 62], [25, 78, 22, 64], [34, 51, 15, 36]], ![[69, 63, 7, 22, 0, 10, 0, 51], [4, 73, 57, 33, 42, 75, 49, 73], [69, 41, 44, 13, 50, 4, 49, 65], [78, 39, 3, 54, 1, 29, 18, 55], [43, 45, 75, 46], [25, 60, 71, 8]], ![[19, 3, 68, 40, 30, 16, 56, 22], [75, 1, 30, 21, 60, 40, 76, 32], [41, 43, 25, 26, 1, 48, 0, 23], [16, 74, 74, 75, 35, 0, 22, 73], [11, 33, 17, 55], [14, 72, 40, 50]]]
 h' := ![![[50, 61, 41, 60, 22], [57, 36, 76, 19, 63], [37, 26, 63, 11, 34], [52, 74, 19, 25, 28], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[28, 44, 60, 9, 73], [5, 42, 36, 42, 45], [27, 62, 56, 77, 15], [15, 11, 11, 25, 46], [16, 25, 67, 68, 68], [55, 11, 64, 10, 36], [50, 61, 41, 60, 22]], ![[10, 67, 7, 59, 18], [16, 50, 70, 4, 44], [24, 52, 52, 0, 41], [73, 6, 18, 75, 70], [61, 77, 46, 1, 4], [2, 47, 10, 70, 8], [28, 44, 60, 9, 73]], ![[1, 64, 50, 30, 45], [8, 63, 15, 70, 4], [57, 29, 70, 29, 37], [65, 61, 67, 72, 61], [39, 40, 73, 23, 74], [78, 63, 43, 75, 58], [10, 67, 7, 59, 18]], ![[0, 1], [68, 46, 40, 23, 2], [56, 68, 75, 41, 31], [29, 6, 43, 40, 32], [9, 16, 51, 66, 11], [74, 37, 40, 3, 56], [1, 64, 50, 30, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 60, 55, 69], [], [], []]
 b := ![[], [26, 18, 77, 73, 22], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [23, 18, 37, 64, 69, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4913506989, 12683215054, -5837846410, 2372424747, 1090328059]
  a := ![9, 27, 5, 26, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![62196291, 160547026, -73896790, 30030693, 13801621]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0, 0, 0]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]] where
  M :=![![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 5 2 6 [15, 41, 46, 31, 50, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 8, 79, 38, 32], [56, 36, 45, 34, 43], [27, 73, 41, 68, 19], [39, 48, 1, 26, 72], [0, 1]]
 g := ![![[17, 5, 69, 2, 59], [80, 3, 6, 76, 40], [20, 34, 37, 37], [11, 0, 27, 10], [1], []], ![[18, 50, 61, 41, 71, 23, 79, 56], [13, 11, 80, 46, 24, 60, 6, 42], [28, 42, 15, 11], [27, 13, 17, 64], [14, 32, 66, 42, 32, 43, 20, 60], [9, 14, 36, 28]], ![[13, 56, 67, 25, 82, 24, 11, 57], [81, 33, 57, 22, 21, 56, 38, 50], [51, 4, 63, 38], [9, 5, 4, 1], [77, 73, 34, 4, 35, 32, 49, 57], [32, 24, 31, 23]], ![[48, 41, 54, 57, 17, 46, 80, 45], [8, 62, 79, 52, 37, 59, 74, 56], [28, 60, 37, 75], [68, 45, 28, 12], [80, 78, 82, 26, 59, 81, 44, 80], [7, 43, 55, 29]], ![[41, 24, 42, 46, 22, 63, 61, 57], [53, 8, 9, 48, 42, 82, 33, 55], [62, 34, 62, 29], [74, 75, 64, 48], [15, 28, 12, 79, 1, 10, 22, 71], [79, 70, 18, 38]]]
 h' := ![![[77, 8, 79, 38, 32], [45, 63, 38, 32, 15], [63, 20, 17, 22, 17], [60, 32, 75, 33, 55], [68, 42, 37, 52, 33], [0, 0, 1], [0, 1]], ![[56, 36, 45, 34, 43], [1, 12, 25, 57, 75], [24, 51, 74, 27, 31], [19, 11, 14, 6, 54], [80, 44, 65, 22, 75], [67, 72, 78, 64, 38], [77, 8, 79, 38, 32]], ![[27, 73, 41, 68, 19], [1, 20, 2, 43, 72], [74, 34, 27, 59, 12], [80, 37, 49, 10, 11], [7, 64, 44, 27, 1], [0, 36, 12, 16, 11], [56, 36, 45, 34, 43]], ![[39, 48, 1, 26, 72], [56, 75, 34, 64, 9], [63, 62, 8, 19, 47], [63, 51, 61, 17, 65], [2, 7, 44, 44, 26], [43, 22, 68, 42, 12], [27, 73, 41, 68, 19]], ![[0, 1], [70, 79, 67, 53, 78], [61, 82, 40, 39, 59], [59, 35, 50, 17, 64], [67, 9, 59, 21, 31], [4, 36, 7, 44, 22], [39, 48, 1, 26, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 37, 56, 64], [], [], []]
 b := ![[], [30, 79, 30, 77, 81], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 5
  hpos := by decide
  P := [15, 41, 46, 31, 50, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![874587434, -18666055173, 29131231685, -26038555239, 14591468309]
  a := ![-11, -9, -5, -7, -21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10537198, -224892231, 350978695, -313717533, 175800823]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19179, 8347, -1723, -2256, -4462]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-19179, 8347, -1723, -2256, -4462]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![88, 46, 72, 1, 0], ![73, 83, 54, 0, 1]] where
  M :=![![![-19179, 8347, -1723, -2256, -4462], ![6668, -848, -577, -1240, -50], ![-1140, 5101, -948, -2344, -2430], ![-2076, 4283, 409, -285, -1104], ![8255, -4107, 1983, 2709, 3075]]]
  hmulB := by decide  
  f := ![![![-3333, -4293, 819, 894, -3938]], ![![8770, 18070, -12169, 6470, 5726]], ![![-4982, -25559, 29522, -23594, 7214]], ![![-3056, -15881, 18409, -14737, 4564]], ![![2922, -1328, 6809, -7415, 6937]]]
  g := ![![![5675, 5421, 4513, -2256, -4462], ![1342, 678, 1027, -1240, -50], ![4298, 3535, 3360, -2344, -2430], ![1164, 1225, 905, -285, -1104], ![-5108, -4314, -4035, 2709, 3075]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [24, 80, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 54, 35], [17, 34, 54], [0, 1]]
 g := ![![[35, 46, 32], [45, 67], [73, 21], [13, 48, 45], [48, 67, 1], []], ![[51, 38, 87, 77], [11, 87], [50, 34], [40, 12, 25, 61], [86, 84, 6, 54], [59, 68]], ![[38, 0, 46, 70], [37, 25], [28, 5], [37, 12, 48, 15], [46, 50, 3, 23], [40, 68]]]
 h' := ![![[50, 54, 35], [24, 26, 11], [6, 6, 45], [44, 58, 33], [5, 70, 57], [0, 0, 1], [0, 1]], ![[17, 34, 54], [76, 10, 38], [47, 26, 49], [1, 18, 37], [56, 68, 27], [16, 27, 34], [50, 54, 35]], ![[0, 1], [27, 53, 40], [84, 57, 84], [69, 13, 19], [61, 40, 5], [41, 62, 54], [17, 34, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 42], []]
 b := ![[], [58, 25, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [24, 80, 22, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![435560, 361984, 194464, -380160, 651088]
  a := ![6, -4, 4, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-153256, -406640, -85312, -380160, 651088]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 0, -4, -3, -2]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![0, 0, -4, -3, -2]] 
 ![![89, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![69, 0, 0, 0, 1]] where
  M :=![![![0, 0, -4, -3, -2], ![1, 3, -4, -9, -4], ![-1, 8, -5, -13, -14], ![7, 24, -8, 0, -4], ![0, -4, 16, 0, 7]]]
  hmulB := by decide  
  f := ![![![-26848, 11064, -1464, -1777, -5292]], ![![-3521, 1451, -192, -233, -694]], ![![-10289, 4240, -561, -681, -2028]], ![![-17239, 7104, -940, -1141, -3398]], ![![-20684, 8524, -1128, -1369, -4077]]]
  g := ![![![5, 0, -4, -3, -2], ![10, 3, -4, -9, -4], ![20, 8, -5, -13, -14], ![3, 24, -8, 0, -4], ![-11, -4, 16, 0, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -2, 18, -20, 20]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![9, -2, 18, -20, 20]] 
 ![![89, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![62, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![9, -2, 18, -20, 20], ![-60, -93, 38, -4, -60], ![116, 274, -213, 132, 52], ![44, -66, 170, -171, 136], ![-218, -238, -10, 114, -287]]]
  hmulB := by decide  
  f := ![![![42553, -17534, 2294, 2780, 8364]], ![![10362, -4269, 558, 676, 2036]], ![![23958, -9870, 1291, 1564, 4708]], ![![29714, -12242, 1602, 1941, 5840]], ![![15571, -6416, 840, 1018, 3061]]]
  g := ![![![-3, -2, 18, -20, 20], ![26, -93, 38, -4, -60], ![-58, 274, -213, 132, 52], ![-10, -66, 170, -171, 136], ![89, -238, -10, 114, -287]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-19179, 8347, -1723, -2256, -4462]] ![![0, 0, -4, -3, -2]]
  ![![-5722, -25039, -1401, 4813, 6882]] where
 M := ![![![-5722, -25039, -1401, 4813, 6882]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![-5722, -25039, -1401, 4813, 6882]] ![![9, -2, 18, -20, 20]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-178, 623, -6675, -8811, -5518]]]
 hmul := by decide  
 g := ![![![![-2, 7, -75, -99, -62]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, -11, 4, -4]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-1, 1, -11, 4, -4]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![44, 41, 20, 1, 0], ![20, 65, 47, 0, 1]] where
  M :=![![![-1, 1, -11, 4, -4], ![12, 12, -7, -14, 12], ![-38, -69, 36, -40, -40], ![14, 73, -71, 43, -26], ![35, 15, 55, -53, 65]]]
  hmulB := by decide  
  f := ![![![-471, 193, -25, -30, -92]], ![![154, -66, 9, 12, 32]], ![![-52, 15, -2, -2, -8]], ![![-160, 63, -8, -9, -30]], ![![-17, 2, 0, 1, -1]]]
  g := ![![![-1, 1, 1, 4, -4], ![4, -2, -3, -14, 12], ![26, 43, 28, -40, -40], ![-14, 0, 3, 43, -26], ![11, -21, -20, -53, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [93, 56, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 6, 79], [75, 90, 18], [0, 1]]
 g := ![![[20, 28, 2], [84, 36], [93, 53], [82, 8], [48, 66], [1]], ![[50, 62, 78, 61], [89, 6], [91, 96], [8, 9], [84, 12], [85, 53, 92, 85]], ![[75, 82, 44, 47], [12, 11], [88, 6], [88, 88], [57, 70], [73, 67, 3, 12]]]
 h' := ![![[80, 6, 79], [23, 80, 14], [50, 27, 6], [39, 93, 21], [14, 38, 69], [4, 41, 58], [0, 1]], ![[75, 90, 18], [21, 50, 14], [76, 47, 54], [10, 10, 22], [47, 21, 94], [83, 72, 20], [80, 6, 79]], ![[0, 1], [44, 64, 69], [53, 23, 37], [34, 91, 54], [78, 38, 31], [23, 81, 19], [75, 90, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 82], []]
 b := ![[], [32, 32, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [93, 56, 39, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18590, 133403, -544729, 280783, -189010]
  a := ![19, 19, 10, 20, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-88586, 9350, 28073, 280783, -189010]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![471, -193, 25, 30, 92]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![471, -193, 25, 30, 92]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![64, 57, 1, 0, 0], ![19, 57, 0, 1, 0], ![10, 6, 0, 0, 1]] where
  M :=![![![471, -193, 25, 30, 92], ![-154, 66, -9, -12, -32], ![52, -15, 2, 2, 8], ![70, -25, 5, 5, 14], ![-205, 81, -9, -11, -39]]]
  hmulB := by decide  
  f := ![![![1, -1, 11, -4, 4]], ![![-12, -12, 7, 14, -12]], ![![-6, -7, 11, 6, -4]], ![![-7, -8, 7, 7, -6]], ![![-1, -1, 1, 1, -1]]]
  g := ![![![-27, -40, 25, 30, 92], ![10, 15, -9, -12, -32], ![-2, -3, 2, 2, 8], ![-5, -7, 5, 5, 14], ![10, 15, -9, -11, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [77, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 96], [0, 1]]
 g := ![![[17, 70], [79], [53], [43], [16], [49, 1]], ![[52, 27], [79], [53], [43], [16], [1, 96]]]
 h' := ![![[49, 96], [71, 19], [25, 51], [41, 21], [32, 25], [10, 93], [0, 1]], ![[0, 1], [32, 78], [2, 46], [3, 76], [93, 72], [8, 4], [49, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [13, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [77, 48, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![34, -156, -68, 6, -19]
  a := ![1, -3, 1, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![46, 36, -68, 6, -19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-1, 1, -11, 4, -4]] ![![471, -193, 25, 30, 92]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1165, -2165, 1269, -554, -922]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-1165, -2165, 1269, -554, -922]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![27, 45, 65, 1, 0], ![50, 28, 7, 0, 1]] where
  M :=![![![-1165, -2165, 1269, -554, -922], ![1290, 4160, -4009, 2906, -186], ![3278, 1117, 3788, -4926, 5998], ![-9106, -16005, 8561, -3127, -7832], ![10759, 24749, -18745, 11301, 5259]]]
  hmulB := by decide  
  f := ![![![-141539, 58351, -7721, -9372, -27902]], ![![46432, -19122, 2547, 3088, 9158]], ![![-15228, 6277, -806, -976, -2982]], ![![-27155, 11203, -1459, -1771, -5338]], ![![-57645, 23770, -3139, -3811, -11361]]]
  g := ![![![593, 481, 433, -554, -922], ![-672, -1202, -1897, 2906, -186], ![-1620, 543, 2792, -4926, 5998], ![4623, 3406, 2640, -3127, -7832], ![-5518, -6248, -7823, 11301, 5259]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [44, 9, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 0, 38], [54, 100, 63], [0, 1]]
 g := ![![[23, 39, 47], [67, 1], [100, 66, 17], [95, 43], [90, 78], [1]], ![[80, 36, 13, 57], [88, 58], [15, 15, 76, 44], [50, 100], [11, 100], [54, 3, 94, 29]], ![[44, 46, 27, 48], [100, 21], [82, 89, 98, 94], [90, 4], [31, 6], [69, 85, 18, 72]]]
 h' := ![![[99, 0, 38], [99, 13, 59], [44, 58, 1], [78, 7, 57], [97, 85, 89], [57, 92, 52], [0, 1]], ![[54, 100, 63], [43, 33, 31], [73, 93, 82], [47, 49, 7], [5, 96, 10], [40, 89, 10], [99, 0, 38]], ![[0, 1], [28, 55, 11], [61, 51, 18], [55, 45, 37], [51, 21, 2], [100, 21, 39], [54, 100, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 73], []]
 b := ![[], [1, 69, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [44, 9, 49, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![654119, 1199247, -737574, 288669, 515709]
  a := ![13, 9, 10, 5, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-325994, -259710, -228822, 288669, 515709]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![141539, -58351, 7721, 9372, 27902]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![141539, -58351, 7721, 9372, 27902]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![45, 72, 1, 0, 0], ![97, 57, 0, 1, 0], ![33, 39, 0, 0, 1]] where
  M :=![![![141539, -58351, 7721, 9372, 27902], ![-46432, 19122, -2547, -3088, -9158], ![15228, -6277, 806, 976, 2982], ![20722, -8511, 1117, 1347, 4064], ![-61305, 25303, -3337, -4057, -12089]]]
  hmulB := by decide  
  f := ![![![1165, 2165, -1269, 554, 922]], ![![-1290, -4160, 4009, -2906, 186]], ![![-433, -2012, 2255, -1776, 484]], ![![481, -110, 959, -1077, 1068]], ![![-224, -1144, 1319, -1053, 321]]]
  g := ![![![-20156, -22145, 7721, 9372, 27902], ![6633, 7284, -2547, -3088, -9158], ![-2120, -2339, 806, 976, 2982], ![-2914, -3210, 1117, 1347, 4064], ![8726, 9587, -3337, -4057, -12089]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [20, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 100], [0, 1]]
 g := ![![[32, 96], [88], [49, 16], [71], [19], [67, 1]], ![[0, 5], [88], [10, 85], [71], [19], [33, 100]]]
 h' := ![![[67, 100], [49, 46], [30, 54], [90, 97], [46, 24], [74, 25], [0, 1]], ![[0, 1], [0, 55], [12, 47], [24, 4], [38, 77], [32, 76], [67, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [76, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [20, 34, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-749, -1810, 1070, -250, -245]
  a := ![7, 7, 3, 6, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-164, -545, 1070, -250, -245]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-1165, -2165, 1269, -554, -922]] ![![141539, -58351, 7721, 9372, 27902]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3445, 1123, 77, 188, -372]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-3445, 1123, 77, 188, -372]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![4, 77, 56, 15, 1]] where
  M :=![![![-3445, 1123, 77, 188, -372], ![932, -1320, 379, 714, 748], ![-782, -1715, 176, 724, 680], ![-784, -981, -367, -159, 10], ![1559, -91, -525, -823, -357]]]
  hmulB := by decide  
  f := ![![![15, -19, 53, -54, 44]], ![![-142, -206, 69, 8, -152]], ![![312, 695, -510, 298, 168]], ![![52, -267, 481, -449, 290]], ![![67, 180, -155, 104, 15]]]
  g := ![![![-19, 289, 203, 56, -372], ![-20, -572, -403, -102, 748], ![-34, -525, -368, -92, 680], ![-8, -17, -9, -3, 10], ![29, 266, 189, 44, -357]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 4 2 6 [1, 18, 36, 77, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 89, 56, 1], [43, 67, 30, 91], [72, 49, 17, 11], [0, 1]]
 g := ![![[89, 79, 46, 15], [88, 45, 102, 9], [85, 37, 66, 100], [86, 64, 76], [22, 26, 1], []], ![[54, 44, 88, 47, 97, 15], [91, 49, 92, 59, 1, 30], [3, 26, 60, 59, 17, 50], [42, 20, 56], [0, 77, 18], [5, 85, 16, 57, 91, 1]], ![[1, 25, 53, 54, 85, 98], [65, 51, 20, 70, 101, 4], [39, 65, 17, 50, 19, 55], [6, 78, 4], [74, 43, 38], [18, 13, 93, 84, 65, 23]], ![[7, 86, 48, 14, 52, 99], [56, 92, 10, 57, 39, 99], [51, 30, 90, 15, 8, 75], [33, 100, 15], [96, 5, 2], [25, 52, 29, 31, 92, 95]]]
 h' := ![![[14, 89, 56, 1], [15, 34, 21, 85], [18, 71, 81, 3], [89, 64, 69, 10], [81, 93, 78, 30], [0, 0, 0, 1], [0, 1]], ![[43, 67, 30, 91], [21, 98, 0, 18], [27, 13, 4, 66], [24, 8, 43, 16], [13, 46, 38, 57], [61, 39, 88, 92], [14, 89, 56, 1]], ![[72, 49, 17, 11], [19, 51, 68, 3], [9, 11, 40, 31], [24, 74, 4, 2], [37, 23, 58, 101], [76, 100, 32, 48], [43, 67, 30, 91]], ![[0, 1], [41, 23, 14, 100], [67, 8, 81, 3], [46, 60, 90, 75], [39, 44, 32, 18], [54, 67, 86, 65], [72, 49, 17, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [99, 6, 59], []]
 b := ![[], [], [60, 34, 18, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 4
  hpos := by decide
  P := [1, 18, 36, 77, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1576054, 4046590, -3487896, 766743, -34312]
  a := ![7, 8, 3, 9, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![16634, 64938, -15208, 12441, -34312]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 112550881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -19, 53, -54, 44]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![15, -19, 53, -54, 44]] 
 ![![103, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![86, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![15, -19, 53, -54, 44], ![-142, -206, 69, 8, -152], ![312, 695, -510, 298, 168], ![52, -267, 481, -449, 290], ![-477, -437, -145, 359, -685]]]
  hmulB := by decide  
  f := ![![![-3445, 1123, 77, 188, -372]], ![![-2466, 794, 59, 142, -260]], ![![-2884, 921, 66, 164, -304]], ![![-2583, 830, 54, 139, -278]], ![![-2092, 686, 42, 107, -231]]]
  g := ![![![-17, -19, 53, -54, 44], ![176, -206, 69, 8, -152], ![-396, 695, -510, 298, 168], ![-51, -267, 481, -449, 290], ![581, -437, -145, 359, -685]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-3445, 1123, 77, 188, -372]] ![![15, -19, 53, -54, 44]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)


lemma PB178I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB178I2 : PrimesBelowBoundCertificateInterval O 61 103 178 where
  m := 9
  g := ![3, 3, 2, 1, 1, 3, 2, 2, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB178I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
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
    · exact ![300763, 67, 67]
    · exact ![357911, 71, 71]
    · exact ![28398241, 73]
    · exact ![3077056399]
    · exact ![3939040643]
    · exact ![704969, 89, 89]
    · exact ![912673, 9409]
    · exact ![1030301, 10201]
    · exact ![112550881, 103]
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
      exact NI103N1
  β := ![I67N1, I67N2, I71N1, I71N2, I73N1, I89N1, I89N2, I103N1]
  Il := ![[I67N1, I67N2], [I71N1, I71N2], [I73N1], [], [], [I89N1, I89N2], [], [], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
