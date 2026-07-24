
import IdealArithmetic.Examples.NF5_3_125000000_1.RI5_3_125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 14, -6, 7, -4]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![47, 14, -6, 7, -4]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![64, 33, 39, 1, 0], ![50, 4, 53, 0, 1]] where
  M :=![![![47, 14, -6, 7, -4], ![-80, -7, 28, -8, 14], ![140, 58, -7, 21, -8], ![-40, 22, 44, 1, 14], ![140, 86, 22, 37, 1]]]
  hmulB := by decide  
  f := ![![![21, 4, -2, 1, -2]], ![![-40, -5, 8, -2, 2]], ![![20, -4, -5, 7, -2]], ![![12, -1, -1, 4, -2]], ![![30, 0, -5, 6, -3]]]
  g := ![![![-3, -3, -1, 7, -4], ![-4, 3, -6, -8, 14], ![-12, -9, -6, 21, -8], ![-12, -1, -11, 1, 14], ![-34, -17, -22, 37, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [9, 24, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 57, 21], [10, 9, 46], [0, 1]]
 g := ![![[9, 47, 39], [17, 41, 33], [57, 54], [27, 64], [63, 1], []], ![[26, 23, 1, 62], [37, 27, 36, 24], [50, 24], [28, 35], [0, 14], [27, 39]], ![[24, 16, 63, 44], [29, 52, 58, 28], [19, 16], [10, 25], [27, 33], [2, 39]]]
 h' := ![![[53, 57, 21], [48, 16, 21], [49, 55, 57], [48, 15, 56], [36, 20, 59], [0, 0, 1], [0, 1]], ![[10, 9, 46], [43, 17, 56], [17, 7, 60], [20, 54, 15], [65, 58, 13], [20, 18, 9], [53, 57, 21]], ![[0, 1], [54, 34, 57], [47, 5, 17], [33, 65, 63], [49, 56, 62], [15, 49, 57], [10, 9, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 35], []]
 b := ![[], [14, 57, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [9, 24, 4, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-61331, -114920, -105549, -65801, -22123]
  a := ![0, -2, -3, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![78449, 32015, 54227, -65801, -22123]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, -17, -4, -6, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-33, -17, -4, -6, 0]] 
 ![![67, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![-33, -17, -4, -6, 0], ![0, -37, -34, -8, -12], ![-120, -89, -37, -28, -8], ![-80, -108, -72, -29, -22], ![-220, -208, -108, -61, -29]]]
  hmulB := by decide  
  f := ![![![-19, 45, 58, -14, -24]], ![![-10, 3, 10, 0, -4]], ![![-9, 6, 11, -2, -4]], ![![12, 40, 32, -15, -14]], ![![4, 52, 52, -17, -23]]]
  g := ![![![7, -17, -4, -6, 0], ![28, -37, -34, -8, -12], ![45, -89, -37, -28, -8], ![68, -108, -72, -29, -22], ![116, -208, -108, -61, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -19, 4, 9, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![-37, -19, 4, 9, 0]] 
 ![![67, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![-37, -19, 4, 9, 0], ![0, -33, -38, 8, 18], ![180, 89, -33, -47, 8], ![80, 138, 108, -41, -56], ![-560, -242, 138, 136, -41]]]
  hmulB := by decide  
  f := ![![![-511, -707, -514, -185, -158]], ![![-398, -529, -374, -140, -114]], ![![-162, -215, -151, -57, -46]], ![![-541, -707, -494, -188, -150]], ![![-377, -481, -328, -129, -99]]]
  g := ![![![4, -19, 4, 9, 0], ![16, -33, -38, 8, 18], ![-15, 89, -33, -47, 8], ![-57, 138, 108, -41, -56], ![31, -242, 138, 136, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![47, 14, -6, 7, -4]] ![![-33, -17, -4, -6, 0]]
  ![![-511, -707, -514, -185, -158]] where
 M := ![![![-511, -707, -514, -185, -158]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![-511, -707, -514, -185, -158]] ![![-37, -19, 4, 9, 0]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 23, 14, 8, 4]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![21, 23, 14, 8, 4]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![25, 63, 1, 0, 0], ![58, 20, 0, 1, 0], ![68, 47, 0, 0, 1]] where
  M :=![![![21, 23, 14, 8, 4], ![80, 83, 46, 24, 16], ![160, 159, 83, 38, 24], ![200, 224, 136, 59, 30], ![300, 348, 224, 121, 59]]]
  hmulB := by decide  
  f := ![![![-2229, -215, 248, -172, 196]], ![![3920, 371, -430, 300, -344]], ![![2645, 249, -289, 202, -232]], ![![-702, -70, 80, -55, 62]], ![![448, 39, -46, 33, -39]]]
  g := ![![![-15, -17, 14, 8, 4], ![-50, -57, 46, 24, 16], ![-81, -98, 83, 38, 24], ![-122, -154, 136, 59, 30], ![-230, -267, 224, 121, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [8, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 70], [0, 1]]
 g := ![![[23, 9], [69, 27], [56, 25], [4], [60], [1]], ![[0, 62], [0, 44], [0, 46], [4], [60], [1]]]
 h' := ![![[29, 70], [16, 68], [49, 13], [68, 5], [10, 69], [63, 29], [0, 1]], ![[0, 1], [0, 3], [0, 58], [0, 66], [23, 2], [52, 42], [29, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [34, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [8, 42, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5017, 34783, 56952, -8092, 8705]
  a := ![3, -65, 2, -66, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21851, -53528, 56952, -8092, 8705]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 2, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-1, 1, 2, 1, 0]] 
 ![![71, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-1, 1, 2, 1, 0], ![0, 1, 2, 4, 2], ![20, 13, 1, 1, 4], ![40, 34, 12, -3, 0], ![0, 26, 34, 12, -3]]]
  hmulB := by decide  
  f := ![![![-1631, -287, 268, -173, 166]], ![![-964, -169, 158, -102, 98]], ![![-646, -115, 107, -69, 66]], ![![-1005, -175, 164, -106, 102]], ![![-124, -24, 22, -14, 13]]]
  g := ![![![-2, 1, 2, 1, 0], ![-4, 1, 2, 4, 2], ![-9, 13, 1, 1, 4], ![-23, 34, 12, -3, 0], ![-36, 26, 34, 12, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![69, 79, 48, 22, 14]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![69, 79, 48, 22, 14]] 
 ![![71, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![69, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![69, 79, 48, 22, 14], ![280, 285, 158, 82, 44], ![440, 483, 285, 136, 82], ![680, 712, 404, 203, 114], ![1140, 1226, 712, 347, 203]]]
  hmulB := by decide  
  f := ![![![-341, -59, 58, -2, 14]], ![![-241, -44, 40, 0, 10]], ![![-63, -10, 9, -2, 4]], ![![-319, -49, 58, -5, 12]], ![![-261, -45, 50, 1, 7]]]
  g := ![![![-96, 79, 48, 22, 14], ![-341, 285, 158, 82, 44], ![-584, 483, 285, 136, 82], ![-855, 712, 404, 203, 114], ![-1478, 1226, 712, 347, 203]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2

def I71N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 5, 6, 1, 2]] i)))

def SI71N3: IdealEqSpanCertificate' Table ![![1, 5, 6, 1, 2]] 
 ![![71, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1, 5, 6, 1, 2], ![40, 31, 10, 10, 2], ![20, 37, 31, 9, 10], ![80, 70, 32, 21, 8], ![80, 104, 70, 28, 21]]]
  hmulB := by decide  
  f := ![![![31, 9, 20, 7, -16]], ![![23, 6, 18, 7, -14]], ![![19, 4, 9, 4, -8]], ![![18, 8, 4, -1, -4]], ![![1, 5, 6, -1, -3]]]
  g := ![![![-8, 5, 6, 1, 2], ![-35, 31, 10, 10, 2], ![-52, 37, 31, 9, 10], ![-84, 70, 32, 21, 8], ![-137, 104, 70, 28, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N3 : Nat.card (O ⧸ I71N3) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N3)

lemma isPrimeI71N3 : Ideal.IsPrime I71N3 := prime_ideal_of_norm_prime hp71.out _ NI71N3
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![21, 23, 14, 8, 4]] ![![-1, 1, 2, 1, 0]]
  ![![579, 602, 334, 151, 90]] where
 M := ![![![579, 602, 334, 151, 90]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![579, 602, 334, 151, 90]] ![![69, 79, 48, 22, 14]]
  ![![560751, 596485, 343182, 169409, 97466]] where
 M := ![![![560751, 596485, 343182, 169409, 97466]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N2 : IdealMulLeCertificate' Table 
  ![![560751, 596485, 343182, 169409, 97466]] ![![1, 5, 6, 1, 2]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![52633791, 55987618, 32211706, 15900876, 9148350]]]
 hmul := by decide  
 g := ![![![![741321, 788558, 453686, 223956, 128850]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2, I71N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
    exact isPrimeI71N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1 ⊙ MulI71N2)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59, 3, 34, -12, 10]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-59, 3, 34, -12, 10]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![16, 66, 18, 28, 1]] where
  M :=![![![-59, 3, 34, -12, 10], ![200, 95, 6, 58, -24], ![-240, -41, 95, 18, 58], ![480, 228, -44, 37, 30], ![300, 398, 228, -59, 37]]]
  hmulB := by decide  
  f := ![![![1013, 103, -116, 80, -90]], ![![-1800, -183, 206, -142, 160]], ![![1600, 163, -183, 126, -142]], ![![-520, -52, 60, -41, 46]], ![![-1204, -122, 138, -95, 107]]]
  g := ![![![-3, -9, -2, -4, 10], ![8, 23, 6, 10, -24], ![-16, -53, -13, -22, 58], ![0, -24, -8, -11, 30], ![-4, -28, -6, -15, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 4 2 6 [61, 71, 63, 19, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 59, 38], [43, 71, 23, 28], [70, 15, 12, 45], [0, 1]]
 g := ![![[62, 16, 32, 57], [47, 42, 24], [12, 45, 72], [27, 66, 61, 69], [1], []], ![[55, 15, 54, 35, 18], [51, 9, 8], [43, 10, 6], [40, 30, 61, 26, 2], [65, 47, 24], [57]], ![[60, 54, 53, 72, 46, 47], [68, 8, 19], [13, 1, 16], [34, 13, 43, 38, 70, 45], [7, 11, 41], [67, 43, 54]], ![[16, 5, 42, 33, 17, 52], [34, 40, 19], [64, 67, 57], [12, 67, 51, 25, 58, 14], [38, 32, 32], [59, 54, 54]]]
 h' := ![![[14, 59, 38], [53, 14, 31, 38], [0, 49, 1, 30], [32, 41, 14, 27], [12, 2, 10, 54], [0, 0, 1], [0, 1]], ![[43, 71, 23, 28], [36, 18, 9, 31], [9, 38, 60, 64], [71, 42, 9, 15], [66, 3, 27, 59], [4, 14, 5, 43], [14, 59, 38]], ![[70, 15, 12, 45], [51, 48, 3, 51], [29, 22, 45, 26], [26, 39, 44, 69], [52, 29, 7, 27], [25, 40, 28, 48], [43, 71, 23, 28]], ![[0, 1], [8, 66, 30, 26], [29, 37, 40, 26], [65, 24, 6, 35], [41, 39, 29, 6], [60, 19, 39, 55], [70, 15, 12, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [36, 2, 53], []]
 b := ![[], [], [61, 71, 55, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 4
  hpos := by decide
  P := [61, 71, 63, 19, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5523635, 5171454, 2424778, 1052927, 874062]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-115909, -719406, -182306, -320833, 874062]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 28398241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1013, 103, -116, 80, -90]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![1013, 103, -116, 80, -90]] 
 ![![73, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![70, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![1013, 103, -116, 80, -90], ![-1800, -183, 206, -142, 160], ![1600, 163, -183, 126, -142], ![-520, -52, 60, -41, 46], ![460, 46, -52, 37, -41]]]
  hmulB := by decide  
  f := ![![![-59, 3, 34, -12, 10]], ![![-11, 2, 8, -2, 2]], ![![-34, 1, 19, -6, 6]], ![![-50, 6, 32, -11, 10]], ![![-46, 8, 32, -11, 9]]]
  g := ![![![50, 103, -116, 80, -90], ![-89, -183, 206, -142, 160], ![79, 163, -183, 126, -142], ![-26, -52, 60, -41, 46], ![22, 46, -52, 37, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-59, 3, 34, -12, 10]] ![![1013, 103, -116, 80, -90]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2001, -556, 466, -286, 238]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-2001, -556, 466, -286, 238]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![53, 76, 71, 30, 1]] where
  M :=![![![-2001, -556, 466, -286, 238], ![4760, 1321, -1112, 694, -572], ![-5720, -1608, 1321, -826, 694], ![4560, 1304, -1052, 627, -540], ![-5400, -1486, 1304, -782, 627]]]
  hmulB := by decide  
  f := ![![![1, 8, 6, 2, 2]], ![![40, 31, 16, 10, 4]], ![![40, 52, 31, 14, 10]], ![![80, 80, 44, 21, 12]], ![![107, 114, 65, 32, 19]]]
  g := ![![![-185, -236, -208, -94, 238], ![444, 567, 500, 226, -572], ![-538, -688, -607, -274, 694], ![420, 536, 472, 213, -540], ![-489, -622, -547, -248, 627]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 4 2 6 [3, 30, 30, 54, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 26, 37, 32], [31, 0, 76, 62], [69, 52, 45, 64], [0, 1]]
 g := ![![[25, 70, 16, 67], [31, 46, 40, 51], [9, 18, 63, 22], [49, 0, 63, 72], [1], []], ![[23, 32, 29, 33, 25, 50], [19, 30, 26, 6, 34, 10], [34, 0, 64, 76, 38, 16], [3, 44, 41, 13, 52, 21], [31, 48, 49], [13, 2, 76]], ![[4, 33, 5, 54, 63, 76], [78, 61, 58, 62, 50, 55], [44, 13, 41, 30, 55, 13], [66, 70, 11, 56, 16, 4], [62, 19, 32], [3, 59, 52]], ![[1, 14, 31, 49, 13, 10], [39, 20, 33, 3, 5, 22], [20, 41, 7, 0, 10, 10], [26, 9, 78, 49, 54, 38], [68, 12, 32], [23, 9, 67]]]
 h' := ![![[4, 26, 37, 32], [65, 56, 0, 15], [52, 34, 39, 50], [11, 40, 22, 41], [76, 49, 49, 25], [0, 0, 1], [0, 1]], ![[31, 0, 76, 62], [5, 35, 4, 58], [56, 7, 11, 5], [0, 72, 15, 44], [41, 69, 27, 48], [56, 49, 57, 7], [4, 26, 37, 32]], ![[69, 52, 45, 64], [24, 46, 10, 68], [26, 63, 65, 39], [0, 24, 23, 56], [67, 55, 34, 24], [4, 49, 10, 36], [31, 0, 76, 62]], ![[0, 1], [23, 21, 65, 17], [67, 54, 43, 64], [13, 22, 19, 17], [46, 64, 48, 61], [31, 60, 11, 36], [69, 52, 45, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [55, 19, 43], []]
 b := ![[], [], [10, 37, 64, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 4
  hpos := by decide
  P := [3, 30, 30, 54, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1304160158, 1338200207, 726570084, 316633480, 194731389]
  a := ![1, 18, 4, 17, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-114134221, -170397283, -165814665, -69940610, 194731389]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 38950081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -8, -6, -2, -2]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-1, -8, -6, -2, -2]] 
 ![![79, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-1, -8, -6, -2, -2], ![-40, -31, -16, -10, -4], ![-40, -52, -31, -14, -10], ![-80, -80, -44, -21, -12], ![-120, -134, -80, -38, -21]]]
  hmulB := by decide  
  f := ![![![2001, 556, -466, 286, -238]], ![![421, 117, -98, 60, -50]], ![![503, 140, -117, 72, -60]], ![![1614, 448, -376, 231, -192]], ![![195, 54, -46, 28, -23]]]
  g := ![![![5, -8, -6, -2, -2], ![19, -31, -16, -10, -4], ![31, -52, -31, -14, -10], ![46, -80, -44, -21, -12], ![81, -134, -80, -38, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-2001, -556, 466, -286, 238]] ![![-1, -8, -6, -2, -2]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


def P83P0 : CertificateIrreducibleZModOfList' 83 5 2 6 [44, 51, 66, 13, 40, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 71, 8, 21, 68], [22, 25, 0, 21, 29], [63, 3, 26, 66, 33], [36, 66, 49, 58, 36], [0, 1]]
 g := ![![[81, 14, 70, 46, 7], [49, 59, 49, 78, 36], [48, 43, 22, 10], [6, 18, 37, 23], [1], []], ![[46, 58, 35, 58, 4, 51, 40, 10], [56, 57, 69, 80, 7, 42, 37, 7], [77, 24, 79, 26], [61, 36, 12, 29], [23, 43, 82, 64, 53, 21, 20, 1], [0, 12, 81, 59]], ![[63, 78, 66, 64, 59, 48, 77, 65], [75, 67, 44, 19, 43, 77, 53, 77], [70, 14, 78, 16], [29, 21], [40, 81, 73, 48, 44, 43, 61, 1], [70, 54, 31, 11]], ![[39, 6, 30, 54, 73, 61, 11, 31], [48, 25, 45, 36, 32, 70, 65, 21], [42, 47, 45, 48], [2, 73, 39, 25], [63, 19, 19, 10, 80, 26, 42, 44], [66, 7, 55, 10]], ![[26, 32, 43, 68, 64, 56, 50, 17], [61, 33, 34, 16, 6, 1, 15, 75], [40, 16, 15, 4], [73, 30, 75, 12], [5, 46, 63, 24, 72, 78], [50, 54, 61, 51]]]
 h' := ![![[5, 71, 8, 21, 68], [2, 46, 41, 5, 16], [24, 79, 50, 81, 77], [12, 70, 72, 59, 50], [39, 32, 17, 70, 43], [0, 0, 1], [0, 1]], ![[22, 25, 0, 21, 29], [58, 27, 47, 36, 44], [40, 4, 51, 15, 49], [5, 9, 29, 3, 62], [38, 75, 17, 9, 19], [25, 16, 32, 52, 29], [5, 71, 8, 21, 68]], ![[63, 3, 26, 66, 33], [44, 46, 19, 77, 51], [61, 10, 13, 47, 55], [53, 2, 82, 69, 4], [1, 82, 39, 42], [60, 51, 21, 29, 35], [22, 25, 0, 21, 29]], ![[36, 66, 49, 58, 36], [26, 33, 6, 22, 29], [1, 6, 49, 38, 71], [43, 22, 80, 58, 52], [31, 19, 5, 4, 78], [69, 24, 53, 6, 19], [63, 3, 26, 66, 33]], ![[0, 1], [37, 14, 53, 26, 26], [46, 67, 3, 68, 80], [48, 63, 69, 60, 81], [40, 41, 5, 41, 26], [9, 75, 59, 79], [36, 66, 49, 58, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 30, 77, 13], [], [], []]
 b := ![[], [2, 7, 55, 72, 23], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 5
  hpos := by decide
  P := [44, 51, 66, 13, 40, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![397156245, 1213832006, 1097633666, -1119427308, -1197536201]
  a := ![-1, 2, -4, 4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4785015, 14624482, 13224502, -13487076, -14428147]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -21, -12, -6, -4]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-19, -21, -12, -6, -4]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![45, 69, 1, 0, 0], ![10, 68, 0, 1, 0], ![55, 30, 0, 0, 1]] where
  M :=![![![-19, -21, -12, -6, -4], ![-80, -79, -42, -20, -12], ![-120, -133, -79, -36, -20], ![-160, -180, -112, -59, -30], ![-300, -316, -180, -97, -59]]]
  hmulB := by decide  
  f := ![![![429, 75, -70, 46, -44]], ![![-880, -169, 150, -96, 92]], ![![-455, -91, 79, -50, 48]], ![![-630, -122, 108, -69, 66]], ![![-25, -9, 6, -3, 3]]]
  g := ![![![9, 15, -12, -6, -4], ![30, 51, -42, -20, -12], ![55, 94, -79, -36, -20], ![80, 140, -112, -59, -30], ![135, 230, -180, -97, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [58, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 88], [0, 1]]
 g := ![![[11, 40], [88], [68], [58, 42], [56, 47], [1]], ![[34, 49], [88], [68], [51, 47], [63, 42], [1]]]
 h' := ![![[74, 88], [9, 29], [29, 34], [18, 54], [45, 65], [31, 74], [0, 1]], ![[0, 1], [19, 60], [53, 55], [9, 35], [49, 24], [78, 15], [74, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [53, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [58, 15, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-742, 2150, 3036, -2940, 542]
  a := ![0, -10, 4, -20, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1548, -266, 3036, -2940, 542]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1181, -175, 94, -106, 90]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-1181, -175, 94, -106, 90]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![17, 59, 1, 0, 0], ![65, 88, 0, 1, 0], ![17, 47, 0, 0, 1]] where
  M :=![![![-1181, -175, 94, -106, 90], ![1800, -7, -350, 98, -212], ![-2120, -547, -7, -244, 98], ![80, -472, -372, -105, -138], ![-1380, -974, -472, -303, -105]]]
  hmulB := by decide  
  f := ![![![1091, 293, -268, 170, -130]], ![![-2600, -737, 586, -406, 340]], ![![-1477, -421, 329, -232, 196]], ![![-1805, -523, 392, -281, 244]], ![![-1137, -328, 250, -175, 151]]]
  g := ![![![29, -7, 94, -106, 90], ![56, 247, -350, 98, -212], ![137, 188, -7, -244, 98], ![175, 418, -372, -105, -138], ![316, 657, -472, -303, -105]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [7, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 88], [0, 1]]
 g := ![![[7, 39], [21], [42], [20, 36], [72, 87], [1]], ![[54, 50], [21], [42], [36, 53], [81, 2], [1]]]
 h' := ![![[40, 88], [80, 22], [82, 33], [38, 24], [30, 6], [82, 40], [0, 1]], ![[0, 1], [70, 67], [67, 56], [19, 65], [3, 83], [80, 49], [40, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [58, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [7, 49, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![973, 197, -134, 389, 86]
  a := ![13, 0, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-264, -339, -134, 389, 86]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 5, -2, -2, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![11, 5, -2, -2, 0]] 
 ![![89, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![11, 5, -2, -2, 0], ![0, 9, 10, -4, -4], ![-40, -19, 9, 12, -4], ![-40, -44, -24, 13, 14], ![140, 52, -44, -31, 13]]]
  hmulB := by decide  
  f := ![![![-10021, -1019, 1140, -790, 888]], ![![-1039, -106, 118, -82, 92]], ![![-8397, -854, 955, -662, 744]], ![![-4222, -430, 480, -333, 374]], ![![-6582, -670, 748, -519, 583]]]
  g := ![![![2, 5, -2, -2, 0], ![-5, 9, 10, -4, -4], ![-8, -19, 9, 12, -4], ![10, -44, -24, 13, 14], ![36, 52, -44, -31, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-19, -21, -12, -6, -4]] ![![-1181, -175, 94, -106, 90]]
  ![![15119, 16764, 9768, 4726, 2814]] where
 M := ![![![15119, 16764, 9768, 4726, 2814]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![15119, 16764, 9768, 4726, 2814]] ![![11, 5, -2, -2, 0]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-19491, -20737, -11926, -5874, -3382]]]
 hmul := by decide  
 g := ![![![![-219, -233, -134, -66, -38]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 88, 68, 22, 22]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![47, 88, 68, 22, 22]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![77, 32, 56, 1, 0], ![53, 69, 0, 0, 1]] where
  M :=![![![47, 88, 68, 22, 22], ![440, 379, 176, 114, 44], ![440, 572, 379, 154, 114], ![920, 904, 484, 265, 132], ![1320, 1494, 904, 418, 265]]]
  hmulB := by decide  
  f := ![![![-49, -4, 4, -6, 6]], ![![120, 27, -8, 2, -12]], ![![-120, -16, 27, -2, 2]], ![![-69, -4, 16, -5, 2]], ![![59, 17, -4, -2, -5]]]
  g := ![![![-29, -22, -12, 22, 22], ![-110, -65, -64, 114, 44], ![-180, -126, -85, 154, 114], ![-273, -172, -148, 265, 132], ![-463, -311, -232, 418, 265]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [34, 76, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 9, 19], [56, 87, 78], [0, 1]]
 g := ![![[57, 87, 2], [45, 72], [39, 48], [45, 22], [56, 66], [1]], ![[16, 24, 79, 59], [74, 32], [40, 81], [13, 73], [50, 72], [28, 89, 72, 69]], ![[25, 94, 95, 74], [66, 6], [5, 73], [4, 31], [2, 94], [18, 89, 9, 28]]]
 h' := ![![[2, 9, 19], [11, 44, 14], [59, 9, 13], [30, 4, 57], [28, 26, 64], [63, 21, 58], [0, 1]], ![[56, 87, 78], [3, 89, 17], [71, 80, 41], [49, 54, 88], [43, 50, 48], [26, 95, 13], [2, 9, 19]], ![[0, 1], [9, 61, 66], [33, 8, 43], [94, 39, 49], [91, 21, 82], [16, 78, 26], [56, 87, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23], []]
 b := ![[], [46, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [34, 76, 39, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16404, 4759, 11426, -24479, 9542]
  a := ![-1, -4, 2, -5, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14049, 1337, 14250, -24479, 9542]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49, 4, -4, 6, -6]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![49, 4, -4, 6, -6]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![1, 41, 1, 0, 0], ![56, 66, 0, 1, 0], ![31, 38, 0, 0, 1]] where
  M :=![![![49, 4, -4, 6, -6], ![-120, -27, 8, -2, 12], ![120, 16, -27, 2, -2], ![40, 48, 12, -25, -4], ![-40, 2, 48, 14, -25]]]
  hmulB := by decide  
  f := ![![![-47, -88, -68, -22, -22]], ![![-440, -379, -176, -114, -44]], ![![-191, -167, -79, -50, -20]], ![![-336, -318, -164, -93, -44]], ![![-201, -192, -100, -56, -27]]]
  g := ![![![-1, 0, -4, 6, -6], ![-4, -7, 8, -2, 12], ![1, 11, -27, 2, -2], ![16, 14, 12, -25, -4], ![-1, -20, 48, 14, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [56, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 96], [0, 1]]
 g := ![![[88, 94], [93], [54], [43], [2], [19, 1]], ![[31, 3], [93], [54], [43], [2], [38, 96]]]
 h' := ![![[19, 96], [83, 26], [76, 53], [53, 32], [91, 25], [3, 14], [0, 1]], ![[0, 1], [92, 71], [16, 44], [79, 65], [81, 72], [75, 83], [19, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [32, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [56, 78, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-821, -361, 1199, -1582, 1225]
  a := ![3, -4, 7, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![501, 86, 1199, -1582, 1225]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![47, 88, 68, 22, 22]] ![![49, 4, -4, 6, -6]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![351, 68, -78, 41, -42]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![351, 68, -78, 41, -42]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![87, 24, 57, 1, 0], ![91, 17, 7, 0, 1]] where
  M :=![![![351, 68, -78, 41, -42], ![-840, -231, 136, -114, 82], ![820, 140, -231, 95, -114], ![-720, -274, 72, -117, 54], ![540, 0, -274, 45, -117]]]
  hmulB := by decide  
  f := ![![![-29, -18, 2, 9, 0]], ![![0, -27, -36, 4, 18]], ![![180, 90, -27, -45, 4]], ![![77, 30, -21, -17, 6]], ![![-19, -17, -5, 7, 3]]]
  g := ![![![6, -2, -21, 41, -42], ![16, 11, 60, -114, 82], ![29, -2, -48, 95, -114], ![45, 16, 63, -117, 54], ![72, 9, -20, 45, -117]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [55, 54, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 57, 77], [74, 43, 24], [0, 1]]
 g := ![![[57, 84, 24], [7, 88], [77, 71, 5], [], [19, 52], [1]], ![[72, 82, 96, 47], [0, 95], [72, 21, 97, 95], [35, 64], [21, 56], [81, 75, 22, 13]], ![[79, 32, 93, 64], [80, 85], [36, 5, 45, 56], [97, 64], [55, 79], [27, 24, 68, 88]]]
 h' := ![![[97, 57, 77], [68, 18, 23], [7, 71, 47], [85, 7, 45], [61, 34], [46, 47, 70], [0, 1]], ![[74, 43, 24], [31, 50, 52], [58, 15, 14], [64, 22, 50], [26, 19, 93], [26, 95, 64], [97, 57, 77]], ![[0, 1], [77, 33, 26], [72, 15, 40], [96, 72, 6], [52, 48, 8], [42, 60, 68], [74, 43, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 76], []]
 b := ![[], [20, 53, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [55, 54, 31, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12581, 7867, 790, 23205, 31410]
  a := ![1, 0, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-48164, -10723, -15265, 23205, 31410]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -10, 8, -5, 4]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-31, -10, 8, -5, 4]] 
 ![![101, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![96, 0, 0, 1, 0], ![80, 0, 0, 0, 1]] where
  M :=![![![-31, -10, 8, -5, 4], ![80, 25, -20, 12, -10], ![-100, -30, 25, -15, 12], ![80, 22, -20, 13, -10], ![-100, -30, 22, -15, 13]]]
  hmulB := by decide  
  f := ![![![29, -20, -24, -5, -6]], ![![8, -7, -8, -2, -2]], ![![26, -20, -23, -5, -6]], ![![24, -22, -24, -5, -6]], ![![20, -20, -22, -5, -5]]]
  g := ![![![-3, -10, 8, -5, 4], ![8, 25, -20, 12, -10], ![-10, -30, 25, -15, 12], ![8, 22, -20, 13, -10], ![-8, -30, 22, -15, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -12, 2, 6, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-21, -12, 2, 6, 0]] 
 ![![101, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![-21, -12, 2, 6, 0], ![0, -19, -24, 4, 12], ![120, 60, -19, -30, 4], ![40, 84, 72, -23, -36], ![-360, -160, 84, 90, -23]]]
  hmulB := by decide  
  f := ![![![9839, 2692, -2246, 1394, -1168]], ![![5224, 1429, -1192, 740, -620]], ![![4952, 1356, -1131, 702, -588]], ![![3878, 1060, -884, 549, -460]], ![![3764, 1032, -860, 534, -447]]]
  g := ![![![3, -12, 2, 6, 0], ![16, -19, -24, 4, 12], ![-12, 60, -19, -30, 4], ![-58, 84, 72, -23, -36], ![16, -160, 84, 90, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![351, 68, -78, 41, -42]] ![![-31, -10, 8, -5, 4]]
  ![![9839, 2692, -2246, 1394, -1168]] where
 M := ![![![9839, 2692, -2246, 1394, -1168]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![9839, 2692, -2246, 1394, -1168]] ![![-21, -12, 2, 6, 0]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 22, -38, -17, 16]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![83, 22, -38, -17, 16]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![32, 42, 3, 1, 0], ![7, 46, 33, 0, 1]] where
  M :=![![![83, 22, -38, -17, 16], ![320, 237, 44, -92, -34], ![-340, -22, 237, 61, -92], ![-1080, -722, -44, 329, 78], ![780, -94, -722, -83, 329]]]
  hmulB := by decide  
  f := ![![![-4059, -420, 470, -323, 362]], ![![7240, 755, -840, 578, -646]], ![![-6460, -676, 755, -517, 578]], ![![1524, 160, -177, 122, -136]], ![![869, 90, -99, 69, -77]]]
  g := ![![![5, 0, -5, -17, 16], ![34, 55, 14, -92, -34], ![-16, 16, 30, 61, -92], ![-118, -176, -35, 329, 78], ![11, -114, -110, -83, 329]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [18, 79, 77, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 36, 16], [2, 66, 87], [0, 1]]
 g := ![![[33], [54, 69, 25], [53, 3, 46], [16, 76], [78, 58], [1]], ![[47, 39, 18, 32], [62, 64, 12, 28], [70, 22, 84, 36], [35, 52], [54, 55], [3, 94, 38, 79]], ![[64, 52, 79, 71], [49, 9, 74, 27], [23, 36, 34, 42], [98, 18], [9, 30], [99, 7, 18, 24]]]
 h' := ![![[24, 36, 16], [58, 62], [76, 14, 5], [49, 41, 47], [53, 67, 73], [85, 24, 26], [0, 1]], ![[2, 66, 87], [1, 69, 65], [45, 81, 39], [14, 13, 50], [52, 6, 19], [71, 24, 40], [24, 36, 16]], ![[0, 1], [79, 75, 38], [74, 8, 59], [55, 49, 6], [58, 30, 11], [80, 55, 37], [2, 66, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 5], []]
 b := ![[], [56, 66, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [18, 79, 77, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1130, 893, 1133, -1484, 369]
  a := ![4, 1, -1, 2, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![425, 449, -64, -1484, 369]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, 0, 0, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![3, 1, 0, 0, 0]] 
 ![![103, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![3, 1, 0, 0, 0], ![0, 3, 2, 0, 0], ![0, 1, 3, 2, 0], ![0, 0, 0, 3, 2], ![20, 12, 0, -1, 3]]]
  hmulB := by decide  
  f := ![![![-19, -33, 22, -12, 8]], ![![1, 0, 0, 0, 0]], ![![-11, -16, 11, -6, 4]], ![![-3, -9, 6, -3, 2]], ![![-5, -3, 2, -1, 1]]]
  g := ![![![0, 1, 0, 0, 0], ![-1, 3, 2, 0, 0], ![-2, 1, 3, 2, 0], ![-1, 0, 0, 3, 2], ![0, 12, 0, -1, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, 1, -24, -5, 10]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![33, 1, -24, -5, 10]] 
 ![![103, 0, 0, 0, 0], ![94, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![33, 1, -24, -5, 10], ![200, 129, 2, -58, -10], ![-100, 41, 129, 7, -58], ![-680, -398, 40, 187, 12], ![120, -248, -398, 34, 187]]]
  hmulB := by decide  
  f := ![![![1631, 185, -554, 169, -260]], ![![1438, 149, -502, 146, -234]], ![![207, 16, -79, 20, -36]], ![![798, 64, -296, 77, -136]], ![![589, 37, -232, 55, -105]]]
  g := ![![![1, 1, -24, -5, 10], ![-82, 129, 2, -58, -10], ![-35, 41, 129, 7, -58], ![250, -398, 40, 187, 12], ![185, -248, -398, 34, 187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![83, 22, -38, -17, 16]] ![![3, 1, 0, 0, 0]]
  ![![569, 303, -70, -143, 14]] where
 M := ![![![569, 303, -70, -143, 14]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![569, 303, -70, -143, 14]] ![![33, 1, -24, -5, 10]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![185297, 90228, -33372, -47174, 7622]]]
 hmul := by decide  
 g := ![![![![1799, 876, -324, -458, 74]]]]
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


lemma PB547I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB547I2 : PrimesBelowBoundCertificateInterval O 61 103 547 where
  m := 9
  g := ![3, 4, 2, 2, 1, 3, 2, 3, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB547I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N2, I71N3]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
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
    · exact ![300763, 67, 67]
    · exact ![5041, 71, 71, 71]
    · exact ![28398241, 73]
    · exact ![38950081, 79]
    · exact ![3939040643]
    · exact ![7921, 7921, 89]
    · exact ![912673, 9409]
    · exact ![1030301, 101, 101]
    · exact ![1092727, 103, 103]
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
      exact NI71N3
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
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
  β := ![I67N1, I67N2, I71N1, I71N2, I71N3, I73N1, I79N1, I89N2, I101N1, I101N2, I103N1, I103N2]
  Il := ![[I67N1, I67N2], [I71N1, I71N2, I71N3], [I73N1], [I79N1], [], [I89N2], [], [I101N1, I101N2], [I103N1, I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
