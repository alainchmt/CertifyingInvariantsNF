
import IdealArithmetic.Examples.NF5_3_303750000_1.RI5_3_303750000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![69, 106, 72, 32, 48]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![69, 106, 72, 32, 48]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![14, 5, 35, 23, 1]] where
  M :=![![![69, 106, 72, 32, 48], ![372, 487, 528, 56, 352], ![320, 478, 331, 162, 176], ![2324, 2974, 3264, 401, 2176], ![1652, 2332, 1986, 570, 1257]]]
  hmulB := by decide  
  f := ![![![-1521, -74, -360, -64, 240]], ![![204, 13, 48, 8, -32]], ![![704, 34, 169, 30, -112]], ![![812, 34, 192, 35, -128]], ![![346, 15, 83, 15, -55]]]
  g := ![![![-9, -2, -24, -16, 48], ![-68, -19, -176, -120, 352], ![-32, -6, -87, -58, 176], ![-420, -118, -1088, -741, 2176], ![-238, -59, -627, -423, 1257]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [5, 51, 23, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 37, 37, 38], [4, 24, 66, 35], [60, 5, 31, 61], [0, 1]]
 g := ![![[53, 36, 56, 25], [36, 7, 18, 37], [29, 21, 1], [60], [1], []], ![[62, 19, 29, 8, 10, 43], [0, 49, 1, 19, 62, 41], [24, 51, 59], [42, 63, 64], [55, 37, 62], [47, 65, 37]], ![[60, 24, 8, 47, 33, 17], [45, 52, 33, 33, 27, 56], [18, 6, 29], [37, 40, 15], [17, 13, 4], [38, 64, 19]], ![[44, 62, 52, 44, 7, 3], [8, 13, 59, 25, 30, 18], [20, 10, 54], [16, 43, 29], [49, 35, 10], [6, 30, 36]]]
 h' := ![![[3, 37, 37, 38], [21, 42, 48, 62], [38, 13, 2, 38], [60, 63, 44, 1], [62, 16, 44], [0, 0, 1], [0, 1]], ![[4, 24, 66, 35], [44, 53, 11, 33], [38, 5, 45, 15], [15, 45, 40, 40], [15, 3, 17, 59], [42, 46, 25, 53], [3, 37, 37, 38]], ![[60, 5, 31, 61], [31, 66, 12, 49], [59, 49, 25, 22], [22, 12, 20, 37], [41, 64, 60, 45], [27, 11, 20, 2], [4, 24, 66, 35]], ![[0, 1], [19, 40, 63, 57], [7, 0, 62, 59], [43, 14, 30, 56], [49, 51, 13, 30], [19, 10, 21, 12], [60, 5, 31, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [42, 29, 17], []]
 b := ![[], [], [65, 26, 55, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 4
  hpos := by decide
  P := [5, 51, 23, 0, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![346377950081, 418814231595, 531069262143, 20185149456, 365320119372]
  a := ![-20, -41, -39, 24, -100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-71165727181, -21011736795, -182912461431, -125107128300, 365320119372]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1521, -74, -360, -64, 240]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-1521, -74, -360, -64, 240]] 
 ![![67, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![-1521, -74, -360, -64, 240], ![204, 13, 48, 8, -32], ![704, 34, 169, 30, -112], ![812, 34, 192, 35, -128], ![140, 4, 30, 6, -21]]]
  hmulB := by decide  
  f := ![![![69, 106, 72, 32, 48]], ![![21, 31, 24, 8, 16]], ![![47, 72, 49, 22, 32]], ![![80, 114, 96, 27, 64]], ![![71, 106, 78, 30, 51]]]
  g := ![![![95, -74, -360, -64, 240], ![-13, 13, 48, 8, -32], ![-45, 34, 169, 30, -112], ![-50, 34, 192, 35, -128], ![-7, 4, 30, 6, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![69, 106, 72, 32, 48]] ![![-1521, -74, -360, -64, 240]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1955, 90, 458, 81, -311]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![1955, 90, 458, 81, -311]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![37, 41, 38, 1, 0], ![57, 25, 5, 0, 1]] where
  M :=![![![1955, 90, 458, 81, -311], ![-280, -36, -85, -15, 26], ![-920, -66, -231, -44, 132], ![-1156, -197, -393, -70, 70], ![-262, -119, -141, -33, -33]]]
  hmulB := by decide  
  f := ![![![11, -44, 26, 11, -11]], ![![-88, -92, -169, -7, 66]], ![![0, 136, -11, -26, 8]], ![![-43, -1, -86, -12, 35]], ![![-21, -59, -37, 5, 14]]]
  g := ![![![235, 64, -15, 81, -311], ![-17, -1, 5, -15, 26], ![-96, -22, 11, -44, 132], ![-36, 13, 27, -70, 70], ![40, 29, 18, -33, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [1, 27, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 59, 31], [10, 11, 40], [0, 1]]
 g := ![![[28, 3, 1], [45, 42, 36], [66, 69, 8], [54, 27], [53, 1], []], ![[26, 43, 49, 13], [69, 69, 56, 34], [70, 18, 3, 46], [65, 43], [50, 50], [63, 38]], ![[38, 55, 33, 38], [41, 38, 42, 50], [39, 40, 63, 1], [54, 9], [58, 2], [54, 38]]]
 h' := ![![[43, 59, 31], [26, 46, 1], [5, 49, 65], [57, 0, 47], [18, 59, 13], [0, 0, 1], [0, 1]], ![[10, 11, 40], [27, 14, 17], [58, 63, 33], [6, 48, 20], [0, 47, 55], [11, 69, 11], [43, 59, 31]], ![[0, 1], [35, 11, 53], [6, 30, 44], [18, 23, 4], [70, 36, 3], [46, 2, 59], [10, 11, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 46], []]
 b := ![[], [61, 39, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [1, 27, 18, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-450804879, -516030997, -740850465, 17360527, -521056110]
  a := ![-37, -75, -76, 33, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![402916252, 166177326, 16968029, 17360527, -521056110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -44, 26, 11, -11]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![11, -44, 26, 11, -11]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![42, 44, 1, 0, 0], ![51, 53, 0, 1, 0], ![46, 19, 0, 0, 1]] where
  M :=![![![11, -44, 26, 11, -11], ![-88, -92, -169, -7, 66], ![0, 136, -11, -26, 8], ![148, 161, 279, 16, -118], ![82, -61, 171, 33, -69]]]
  hmulB := by decide  
  f := ![![![1955, 90, 458, 81, -311]], ![![-280, -36, -85, -15, 26]], ![![970, 30, 215, 38, -166]], ![![1179, 35, 260, 46, -203]], ![![1188, 47, 272, 48, -195]]]
  g := ![![![-16, -22, 26, 11, -11], ![61, 91, -169, -7, 66], ![20, 26, -11, -26, 8], ![-98, -151, 279, 16, -118], ![-79, -113, 171, 33, -69]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [40, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 70], [0, 1]]
 g := ![![[30, 16], [49, 64], [44, 29], [16], [49], [1]], ![[0, 55], [0, 7], [34, 42], [16], [49], [1]]]
 h' := ![![[7, 70], [28, 67], [15, 8], [24, 10], [66, 67], [31, 7], [0, 1]], ![[0, 1], [0, 4], [0, 63], [23, 61], [38, 4], [9, 64], [7, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [30, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [40, 64, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5523, 5897, 9514, -599, 6458]
  a := ![-5, -11, -10, 6, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9304, -7094, 9514, -599, 6458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![1955, 90, 458, 81, -311]] ![![11, -44, 26, 11, -11]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -1, 1, 3, -4]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![5, -1, 1, 3, -4]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![54, 19, 51, 1, 0], ![21, 51, 38, 0, 1]] where
  M :=![![![5, -1, 1, 3, -4], ![-4, -12, 3, -9, 16], ![-4, 16, -19, 10, -12], ![20, -7, 95, -50, 60], ![8, 11, -1, 17, -19]]]
  hmulB := by decide  
  f := ![![![25, 3, 7, 1, -4]], ![![0, 0, 5, 1, 0]], ![![-12, -2, -5, 0, 4]], ![![10, 1, 3, 1, 0]], ![![1, 0, 3, 1, 1]]]
  g := ![![![-1, 2, 0, 3, -4], ![2, -9, -2, -9, 16], ![-4, 6, -1, 10, -12], ![20, -29, 5, -50, 60], ![-7, 9, -2, 17, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [38, 53, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 66, 26], [18, 6, 47], [0, 1]]
 g := ![![[65, 53, 54], [64, 9], [59, 38], [49, 7, 38], [30, 1], []], ![[7, 33, 46, 26], [19, 18], [52, 36], [13, 7, 72, 13], [55, 36], [60, 19]], ![[32, 57, 43, 34], [67, 35], [48, 18], [20, 37, 6, 56], [43, 49], [39, 19]]]
 h' := ![![[12, 66, 26], [59, 2, 28], [3, 63, 3], [36, 38, 29], [28, 51, 44], [0, 0, 1], [0, 1]], ![[18, 6, 47], [62, 52, 1], [45, 51, 50], [14, 37, 67], [23, 70, 57], [54, 18, 6], [12, 66, 26]], ![[0, 1], [10, 19, 44], [72, 32, 20], [61, 71, 50], [72, 25, 45], [10, 55, 66], [18, 6, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 17], []]
 b := ![[], [67, 3, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [38, 53, 43, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1828310658, 2070021093, 3051172572, -115695408, 2174879451]
  a := ![46, 95, 92, -54, 215]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-515021997, -1460967372, -1009503846, -115695408, 2174879451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 3, 7, 1, -4]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![25, 3, 7, 1, -4]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![20, 24, 1, 0, 0], ![46, 26, 0, 1, 0], ![22, 66, 0, 0, 1]] where
  M :=![![![25, 3, 7, 1, -4], ![0, 0, 5, 1, 0], ![-12, -2, -5, 0, 4], ![-8, 13, 1, 0, 12], ![4, 13, 7, 1, 5]]]
  hmulB := by decide  
  f := ![![![5, -1, 1, 3, -4]], ![![-4, -12, 3, -9, 16]], ![![0, -4, 1, -2, 4]], ![![2, -5, 3, -2, 4]], ![![-2, -11, 3, -7, 13]]]
  g := ![![![-1, 1, 7, 1, -4], ![-2, -2, 5, 1, 0], ![0, -2, -5, 0, 4], ![-4, -11, 1, 0, 12], ![-4, -7, 7, 1, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [51, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 72], [0, 1]]
 g := ![![[34, 46], [41], [8], [44, 69], [32], [1]], ![[59, 27], [41], [8], [45, 4], [32], [1]]]
 h' := ![![[18, 72], [45, 22], [26, 48], [19, 9], [20, 54], [22, 18], [0, 1]], ![[0, 1], [3, 51], [14, 25], [35, 64], [43, 19], [54, 55], [18, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [33, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [51, 55, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![182147, 198119, 333383, -43348, 264431]
  a := ![-27, -60, -55, 38, -147]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-141219, -330527, 333383, -43348, 264431]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![5, -1, 1, 3, -4]] ![![25, 3, 7, 1, -4]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -9, 21, -16, 19]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![1, -9, 21, -16, 19]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![15, 50, 1, 0, 0], ![38, 68, 0, 1, 0], ![3, 14, 0, 0, 1]] where
  M :=![![![1, -9, 21, -16, 19], ![-12, 37, -102, 72, -90], ![12, -54, 127, -94, 112], ![-72, 204, -582, 405, -506], ![6, -72, 138, -112, 125]]]
  hmulB := by decide  
  f := ![![![-131, -33, -39, -2, 23]], ![![-24, 7, -78, -12, 30]], ![![-39, -1, -56, -8, 23]], ![![-82, -10, -84, -11, 36]], ![![-9, -1, -15, -2, 6]]]
  g := ![![![3, -3, 21, -16, 19], ![-12, 19, -102, 72, -90], ![17, -20, 127, -94, 112], ![-66, 112, -582, 405, -506], ![23, -14, 138, -112, 125]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [10, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 78], [0, 1]]
 g := ![![[1, 8], [61, 76], [6, 13], [15, 21], [21], [1]], ![[0, 71], [12, 3], [34, 66], [42, 58], [21], [1]]]
 h' := ![![[69, 78], [22, 18], [19, 32], [8, 48], [48, 69], [69, 69], [0, 1]], ![[0, 1], [0, 61], [15, 47], [2, 31], [69, 10], [11, 10], [69, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [13, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [10, 10, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4282, -548, 18548, -10556, 15168]
  a := ![2, 16, 14, -18, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1034, -5348, 18548, -10556, 15168]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -2, -8, -1, 5]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-37, -2, -8, -1, 5]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![24, 75, 1, 0, 0], ![5, 30, 0, 1, 0], ![32, 15, 0, 0, 1]] where
  M :=![![![-37, -2, -8, -1, 5], ![4, -4, 1, -1, 2], ![16, 4, -1, 2, -4], ![24, 3, 21, -8, 6], ![6, 3, 3, 3, -5]]]
  hmulB := by decide  
  f := ![![![3, 8, 8, 1, 1]], ![![20, 12, 29, 7, 10]], ![![20, 14, 30, 7, 10]], ![![9, 7, 13, 3, 5]], ![![6, 7, 10, 2, 3]]]
  g := ![![![0, 7, -8, -1, 5], ![-1, -1, 1, -1, 2], ![2, 1, -1, 2, -4], ![-8, -18, 21, -8, 6], ![1, -3, 3, 3, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [14, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 78], [0, 1]]
 g := ![![[11, 9], [5, 2], [63, 73], [54, 13], [16], [1]], ![[47, 70], [13, 77], [39, 6], [27, 66], [16], [1]]]
 h' := ![![[4, 78], [9, 3], [66, 70], [34, 28], [51, 31], [65, 4], [0, 1]], ![[0, 1], [21, 76], [30, 9], [67, 51], [17, 48], [2, 75], [4, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [71, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [14, 75, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![646126, 749840, 1079766, -62393, 856549]
  a := ![60, 102, 106, -52, 251]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-662859, -1154545, 1079766, -62393, 856549]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -5, 1, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-3, -5, 1, 1, 0]] 
 ![![79, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![-3, -5, 1, 1, 0], ![-8, -6, -17, -1, 8], ![4, 16, 3, -2, 0], ![24, 21, 39, 4, -8], ![12, -3, 21, 5, -3]]]
  hmulB := by decide  
  f := ![![![7, -127, 317, -235, 288]], ![![3, -81, 202, -150, 184]], ![![8, -106, 265, -196, 240]], ![![-6, -45, 111, -84, 104]], ![![8, -101, 253, -187, 229]]]
  g := ![![![2, -5, 1, 1, 0], ![12, -6, -17, -1, 8], ![-12, 16, 3, -2, 0], ![-41, 21, 39, 4, -8], ![-15, -3, 21, 5, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![1, -9, 21, -16, 19]] ![![-37, -2, -8, -1, 5]]
  ![![-7, 127, -317, 235, -288]] where
 M := ![![![-7, 127, -317, 235, -288]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-7, 127, -317, 235, -288]] ![![-3, -5, 1, 1, 0]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)
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


def P83P0 : CertificateIrreducibleZModOfList' 83 5 2 6 [78, 25, 68, 70, 27, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 51, 13, 17, 48], [60, 35, 25, 38, 82], [64, 23, 58, 7, 11], [80, 56, 70, 21, 25], [0, 1]]
 g := ![![[70, 54, 25, 42, 77], [72, 59, 2, 79, 29], [22, 72, 52, 11], [30, 60, 33, 65], [1], []], ![[0, 3, 81, 75, 11, 79, 26, 33], [45, 21, 66, 23, 45, 70, 18, 49], [3, 4, 34, 63], [65, 55, 6, 41], [20, 21, 39, 54, 28, 20, 24, 68], [37, 69, 14, 63]], ![[52, 21, 32, 32, 16, 78, 53, 80], [59, 31, 48, 19, 62, 22, 61, 73], [64, 71, 82, 41], [79, 37, 78, 49], [51, 75, 8, 76, 70, 36, 23, 18], [61, 38, 63, 1]], ![[56, 3, 19, 8, 33, 53, 38, 64], [27, 68, 19, 28, 55, 70, 11, 49], [41, 41, 28, 28], [17, 67, 46, 38], [54, 43, 0, 51, 71, 3, 58, 61], [46, 48, 41, 38]], ![[19, 80, 70, 17, 9, 15, 79, 3], [3, 27, 76, 10, 10, 17, 32, 64], [56, 9, 31, 30], [56, 33, 45, 59], [45, 24, 65, 66, 20, 56, 59, 41], [28, 22, 28, 44]]]
 h' := ![![[18, 51, 13, 17, 48], [28, 33, 45, 75, 49], [25, 75, 15, 62, 19], [9, 47, 56, 4, 54], [5, 58, 15, 13, 56], [0, 0, 1], [0, 1]], ![[60, 35, 25, 38, 82], [23, 75, 12, 74, 55], [9, 6, 57, 40, 56], [34, 7, 68, 76, 48], [37, 6, 66, 13, 46], [11, 11, 60, 16, 6], [18, 51, 13, 17, 48]], ![[64, 23, 58, 7, 11], [37, 19, 1, 52, 70], [81, 41, 79, 20, 50], [50, 61, 0, 3, 46], [53, 48, 52, 23, 7], [4, 43, 23, 44, 27], [60, 35, 25, 38, 82]], ![[80, 56, 70, 21, 25], [32, 79, 53, 58, 6], [77, 79, 66, 64, 26], [72, 61, 52, 33, 32], [30, 62, 59, 72, 72], [10, 42, 12, 63, 74], [64, 23, 58, 7, 11]], ![[0, 1], [81, 43, 55, 73, 69], [71, 48, 32, 63, 15], [17, 73, 73, 50, 69], [22, 75, 57, 45, 68], [66, 70, 70, 43, 59], [80, 56, 70, 21, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 46, 58, 22], [], [], []]
 b := ![[], [47, 21, 10, 77, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 5
  hpos := by decide
  P := [78, 25, 68, 70, 27, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![816742410, -1136716623, 4686457718, -2937539486, 4000882781]
  a := ![0, 3, 2, -4, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9840270, -13695381, 56463346, -35392042, 48203407]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6217, -302, -1466, -261, 979]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-6217, -302, -1466, -261, 979]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![83, 78, 1, 0, 0], ![64, 21, 0, 1, 0], ![43, 26, 0, 0, 1]] where
  M :=![![![-6217, -302, -1466, -261, 979], ![832, 38, 193, 35, -130], ![2872, 142, 677, 120, -452], ![3324, 165, 789, 140, -526], ![582, 27, 141, 25, -93]]]
  hmulB := by decide  
  f := ![![![-15, -20, -14, -9, -11]], ![![-80, -114, -113, -7, -94]], ![![-85, -120, -113, -15, -93]], ![![-36, -49, -46, -9, -36]], ![![-35, -49, -45, -8, -36]]]
  g := ![![![1012, 1057, -1466, -261, 979], ![-133, -139, 193, 35, -130], ![-467, -488, 677, 120, -452], ![-545, -569, 789, 140, -526], ![-98, -102, 141, 25, -93]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [87, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 88], [0, 1]]
 g := ![![[8, 44], [72], [25], [72, 10], [66, 78], [1]], ![[0, 45], [72], [25], [54, 79], [68, 11], [1]]]
 h' := ![![[16, 88], [53, 69], [49, 28], [55, 84], [43, 59], [2, 16], [0, 1]], ![[0, 1], [0, 20], [52, 61], [64, 5], [8, 30], [80, 73], [16, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [54, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [87, 73, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![419447, 459067, 769923, -105462, 626017]
  a := ![45, 91, 91, -56, 217]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-939925, -827603, 769923, -105462, 626017]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 7, 31, 3, -12]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![9, 7, 31, 3, -12]] 
 ![![89, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![47, 0, 0, 0, 1]] where
  M :=![![![9, 7, 31, 3, -12], ![-4, -78, -3, 13, 0], ![-36, 6, -79, -12, 32], ![12, 133, 5, -22, 0], ![48, 67, 89, 1, -35]]]
  hmulB := by decide  
  f := ![![![-59, 211, -499, 369, -436]], ![![-14, 52, -119, 89, -104]], ![![-5, 21, -50, 37, -44]], ![![-8, 41, -73, 60, -64]], ![![-33, 130, -300, 224, -263]]]
  g := ![![![2, 7, 31, 3, -12], ![17, -78, -3, 13, 0], ![-11, 6, -79, -12, 32], ![-29, 133, 5, -22, 0], ![-4, 67, 89, 1, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-139, -201, -261, -2, 103]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-139, -201, -261, -2, 103]] 
 ![![89, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![-139, -201, -261, -2, 103], ![-200, 533, -448, -154, 190], ![404, 332, 781, 52, -312], ![348, -896, 776, 263, -330], ![-246, -854, -418, 88, 157]]]
  hmulB := by decide  
  f := ![![![-15585, -939, -3815, -692, 2325]], ![![-5588, -347, -1376, -250, 826]], ![![-8332, -512, -2047, -372, 1236]], ![![-9937, -663, -2483, -453, 1435]], ![![-10876, -702, -2698, -492, 1589]]]
  g := ![![![141, -201, -261, -2, 103], ![14, 533, -448, -154, 190], ![-352, 332, 781, 52, -312], ![-31, -896, 776, 263, -330], ![364, -854, -418, 88, 157]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2

def I89N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -9, 39, 7, -16]] i)))

def SI89N3: IdealEqSpanCertificate' Table ![![19, -9, 39, 7, -16]] 
 ![![89, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![71, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![19, -9, 39, 7, -16], ![-36, -104, -63, 9, 24], ![-36, 54, -77, -20, 32], ![60, 177, 105, -16, -40], ![72, 39, 141, 13, -57]]]
  hmulB := by decide  
  f := ![![![-1825, -93, -447, -71, 272]], ![![-1556, -80, -381, -61, 232]], ![![-114, -6, -29, -4, 16]], ![![-1447, -78, -354, -59, 216]], ![![-492, -27, -123, -19, 71]]]
  g := ![![![4, -9, 39, 7, -16], ![79, -104, -63, 9, 24], ![-34, 54, -77, -20, 32], ![-134, 177, 105, -16, -40], ![-37, 39, 141, 13, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N3 : Nat.card (O ⧸ I89N3) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N3)

lemma isPrimeI89N3 : Ideal.IsPrime I89N3 := prime_ideal_of_norm_prime hp89.out _ NI89N3
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-6217, -302, -1466, -261, 979]] ![![9, 7, 31, 3, -12]]
  ![![41891, 2121, 9819, 1736, -6573]] where
 M := ![![![41891, 2121, 9819, 1736, -6573]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![41891, 2121, 9819, 1736, -6573]] ![![-139, -201, -261, -2, 103]]
  ![![-59087, 28196, -120470, -21684, 49394]] where
 M := ![![![-59087, 28196, -120470, -21684, 49394]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N2 : IdealMulLeCertificate' Table 
  ![![-59087, 28196, -120470, -21684, 49394]] ![![19, -9, 39, 7, -16]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![4454539, -10817683, 9883183, 3238621, -4181042]]]
 hmul := by decide  
 g := ![![![![50051, -121547, 111047, 36389, -46978]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -33, -27, -3, -6]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-19, -33, -27, -3, -6]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![29, 72, 28, 1, 0], ![21, 18, 39, 0, 1]] where
  M :=![![![-19, -33, -27, -3, -6], ![-84, -70, -123, -27, -36], ![-36, -48, -31, -18, -60], ![-372, -585, -447, -100, -360], ![-300, -459, -375, -81, -235]]]
  hmulB := by decide  
  f := ![![![1793, 87, 423, 75, -282]], ![![-240, -10, -57, -9, 36]], ![![-828, -42, -193, -36, 132]], ![![109, 6, 26, 5, -18]], ![![9, 0, 3, 0, -1]]]
  g := ![![![2, 3, 3, -3, -6], ![15, 26, 21, -27, -36], ![18, 24, 29, -18, -60], ![104, 135, 169, -100, -360], ![72, 99, 114, -81, -235]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [2, 66, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 44, 88], [6, 52, 9], [0, 1]]
 g := ![![[88, 50, 2], [43, 49], [19, 49], [61, 85], [83, 91], [1]], ![[24, 34, 30, 79], [45, 11], [94, 12], [53, 85], [52, 1], [14, 74, 83, 47]], ![[66, 11], [8, 27], [63, 50], [34, 49], [92, 44], [28, 1, 62, 50]]]
 h' := ![![[18, 44, 88], [61, 90, 83], [27, 74, 90], [29, 48, 90], [32, 36, 52], [95, 31, 24], [0, 1]], ![[6, 52, 9], [10, 27, 14], [87, 77, 37], [9, 0, 77], [55, 21, 52], [81, 83, 96], [18, 44, 88]], ![[0, 1], [33, 77], [90, 43, 67], [33, 49, 27], [2, 40, 90], [63, 80, 74], [6, 52, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 5], []]
 b := ![[], [57, 18, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [2, 66, 73, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![151477992, 170100268, 255746740, -12453650, 184008210]
  a := ![18, 39, 36, -24, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-34551944, -23148296, -67751250, -12453650, 184008210]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1793, -87, -423, -75, 282]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-1793, -87, -423, -75, 282]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![79, 66, 1, 0, 0], ![16, 52, 0, 1, 0], ![82, 31, 0, 0, 1]] where
  M :=![![![-1793, -87, -423, -75, 282], ![240, 10, 57, 9, -36], ![828, 42, 193, 36, -132], ![960, 45, 237, 34, -144], ![168, 9, 39, 9, -29]]]
  hmulB := by decide  
  f := ![![![19, 33, 27, 3, 6]], ![![84, 70, 123, 27, 36]], ![![73, 75, 106, 21, 30]], ![![52, 49, 75, 16, 24]], ![![46, 55, 66, 12, 19]]]
  g := ![![![100, 237, -423, -75, 282], ![-15, -32, 57, 9, -36], ![-43, -108, 193, 36, -132], ![-67, -133, 237, 34, -144], ![-7, -22, 39, 9, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [86, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 96], [0, 1]]
 g := ![![[67, 44], [2], [88], [64], [12], [58, 1]], ![[0, 53], [2], [88], [64], [12], [19, 96]]]
 h' := ![![[58, 96], [24, 23], [83, 83], [52, 31], [67, 8], [56, 77], [0, 1]], ![[0, 1], [0, 74], [47, 14], [7, 66], [46, 89], [60, 20], [58, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [94, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [86, 39, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![85966, 100273, 143107, -8269, 114860]
  a := ![21, 37, 37, -19, 92]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-211399, -128613, 143107, -8269, 114860]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-19, -33, -27, -3, -6]] ![![-1793, -87, -423, -75, 282]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![303, 462, 310, 152, 178]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![303, 462, 310, 152, 178]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![80, 99, 38, 1, 0], ![69, 27, 51, 0, 1]] where
  M :=![![![303, 462, 310, 152, 178], ![1584, 1979, 2324, 184, 1572], ![1320, 2080, 1239, 760, 672], ![9928, 12532, 14356, 1335, 9668], ![7036, 10000, 8368, 2516, 5199]]]
  hmulB := by decide  
  f := ![![![4515, 194, 1050, 192, -706]], ![![-640, -1, -212, -40, 124]], ![![-2056, -48, -429, -88, 304]], ![![2152, 133, 458, 79, -320]], ![![1871, 107, 443, 76, -295]]]
  g := ![![![-239, -192, -144, 152, 178], ![-1204, -581, -840, 184, 1572], ![-1048, -904, -613, 760, 672], ![-7564, -3769, -5242, 1335, 9668], ![-5475, -3757, -3489, 2516, 5199]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [74, 61, 95, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 33, 90], [15, 67, 11], [0, 1]]
 g := ![![[67, 29, 54], [33, 9], [60, 6, 25], [3, 13], [90, 36], [1]], ![[62, 63, 94, 10], [48, 68], [90, 91, 64, 51], [13, 65], [32, 30], [100, 93, 54, 83]], ![[80, 82, 76, 28], [59, 100], [0, 24, 99, 59], [67, 19], [36, 14], [7, 98, 88, 18]]]
 h' := ![![[92, 33, 90], [99, 76, 16], [4, 54, 98], [57, 26, 5], [28, 66, 66], [27, 40, 6], [0, 1]], ![[15, 67, 11], [4, 28, 34], [83, 25, 13], [26, 83, 49], [33, 28, 60], [52, 87, 63], [92, 33, 90]], ![[0, 1], [82, 98, 51], [2, 22, 91], [16, 93, 47], [96, 7, 76], [29, 75, 32], [15, 67, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 89], []]
 b := ![[], [78, 13, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [74, 61, 95, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8494981451, -9253231315, -14756406604, 1036839460, -10618387820]
  a := ![-75, -156, -157, 98, -371]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6348778429, 1730654785, 4825559136, 1036839460, -10618387820]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4515, -194, -1050, -192, 706]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-4515, -194, -1050, -192, 706]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![66, 16, 1, 0, 0], ![15, 83, 0, 1, 0], ![5, 81, 0, 0, 1]] where
  M :=![![![-4515, -194, -1050, -192, 706], ![640, 1, 212, 40, -124], ![2056, 48, 429, 88, -304], ![2360, 164, 452, 77, -332], ![428, 104, 104, 4, -67]]]
  hmulB := by decide  
  f := ![![![-303, -462, -310, -152, -178]], ![![-1584, -1979, -2324, -184, -1572]], ![![-462, -636, -583, -136, -372]], ![![-1445, -1819, -2098, -187, -1414]], ![![-1355, -1709, -1962, -180, -1321]]]
  g := ![![![635, -244, -1050, -192, 706], ![-132, 33, 212, 40, -124], ![-258, 104, 429, 88, -304], ![-267, 133, 452, 77, -332], ![-61, 35, 104, 4, -67]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [80, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 100], [0, 1]]
 g := ![![[70, 24], [78], [20, 14], [77], [70], [56, 1]], ![[0, 77], [78], [97, 87], [77], [70], [11, 100]]]
 h' := ![![[56, 100], [76, 78], [16, 49], [7, 32], [39, 28], [65, 26], [0, 1]], ![[0, 1], [0, 23], [33, 52], [82, 69], [92, 73], [6, 75], [56, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [29, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [80, 45, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![186138, 204130, 334724, -38483, 263685]
  a := ![-29, -59, -58, 36, -145]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-224226, -230850, 334724, -38483, 263685]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![303, 462, 310, 152, 178]] ![![-4515, -194, -1050, -192, 706]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3249, 159, 755, 141, -516]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![3249, 159, 755, 141, -516]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![47, 47, 69, 65, 1]] where
  M :=![![![3249, 159, 755, 141, -516], ![-432, -20, -71, -43, 96], ![-1500, -58, -381, -32, 196], ![-1720, -175, -235, -196, 428], ![-316, -7, -133, 21, 13]]]
  hmulB := by decide  
  f := ![![![3, 5, 3, 1, 4]], ![![20, 32, 25, 5, 16]], ![![20, 24, 27, 6, 12]], ![![124, 163, 157, 38, 100]], ![![103, 137, 131, 31, 81]]]
  g := ![![![267, 237, 353, 327, -516], ![-48, -44, -65, -61, 96], ![-104, -90, -135, -124, 196], ![-212, -197, -289, -272, 428], ![-9, -6, -10, -8, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 4 2 6 [77, 55, 87, 79, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 47, 38, 40], [64, 31, 75, 50], [34, 24, 93, 13], [0, 1]]
 g := ![![[13, 88, 34, 19], [60, 1, 32, 30], [9, 85, 36, 19], [73, 84, 93], [77, 24, 1], []], ![[81, 56, 79, 64, 102, 27], [49, 68, 25, 9, 42, 20], [5, 36, 77, 64, 43, 43], [49, 40, 32], [30, 7, 41], [10, 56, 100, 26, 51, 37]], ![[39, 51, 44, 41, 1, 97], [79, 64, 34, 42, 51, 33], [94, 49, 82, 20, 32, 23], [48, 60, 8], [74, 97, 30], [43, 73, 63, 61, 39, 61]], ![[21, 97, 35, 38, 17, 2], [76, 30, 55, 94, 23, 23], [8, 88, 79, 69, 99, 32], [13, 67, 33], [36, 18, 28], [83, 53, 34, 6, 72, 34]]]
 h' := ![![[29, 47, 38, 40], [15, 85, 34, 15], [28, 45, 77, 37], [9, 101, 14, 88], [45, 97, 41, 14], [0, 0, 0, 1], [0, 1]], ![[64, 31, 75, 50], [79, 63, 0, 82], [73, 93, 60, 84], [66, 23, 68, 87], [53, 10, 81, 54], [32, 7, 58, 12], [29, 47, 38, 40]], ![[34, 24, 93, 13], [101, 33, 43, 2], [77, 10, 68, 94], [21, 2, 89, 15], [3, 43, 94, 76], [97, 82, 57, 37], [64, 31, 75, 50]], ![[0, 1], [14, 25, 26, 4], [85, 58, 1, 94], [67, 80, 35, 16], [55, 56, 93, 62], [56, 14, 91, 53], [34, 24, 93, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [25, 51, 11], []]
 b := ![[], [], [15, 26, 53, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 4
  hpos := by decide
  P := [77, 55, 87, 79, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4180200931631, 5279538753851, 6043247921677, 561854544353, 4074679837320]
  a := ![39, 71, 70, -37, 177]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1818735450703, -1808062267963, -2670967581101, -2565944998849, 4074679837320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 112550881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 5, 3, 1, 4]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![3, 5, 3, 1, 4]] 
 ![![103, 0, 0, 0, 0], ![96, 1, 0, 0, 0], ![93, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![3, 5, 3, 1, 4], ![20, 32, 25, 5, 16], ![20, 24, 27, 6, 12], ![124, 163, 157, 38, 100], ![88, 121, 109, 27, 75]]]
  hmulB := by decide  
  f := ![![![3249, 159, 755, 141, -516]], ![![3024, 148, 703, 131, -480]], ![![2919, 143, 678, 127, -464]], ![![488, 23, 115, 20, -76]], ![![407, 20, 94, 18, -65]]]
  g := ![![![-8, 5, 3, 1, 4], ![-55, 32, 25, 5, 16], ![-49, 24, 27, 6, 12], ![-311, 163, 157, 38, 100], ![-224, 121, 109, 27, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![3249, 159, 755, 141, -516]] ![![3, 5, 3, 1, 4]]
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


lemma PB853I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB853I2 : PrimesBelowBoundCertificateInterval O 61 103 853 where
  m := 9
  g := ![2, 2, 2, 3, 1, 4, 2, 2, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB853I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2, I89N3]
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
    · exact ![20151121, 67]
    · exact ![357911, 5041]
    · exact ![389017, 5329]
    · exact ![6241, 6241, 79]
    · exact ![3939040643]
    · exact ![7921, 89, 89, 89]
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
      exact NI79N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I67N1, I79N2, I89N1, I89N2, I89N3, I103N1]
  Il := ![[I67N1], [], [], [I79N2], [], [I89N1, I89N2, I89N3], [], [], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
