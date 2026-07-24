
import IdealArithmetic.Examples.NF5_3_67500000_1.RI5_3_67500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-126, -285, -69, -5, 40]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-126, -285, -69, -5, 40]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![16, 60, 12, 1, 0], ![29, 59, 45, 0, 1]] where
  M :=![![![-126, -285, -69, -5, 40], ![-135, -330, -155, -193, -150], ![-129, -419, -394, -739, -708], ![21, -143, -455, -1052, -1080], ![91, 181, -5, -119, -153]]]
  hmulB := by decide  
  f := ![![![18, -15, -3, 5, -2]], ![![21, 36, -31, 11, 36]], ![![-75, -85, 122, -65, -42]], ![![9, 13, -7, 0, 22]], ![![-23, -31, 53, -32, 5]]]
  g := ![![![-18, -35, -27, -5, 40], ![109, 300, 133, -193, -150], ![481, 1279, 602, -739, -708], ![719, 1891, 907, -1052, -1080], ![96, 244, 124, -119, -153]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [15, 21, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 37, 35], [43, 29, 32], [0, 1]]
 g := ![![[33, 2, 14], [56, 57, 65], [41, 37], [], [17, 1], []], ![[43, 31, 17, 17], [41, 40, 23, 6], [50, 1], [57, 15], [26, 37], [32, 19]], ![[32, 66, 61, 12], [53, 51, 10, 50], [43, 29], [10, 15], [24, 29], [35, 19]]]
 h' := ![![[41, 37, 35], [31, 28, 58], [7, 53, 47], [35, 43, 29], [13, 30], [0, 0, 1], [0, 1]], ![[43, 29, 32], [18, 31, 49], [2, 18, 2], [45, 50, 1], [37, 38, 45], [62, 0, 29], [41, 37, 35]], ![[0, 1], [39, 8, 27], [60, 63, 18], [13, 41, 37], [30, 66, 22], [51, 0, 37], [43, 29, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 32], []]
 b := ![[], [21, 27, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [15, 21, 50, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24443, 16933, -28535, -20542, 8362]
  a := ![-5, -7, 2, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1651, 11285, -2363, -20542, 8362]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![405, 195, -307, 134, 388]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![405, 195, -307, 134, 388]] 
 ![![67, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![405, 195, -307, 134, 388], ![-762, -664, 1091, -600, -360], ![-720, -391, -544, 742, -2520], ![5274, 4593, -5263, 2129, 6186], ![-4727, -4219, 5207, -2305, -4911]]]
  hmulB := by decide  
  f := ![![![-46803, 165049, 639109, 1499496, 1545052]], ![![-11121, 38825, 150890, 354106, 364888]], ![![-28182, 97845, 381034, 894320, 921584]], ![![-21210, 72589, 284175, 667209, 687614]], ![![-44366, 156198, 605196, 1419983, 1463139]]]
  g := ![![![-290, 195, -307, 134, 388], ![114, -664, 1091, -600, -360], ![2473, -391, -544, 742, -2520], ![-4751, 4593, -5263, 2129, 6186], ![3567, -4219, 5207, -2305, -4911]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28, -116, -424, -991, -1020]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![28, -116, -424, -991, -1020]] 
 ![![67, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![28, -116, -424, -991, -1020], ![87, -309, -1194, -2801, -2886], ![255, -852, -3365, -7905, -8148], ![321, -1036, -4146, -9748, -10050], ![18, -40, -188, -446, -461]]]
  hmulB := by decide  
  f := ![![![370, -76, -122, 73, 222]], ![![159, -37, -48, 29, 96]], ![![209, -44, -75, 47, 114]], ![![129, 4, -60, 30, 96]], ![![94, -48, -12, 12, 43]]]
  g := ![![![894, -116, -424, -991, -1020], ![2517, -309, -1194, -2801, -2886], ![7093, -852, -3365, -7905, -8148], ![8739, -1036, -4146, -9748, -10050], ![396, -40, -188, -446, -461]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-126, -285, -69, -5, 40]] ![![405, 195, -307, 134, 388]]
  ![![370, -76, -122, 73, 222]] where
 M := ![![![370, -76, -122, 73, 222]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![370, -76, -122, 73, 222]] ![![28, -116, -424, -991, -1020]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![473, -257, -29, 42, 120]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![473, -257, -29, 42, 120]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![14, 2, 11, 11, 1]] where
  M :=![![![473, -257, -29, 42, 120], ![-234, 210, 19, -52, -108], ![168, -47, -10, -10, 12], ![84, -59, -5, -5, 6], ![-111, 45, -1, -1, -13]]]
  hmulB := by decide  
  f := ![![![1, 1, -1, 0, 0]], ![![0, 0, 1, -2, 0]], ![![-6, -5, 4, -4, -12]], ![![12, 11, -17, 5, 6]], ![![1, 1, -2, 0, -1]]]
  g := ![![![-17, -7, -19, -18, 120], ![18, 6, 17, 16, -108], ![0, -1, -2, -2, 12], ![0, -1, -1, -1, 6], ![1, 1, 2, 2, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [60, 11, 43, 29, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 15, 63, 44], [42, 48, 1, 49], [50, 7, 7, 49], [0, 1]]
 g := ![![[60, 25, 70, 37], [47, 2, 64, 25], [57, 5, 16, 38], [51, 44, 60], [1], []], ![[39, 7, 23, 60, 38, 21], [4, 7, 1, 8, 30, 47], [60, 62, 43, 6, 45, 70], [14, 66, 49], [10, 50, 19], [42, 23, 19]], ![[57, 31, 44, 33, 63, 32], [5, 64, 42, 6, 13, 1], [37, 6, 12, 11, 50, 27], [25, 16, 43], [31, 31, 1], [9, 49, 58]], ![[49, 44, 23, 32, 13, 27], [15, 45, 34, 64, 55, 58], [62, 61, 48, 28, 41, 9], [17, 49, 24], [54, 25, 3], [3, 69, 58]]]
 h' := ![![[21, 15, 63, 44], [20, 4, 34, 45], [59, 70, 56, 66], [43, 36, 69, 40], [11, 60, 28, 42], [0, 0, 1], [0, 1]], ![[42, 48, 1, 49], [15, 15, 64, 21], [12, 54, 2, 8], [39, 30, 16, 60], [13, 1, 20, 7], [51, 66, 27, 44], [21, 15, 63, 44]], ![[50, 7, 7, 49], [50, 58, 60, 17], [23, 57, 6, 61], [1, 16, 19, 12], [62, 37, 16, 55], [17, 70, 41, 70], [42, 48, 1, 49]], ![[0, 1], [12, 65, 55, 59], [22, 32, 7, 7], [1, 60, 38, 30], [58, 44, 7, 38], [48, 6, 2, 28], [50, 7, 7, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [64, 44, 19], []]
 b := ![[], [], [32, 57, 2, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [60, 11, 43, 29, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20990786745, 29404319330, -48015669718, 59628776229, 3074280144]
  a := ![6, -59, -1, -60, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-310551201, 327545902, -1152573962, 363544995, 3074280144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, -1, 0, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![1, 1, -1, 0, 0]] 
 ![![71, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![1, 1, -1, 0, 0], ![0, 0, 1, -2, 0], ![-6, -5, 4, -4, -12], ![12, 11, -17, 5, 6], ![-9, -9, 13, -7, -5]]]
  hmulB := by decide  
  f := ![![![473, -257, -29, 42, 120]], ![![50, -26, -3, 4, 12]], ![![49, -26, -3, 4, 12]], ![![261, -142, -16, 23, 66]], ![![145, -79, -9, 13, 37]]]
  g := ![![![0, 1, -1, 0, 0], ![1, 0, 1, -2, 0], ![6, -5, 4, -4, -12], ![-4, 11, -17, 5, 6], ![5, -9, 13, -7, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![473, -257, -29, 42, 120]] ![![1, 1, -1, 0, 0]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -9, -19, -40, -42]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-1, -9, -19, -40, -42]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![62, 0, 51, 1, 0], ![47, 68, 44, 0, 1]] where
  M :=![![![-1, -9, -19, -40, -42], ![6, -14, -55, -116, -114], ![-6, -55, -124, -344, -354], ![12, -43, -187, -405, -444], ![9, 5, -5, -25, -1]]]
  hmulB := by decide  
  f := ![![![-559, 359, 39, -70, -174]], ![![312, -208, -23, 42, 102]], ![![-180, 109, 14, -22, -54]], ![![-602, 382, 43, -75, -186]], ![![-176, 102, 12, -19, -49]]]
  g := ![![![61, 39, 53, -40, -42], ![172, 106, 149, -116, -114], ![520, 329, 452, -344, -354], ![630, 413, 548, -405, -444], ![22, 1, 18, -25, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [39, 13, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 53, 1], [21, 19, 72], [0, 1]]
 g := ![![[22, 67, 64], [61, 24], [57, 23], [33, 64, 41], [39, 1], []], ![[39, 13, 57, 18], [59, 50], [55, 57], [62, 44, 29, 1], [39, 69], [72, 1]], ![[55, 56, 55, 61], [26, 38], [34, 41], [20, 38, 34, 8], [68, 35], [1, 1]]]
 h' := ![![[18, 53, 1], [18, 17, 8], [39, 28, 30], [27, 66, 60], [12, 38, 48], [0, 0, 1], [0, 1]], ![[21, 19, 72], [16, 43, 23], [45, 55, 14], [0, 56, 38], [16, 5, 1], [71, 57, 19], [18, 53, 1]], ![[0, 1], [14, 13, 42], [58, 63, 29], [56, 24, 48], [31, 30, 24], [37, 16, 53], [21, 19, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 34], []]
 b := ![[], [29, 32, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [39, 13, 34, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9880, -10141, 5631, -15009, -23916]
  a := ![-1, -5, 1, -6, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![28010, 22139, 24978, -15009, -23916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![559, -359, -39, 70, 174]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![559, -359, -39, 70, 174]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![39, 44, 1, 0, 0], ![18, 1, 0, 1, 0], ![71, 59, 0, 0, 1]] where
  M :=![![![559, -359, -39, 70, 174], ![-312, 208, 23, -42, -102], ![180, -109, -14, 22, 54], ![108, -69, -7, 13, 36], ![-129, 79, 9, -15, -41]]]
  hmulB := by decide  
  f := ![![![1, 9, 19, 40, 42]], ![![-6, 14, 55, 116, 114]], ![![-3, 14, 45, 96, 96]], ![![0, 3, 8, 17, 18]], ![![-4, 20, 63, 133, 133]]]
  g := ![![![-158, -123, -39, 70, 174], ![93, 72, 23, -42, -102], ![-48, -37, -14, 22, 54], ![-33, -26, -7, 13, 36], ![37, 29, 9, -15, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [67, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 72], [0, 1]]
 g := ![![[63, 12], [49], [36], [37, 70], [23], [1]], ![[0, 61], [49], [36], [71, 3], [23], [1]]]
 h' := ![![[13, 72], [38, 42], [6, 66], [3, 6], [28, 17], [6, 13], [0, 1]], ![[0, 1], [0, 31], [61, 7], [8, 67], [30, 56], [29, 60], [13, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [36, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [67, 60, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3860, 5744, -1539, 10372, 10563]
  a := ![8, 26, -3, 25, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11956, -7673, -1539, 10372, 10563]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-1, -9, -19, -40, -42]] ![![559, -359, -39, 70, 174]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0, 0, 0]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]] where
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [47, 76, 41, 67, 66, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 70, 65, 63, 17], [10, 54, 11, 3, 49], [39, 31, 49, 68, 33], [39, 2, 33, 24, 59], [0, 1]]
 g := ![![[10, 17, 56, 54, 1], [22, 71, 18, 26, 26], [36, 3, 69, 36, 23], [72, 19, 23, 13, 1], [], []], ![[73, 57, 10, 57, 19, 71, 15, 66], [22, 44, 77, 0, 55, 51, 1, 60], [8, 46, 66, 51, 63, 66, 46, 29], [35, 24, 21, 21, 6, 27, 73, 57], [28, 12, 33, 10], [57, 66, 53, 52]], ![[64, 65, 61, 60, 4, 34, 15, 31], [71, 6, 34, 77, 45, 71, 42, 38], [66, 32, 60, 46, 10, 14, 21, 49], [48, 60, 35, 35, 27, 49], [48, 41, 63, 11], [59, 13, 65, 31]], ![[34, 31, 43, 42, 74, 75, 31, 17], [17, 33, 18, 6, 6, 57, 19, 29], [70, 67, 51, 22, 12, 75, 40, 60], [22, 69, 39, 45, 26, 55, 70, 77], [10, 49, 29, 23], [70, 4, 1, 62]], ![[11, 22, 66, 14, 4, 4, 75, 7], [20, 52, 32, 57, 77, 37, 50, 24], [36, 28, 67, 73, 58, 22, 16, 69], [31, 24, 30, 65, 11, 3, 9, 74], [39, 17, 63, 67], [25, 5, 53, 5]]]
 h' := ![![[4, 70, 65, 63, 17], [72, 30, 75, 19, 78], [46, 57, 45, 15, 37], [13, 34, 53, 17, 55], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[10, 54, 11, 3, 49], [66, 44, 24, 25, 23], [65, 21, 52, 2, 34], [50, 18, 32, 47, 66], [3, 27, 24, 52, 61], [23, 78, 0, 4, 57], [4, 70, 65, 63, 17]], ![[39, 31, 49, 68, 33], [53, 54, 57, 53, 7], [55, 68, 64, 33, 77], [23, 35, 49, 70, 78], [46, 3, 1, 1], [13, 14, 71, 3, 13], [10, 54, 11, 3, 49]], ![[39, 2, 33, 24, 59], [26, 58, 73, 0, 21], [76, 5, 54, 1, 43], [46, 19, 46, 61, 3], [17, 23, 45, 61, 56], [48, 70, 61, 24, 24], [39, 31, 49, 68, 33]], ![[0, 1], [25, 51, 8, 61, 29], [60, 7, 22, 28, 46], [50, 52, 57, 42, 35], [15, 26, 9, 44, 40], [30, 75, 25, 48, 64], [39, 2, 33, 24, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 70, 11, 9], [], [], []]
 b := ![[], [24, 18, 57, 41, 32], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [47, 76, 41, 67, 66, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12056401641, 8234021796, -1661501377, -3491465198, 27398182681]
  a := ![-10, -8, 5, -6, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![152612679, 104228124, -21031663, -44195762, 346812439]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -1, 1, -1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![2, -1, 1, -1, 0]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![59, 67, 1, 0, 0], ![57, 68, 0, 1, 0], ![70, 69, 0, 0, 1]] where
  M :=![![![2, -1, 1, -1, 0], ![-3, 0, 1, -1, -6], ![15, 13, -16, 5, 12], ![-9, -11, 19, -14, 0], ![3, 5, -13, 9, -7]]]
  hmulB := by decide  
  f := ![![![34, 5, -1, -7, -6]], ![![-3, 30, 1, -17, -24]], ![![22, 28, 0, -19, -24]], ![![21, 28, 0, -19, -24]], ![![26, 29, 0, -20, -25]]]
  g := ![![![0, 0, 1, -1, 0], ![5, 5, 1, -1, -6], ![-2, -1, -16, 5, 12], ![-4, -4, 19, -14, 0], ![9, 9, -13, 9, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [68, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 82], [0, 1]]
 g := ![![[55, 11], [18, 70], [11], [40], [57, 25], [1]], ![[0, 72], [0, 13], [11], [40], [15, 58], [1]]]
 h' := ![![[78, 82], [21, 54], [67, 30], [63, 29], [25, 66], [15, 78], [0, 1]], ![[0, 1], [0, 29], [0, 53], [1, 54], [27, 17], [40, 5], [78, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [39, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [68, 5, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3766, -2348, 962, 2930, -7308]
  a := ![6, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3422, 2870, 962, 2930, -7308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-87, 1092, 3128, 7172, 7342]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-87, 1092, 3128, 7172, 7342]] 
 ![![83, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-87, 1092, 3128, 7172, 7342], ![-510, 2531, 8774, 20430, 21006], ![-1728, 6536, 24689, 57832, 59562], ![-2340, 7620, 30392, 71441, 73650], ![-212, 128, 1364, 3332, 3471]]]
  hmulB := by decide  
  f := ![![![-17445, 11180, 1448, -2364, -5446]], ![![-10818, 6923, 902, -1466, -3386]], ![![-7389, 4788, 577, -988, -2284]], ![![-12672, 8084, 1096, -1743, -3942]], ![![-6461, 4156, 508, -856, -2039]]]
  g := ![![![-9931, 1092, 3128, 7172, 7342], ![-27906, 2531, 8774, 20430, 21006], ![-78579, 6536, 24689, 57832, 59562], ![-96770, 7620, 30392, 71441, 73650], ![-4363, 128, 1364, 3332, 3471]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -1, 7, -4, -6]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-11, -1, 7, -4, -6]] 
 ![![83, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![-11, -1, 7, -4, -6], ![6, 2, -11, 8, -6], ![42, 37, -32, 8, 66], ![-90, -83, 115, -57, -72], ![69, 65, -97, 51, 43]]]
  hmulB := by decide  
  f := ![![![-547, -1139, -165, 258, 450]], ![![-376, -784, -115, 174, 306]], ![![-126, -265, -44, 46, 90]], ![![-323, -676, -106, 133, 246]], ![![-325, -677, -99, 151, 265]]]
  g := ![![![5, -1, 7, -4, -6], ![0, 2, -11, 8, -6], ![-62, 37, -32, 8, 66], ![107, -83, 115, -57, -72], ![-78, 65, -97, 51, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2

def I83N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![846, -552, -60, 109, 268]] i)))

def SI83N3: IdealEqSpanCertificate' Table ![![846, -552, -60, 109, 268]] 
 ![![83, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![55, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![846, -552, -60, 109, 268], ![-477, 309, 34, -61, -150], ![267, -176, -19, 35, 84], ![165, -104, -14, 22, 54], ![-194, 124, 16, -26, -63]]]
  hmulB := by decide  
  f := ![![![-36, 48, 294, 697, 722]], ![![-33, 45, 272, 645, 668]], ![![-3, 8, 35, 83, 86]], ![![-27, 40, 230, 543, 562]], ![![-14, 20, 118, 281, 291]]]
  g := ![![![325, -552, -60, 109, 268], ![-182, 309, 34, -61, -150], ![104, -176, -19, 35, 84], ![59, -104, -14, 22, 54], ![-71, 124, 16, -26, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N3 : Nat.card (O ⧸ I83N3) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N3)

lemma isPrimeI83N3 : Ideal.IsPrime I83N3 := prime_ideal_of_norm_prime hp83.out _ NI83N3
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![2, -1, 1, -1, 0]] ![![-87, 1092, 3128, 7172, 7342]]
  ![![948, -1431, -8221, -19695, -20410]] where
 M := ![![![948, -1431, -8221, -19695, -20410]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![948, -1431, -8221, -19695, -20410]] ![![-11, -1, 7, -4, -6]]
  ![![-36, 48, 294, 697, 722]] where
 M := ![![![-36, 48, 294, 697, 722]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N2 : IdealMulLeCertificate' Table 
  ![![-36, 48, 294, 697, 722]] ![![846, -552, -60, 109, 268]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29805, -52896, 16628, 72620, 84464]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-29805, -52896, 16628, 72620, 84464]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![33, 79, 84, 58, 1]] where
  M :=![![![-29805, -52896, 16628, 72620, 84464], ![-35532, -48709, 55256, 166652, 182328], ![-47028, -27304, 164971, 428140, 452928], ![-19416, 46144, 209972, 497391, 513864], ![18464, 42152, 12888, 7424, 1107]]]
  hmulB := by decide  
  f := ![![![147, 64, -4, -44, 304]], ![![-1044, -901, 1064, -444, -1176]], ![![2196, 2216, -3541, 1972, 864]], ![![2184, 1440, -100, -793, 5208]], ![![2591, 2229, -2448, 934, 3219]]]
  g := ![![![-31653, -75568, -79532, -54228, 84464], ![-68004, -162389, -171464, -116948, 182328], ![-168468, -402344, -425629, -290356, 452928], ![-190752, -455608, -482636, -329289, 513864], ![-203, -509, -900, -638, 1107]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [46, 33, 42, 44, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 41, 6, 21], [79, 24, 72, 28], [83, 23, 11, 40], [0, 1]]
 g := ![![[78, 35, 59, 25], [14, 45, 21], [23, 76, 40], [79, 4, 60, 2], [45, 1], []], ![[11, 29, 39, 86, 17, 73], [18, 73, 64], [45, 65, 49], [28, 87, 24, 65, 54, 79], [74, 33, 9, 40, 16, 22], [4, 72, 85]], ![[42, 15, 0, 80, 35, 33], [38, 30, 1], [87, 47, 21], [7, 79, 60, 41, 44, 59], [50, 76, 85, 33, 11, 75], [20, 63, 72]], ![[4, 17, 80, 53, 16, 47], [7, 8, 42], [78, 58, 32], [27, 35, 24, 45], [56, 4, 49, 79, 54, 16], [37, 78, 87]]]
 h' := ![![[61, 41, 6, 21], [24, 47, 71, 84], [57, 64, 46, 56], [15, 52, 47, 29], [66, 71, 35, 25], [0, 0, 1], [0, 1]], ![[79, 24, 72, 28], [66, 84, 30, 23], [2, 30, 86, 8], [84, 39, 13, 82], [29, 39, 17, 50], [66, 45, 53, 75], [61, 41, 6, 21]], ![[83, 23, 11, 40], [33, 5, 4, 49], [88, 60, 37, 1], [68, 8, 19, 56], [53, 56, 78, 14], [70, 56, 25, 20], [79, 24, 72, 28]], ![[0, 1], [55, 42, 73, 22], [56, 24, 9, 24], [66, 79, 10, 11], [82, 12, 48], [25, 77, 10, 83], [83, 23, 11, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [84, 44, 57], []]
 b := ![[], [], [57, 50, 4, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [46, 33, 42, 44, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13066645, -7721844, 19250420, 19364575, 4796800]
  a := ![6, 6, 4, 7, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1925405, -4344596, -4311020, -2908425, 4796800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![147, 64, -4, -44, 304]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![147, 64, -4, -44, 304]] 
 ![![89, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![76, 0, 0, 0, 1]] where
  M :=![![![147, 64, -4, -44, 304], ![-1044, -901, 1064, -444, -1176], ![2196, 2216, -3541, 1972, 864], ![2184, 1440, -100, -793, 5208], ![-2912, -2216, 1448, 0, -5277]]]
  hmulB := by decide  
  f := ![![![-29805, -52896, 16628, 72620, 84464]], ![![-4083, -7085, 2676, 10848, 12488]], ![![-19617, -34184, 12503, 51320, 59184]], ![![-12609, -21472, 9272, 35779, 40888]], ![![-25244, -44696, 14344, 62096, 72139]]]
  g := ![![![-245, 64, -4, -44, 304], ![607, -901, 1064, -444, -1176], ![461, 2216, -3541, 1972, 864], ![-4207, 1440, -100, -793, 5208], ![3820, -2216, 1448, 0, -5277]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-29805, -52896, 16628, 72620, 84464]] ![![147, 64, -4, -44, 304]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-477, 1461, 5965, 14042, 14482]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-477, 1461, 5965, 14042, 14482]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![76, 78, 95, 1, 0], ![94, 42, 77, 0, 1]] where
  M :=![![![-477, 1461, 5965, 14042, 14482], ![-1320, 4168, 16823, 39574, 40806], ![-3696, 11807, 47438, 111562, 115026], ![-4536, 14591, 58469, 137481, 141744], ![-197, 683, 2661, 6245, 6435]]]
  hmulB := by decide  
  f := ![![![-171, 101, 23, -28, -50]], ![![66, -82, 7, 12, -18]], ![![90, 163, -160, 68, 126]], ![![6, 172, -131, 53, 70]], ![![-65, 192, -103, 33, 43]]]
  g := ![![![-25041, -17547, -25187, 14042, 14482], ![-70564, -49448, -70977, 39574, 40806], ![-198916, -139393, -200082, 111562, 115026], ![-245124, -171775, -246562, 137481, 141744], ![-11131, -7801, -11197, 6245, 6435]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [80, 29, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 13, 96], [27, 83, 1], [0, 1]]
 g := ![![[19, 86, 47], [49, 54], [15, 62], [61, 85], [3, 86], [1]], ![[23, 86, 33, 12], [64, 35], [2, 4], [36, 73], [47, 53], [62, 87, 77, 96]], ![[13, 13, 50, 48], [62, 65], [47, 33], [39, 16], [69, 86], [75, 91, 17, 1]]]
 h' := ![![[32, 13, 96], [84, 19, 85], [67, 1, 32], [43, 65, 16], [49, 1, 45], [17, 68, 59], [0, 1]], ![[27, 83, 1], [5, 88, 52], [88, 49, 36], [32, 87, 2], [14, 3, 48], [66, 41, 76], [32, 13, 96]], ![[0, 1], [75, 87, 57], [31, 47, 29], [69, 42, 79], [45, 93, 4], [6, 85, 59], [27, 83, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 79], []]
 b := ![[], [68, 61, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [80, 29, 38, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![49623, 39892, -33234, 6643, 78190]
  a := ![2, -2, -1, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-80465, -38786, -68917, 6643, 78190]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![171, -101, -23, 28, 50]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![171, -101, -23, 28, 50]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![55, 4, 1, 0, 0], ![84, 20, 0, 1, 0], ![36, 41, 0, 0, 1]] where
  M :=![![![171, -101, -23, 28, 50], ![-66, 82, -7, -12, 18], ![-90, -163, 160, -68, -126], ![120, 81, -199, 127, -24], ![-67, -23, 127, -93, 75]]]
  hmulB := by decide  
  f := ![![![477, -1461, -5965, -14042, -14482]], ![![1320, -4168, -16823, -39574, -40806]], ![![363, -1122, -4565, -10744, -11080]], ![![732, -2275, -9237, -21737, -22416]], ![![737, -2311, -9352, -22003, -22689]]]
  g := ![![![-28, -27, -23, 28, 50], ![7, -4, -7, -12, 18], ![14, 59, 160, -68, -126], ![13, -7, -199, 127, -24], ![-20, -18, 127, -93, 75]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [42, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 96], [0, 1]]
 g := ![![[4, 25], [12], [75], [4], [85], [26, 1]], ![[72, 72], [12], [75], [4], [85], [52, 96]]]
 h' := ![![[26, 96], [84, 92], [54, 77], [87, 50], [62, 95], [72, 52], [0, 1]], ![[0, 1], [51, 5], [19, 20], [29, 47], [10, 2], [66, 45], [26, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [18, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [42, 71, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1604, -1456, 1748, -38, -2260]
  a := ![10, 6, 0, 2, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-136, 876, 1748, -38, -2260]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-477, 1461, 5965, 14042, 14482]] ![![171, -101, -23, 28, 50]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]] where
  M :=![![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 5 2 6 [2, 73, 77, 34, 75, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 82, 37, 32, 6], [72, 76, 50, 31, 20], [49, 12, 92, 79, 21], [79, 31, 23, 60, 54], [0, 1]]
 g := ![![[87, 58, 51, 53, 52], [49, 84, 45, 20], [60, 17, 92, 26, 14], [57, 71, 56, 84], [26, 1], []], ![[51, 8, 32, 17, 73, 8, 70, 20], [50, 69, 33, 5], [73, 57, 39, 48, 100, 56, 75, 33], [27, 90, 84, 47], [88, 81, 19, 30], [64, 75, 7, 51, 6, 72, 83, 14]], ![[75, 93, 10, 1, 47, 52, 87, 21], [18, 46, 8, 13], [45, 94, 69, 63, 86, 74, 45, 37], [90, 52, 53, 82], [19, 72, 62, 58], [71, 100, 75, 64, 44, 68, 73, 21]], ![[29, 69, 82, 43, 67, 91, 6, 56], [4, 69, 75, 71], [39, 28, 47, 23, 14, 78, 98, 22], [69, 79], [18, 99, 35, 82], [99, 34, 99, 61, 29, 33, 85, 70]], ![[60, 15, 95, 69, 39, 5, 57, 92], [9, 56, 72, 64], [87, 43, 51, 100, 88, 19], [85, 91, 63, 92], [45, 60, 1, 81], [9, 37, 64, 32, 6, 79, 12, 5]]]
 h' := ![![[28, 82, 37, 32, 6], [61, 3, 56, 10, 31], [82, 13, 27, 17, 90], [65, 84, 33, 40, 69], [49, 19, 46, 49, 36], [0, 0, 0, 1], [0, 1]], ![[72, 76, 50, 31, 20], [10, 58, 40, 65, 80], [3, 35, 49, 18, 45], [67, 99, 68, 24, 37], [90, 63, 52, 61, 42], [8, 81, 73, 14, 63], [28, 82, 37, 32, 6]], ![[49, 12, 92, 79, 21], [18, 91, 87, 97, 81], [85, 70, 49, 53, 35], [47, 87, 7, 4, 44], [5, 60, 27, 69, 53], [12, 20, 76, 54, 82], [72, 76, 50, 31, 20]], ![[79, 31, 23, 60, 54], [73, 9, 34, 26, 75], [9, 30, 72, 62, 24], [12, 3, 35, 63, 52], [7, 25, 100, 33], [89, 58, 73, 76, 48], [49, 12, 92, 79, 21]], ![[0, 1], [13, 41, 86, 4, 36], [58, 54, 5, 52, 8], [57, 30, 59, 71], [96, 35, 78, 91, 71], [40, 43, 81, 57, 9], [79, 31, 23, 60, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 48, 91, 57], [], [], []]
 b := ![[], [17, 67, 4, 30, 41], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 5
  hpos := by decide
  P := [2, 73, 77, 34, 75, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-471186311, -457250432, 740993570, -310507229, -171045318]
  a := ![6, 6, -3, 5, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4665211, -4527232, 7336570, -3074329, -1693518]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2233, -3359, 1233, -262, 6]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![2233, -3359, 1233, -262, 6]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![36, 73, 74, 1, 0], ![73, 70, 55, 0, 1]] where
  M :=![![![2233, -3359, 1233, -262, 6], ![-804, 2662, -2817, 1674, -1590], ![9792, 6171, -5456, 978, 14814], ![-20352, -19917, 25737, -12233, -18492], ![15855, 16391, -22383, 11281, 11989]]]
  hmulB := by decide  
  f := ![![![-2759, -17065, -28527, -61232, -61458]], ![![678, -30608, -78975, -179292, -183018]], ![![11178, -67119, -221078, -512808, -526698]], ![![7746, -76547, -227410, -523085, -535974]], ![![4516, -68699, -192056, -439383, -449513]]]
  g := ![![![109, 149, 197, -262, 6], ![534, -80, -381, 1674, -1590], ![-10746, -10701, -8666, 978, 14814], ![17184, 21044, 18913, -12233, -18492], ![-12286, -15984, -14724, 11281, 11989]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [9, 9, 99, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 11, 47], [89, 91, 56], [0, 1]]
 g := ![![[101, 91, 93], [48, 41, 16], [1, 56, 26], [23, 79], [95, 16], [1]], ![[45, 43, 8, 87], [87, 11, 81, 65], [20, 58, 30, 31], [95, 32], [74, 82], [39, 66, 72, 102]], ![[40, 15, 12, 72], [2, 15, 86, 58], [91, 78, 52, 1], [71, 100], [69, 38], [2, 90, 99, 1]]]
 h' := ![![[18, 11, 47], [83, 1, 14], [94, 10, 4], [27, 48, 51], [50, 90, 39], [94, 94, 4], [0, 1]], ![[89, 91, 56], [4, 70, 85], [55, 68, 10], [30, 44, 99], [24, 14, 54], [22, 65, 44], [18, 11, 47]], ![[0, 1], [35, 32, 4], [62, 25, 89], [11, 11, 56], [49, 102, 10], [19, 47, 55], [89, 91, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 50], []]
 b := ![[], [11, 100, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [9, 9, 99, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16776, 25188, -9062, 64605, 52700]
  a := ![3, 4, 0, 5, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-59768, -81359, -74644, 64605, 52700]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2759, -17065, -28527, -61232, -61458]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-2759, -17065, -28527, -61232, -61458]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![26, 58, 1, 0, 0], ![70, 31, 0, 1, 0], ![63, 94, 0, 0, 1]] where
  M :=![![![-2759, -17065, -28527, -61232, -61458], ![678, -30608, -78975, -179292, -183018], ![11178, -67119, -221078, -512808, -526698], ![20496, -68811, -271311, -637295, -656868], ![4305, 3853, -11757, -31633, -33755]]]
  hmulB := by decide  
  f := ![![![2233, -3359, 1233, -262, 6]], ![![-804, 2662, -2817, 1674, -1590]], ![![206, 711, -1328, 886, -750]], ![![1078, -1675, 240, 207, -654]], ![![786, 534, -2034, 1477, -1331]]]
  g := ![![![86379, 90415, -28527, -61232, -61458], ![253734, 265162, -78975, -179292, -183018], ![726580, 758855, -221078, -512808, -526698], ![903572, 943388, -271311, -637295, -656868], ![45154, 46984, -11757, -31633, -33755]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [7, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 102], [0, 1]]
 g := ![![[38, 59], [18, 93], [17, 2], [58], [41], [43, 1]], ![[0, 44], [0, 10], [0, 101], [58], [41], [86, 102]]]
 h' := ![![[43, 102], [80, 70], [87, 89], [89, 65], [86, 26], [8, 91], [0, 1]], ![[0, 1], [0, 33], [0, 14], [0, 38], [71, 77], [7, 12], [43, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [58, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [7, 60, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8779, -6972, 7989, 362, -9381]
  a := ![-16, -14, -1, -14, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3390, 3886, 7989, 362, -9381]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![2233, -3359, 1233, -262, 6]] ![![-2759, -17065, -28527, -61232, -61458]]
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


lemma PB402I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB402I2 : PrimesBelowBoundCertificateInterval O 61 103 402 where
  m := 9
  g := ![3, 2, 2, 1, 4, 2, 2, 1, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB402I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
    · exact ![I83N0, I83N1, I83N2, I83N3]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
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
    · exact ![25411681, 71]
    · exact ![389017, 5329]
    · exact ![3077056399]
    · exact ![6889, 83, 83, 83]
    · exact ![62742241, 89]
    · exact ![912673, 9409]
    · exact ![10510100501]
    · exact ![1092727, 10609]
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
      exact NI83N3
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
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
  β := ![I67N1, I67N2, I71N1, I83N1, I83N2, I83N3, I89N1]
  Il := ![[I67N1, I67N2], [I71N1], [], [], [I83N1, I83N2, I83N3], [I89N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
