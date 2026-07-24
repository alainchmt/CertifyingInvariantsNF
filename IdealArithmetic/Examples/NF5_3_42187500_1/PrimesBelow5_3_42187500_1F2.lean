
import IdealArithmetic.Examples.NF5_3_42187500_1.RI5_3_42187500_1
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


def P67P0 : CertificateIrreducibleZModOfList' 67 5 2 6 [37, 21, 42, 31, 20, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 36, 29, 65, 61], [59, 31, 38, 3, 42], [12, 8, 33, 32, 10], [14, 58, 34, 34, 21], [0, 1]]
 g := ![![[30, 65, 31, 5, 22], [14, 3, 31, 49, 22], [60, 60, 30, 16], [32, 34, 47, 1], [], []], ![[54, 23, 14, 53, 47, 2, 65, 50], [62, 20, 30, 29, 59, 1, 13, 44], [20, 15, 18, 25], [56, 32, 10, 10], [15, 9, 28, 23], [59, 65, 41, 36]], ![[27, 23, 14, 23, 52, 64, 7, 61], [34, 23, 23, 48, 2, 1, 38, 66], [38, 27, 41, 9], [23, 12, 8, 64], [41, 24, 42, 40], [9, 48, 13, 22]], ![[23, 65, 39, 48, 44, 20, 11, 6], [10, 8, 45, 29, 38, 11, 14, 62], [39, 44, 13, 21], [45, 44, 58, 1], [30, 6, 38, 23], [51, 56, 47, 33]], ![[49, 13, 52, 11, 54, 58, 32, 62], [5, 41, 21, 60, 42, 45, 6, 55], [53, 64, 51, 26], [25, 47, 26, 36], [38, 20, 9, 37], [54, 6, 45, 39]]]
 h' := ![![[29, 36, 29, 65, 61], [18, 33, 22, 38, 42], [6, 40, 66, 13, 42], [22, 13, 22, 40, 63], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[59, 31, 38, 3, 42], [8, 4, 49, 43, 58], [34, 61, 34, 54, 45], [29, 4, 19, 25, 5], [52, 15, 59, 59, 12], [65, 52, 30, 44, 36], [29, 36, 29, 65, 61]], ![[12, 8, 33, 32, 10], [4, 42, 10, 29, 32], [23, 30, 40, 31, 40], [42, 5, 40, 19, 64], [25, 24, 41, 20, 59], [66, 18, 27, 65, 24], [59, 31, 38, 3, 42]], ![[14, 58, 34, 34, 21], [10, 43, 15, 20, 58], [11, 21, 15, 3, 10], [39, 66, 16, 5, 50], [30, 25, 58, 39, 1], [66, 64, 20, 46, 36], [12, 8, 33, 32, 10]], ![[0, 1], [30, 12, 38, 4, 11], [66, 49, 46, 33, 64], [34, 46, 37, 45, 19], [50, 3, 43, 16, 61], [7, 0, 56, 46, 38], [14, 58, 34, 34, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 27, 9, 63], [], [], []]
 b := ![[], [57, 26, 12, 7, 44], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 5
  hpos := by decide
  P := [37, 21, 42, 31, 20, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11266428309470, 2424549871572, -1009615378616, -853690356236, -3802180157860]
  a := ![15, -20, -8, 12, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![168155646410, 36187311516, -15068886248, -12741647108, -56748957580]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-390, -97, -8, 21, 70]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-390, -97, -8, 21, 70]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![35, 26, 8, 50, 1]] where
  M :=![![![-390, -97, -8, 21, 70], ![-1071, -256, -46, 103, 154], ![-671, -253, -56, 5, 206], ![-1883, -277, -47, 150, 216], ![-1148, -370, -21, 64, 237]]]
  hmulB := by decide  
  f := ![![![-265, -28, 13, 32, 56]], ![![-872, -93, 43, 106, 184]], ![![-997, -107, 48, 121, 212]], ![![-2149, -227, 105, 260, 454]], ![![-2106, -223, 103, 255, 445]]]
  g := ![![![-40, -27, -8, -49, 70], ![-91, -60, -18, -107, 154], ![-111, -79, -24, -145, 206], ![-133, -83, -25, -150, 216], ![-133, -92, -27, -166, 237]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [45, 61, 45, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 6, 30, 66], [60, 11, 14, 52], [26, 53, 27, 24], [0, 1]]
 g := ![![[13, 21, 9, 2], [28, 15, 39, 6], [35, 35, 32, 40], [41, 30, 4], [1], []], ![[58, 49, 20, 70, 10, 7], [38, 15, 3, 41, 58, 69], [10, 49, 38, 54, 32, 67], [12, 42, 6], [46, 15, 10], [60, 5, 25]], ![[13, 48, 54, 16, 58, 23], [62, 33, 12, 44, 26, 23], [23, 40, 65, 51, 36, 11], [42, 58, 64], [44, 19, 25], [28, 24, 6]], ![[21, 64, 10, 35, 9, 38], [17, 15, 18, 65, 26, 36], [11, 29, 59, 50, 4, 8], [61, 47, 60], [32, 43, 54], [69, 2, 8]]]
 h' := ![![[54, 6, 30, 66], [18, 58, 32, 59], [58, 6, 63, 19], [38, 6, 11, 18], [26, 10, 26, 69], [0, 0, 1], [0, 1]], ![[60, 11, 14, 52], [9, 51, 30, 58], [34, 10, 45, 16], [32, 27, 0, 50], [69, 30, 21, 52], [3, 29, 69, 9], [54, 6, 30, 66]], ![[26, 53, 27, 24], [3, 56, 30, 9], [55, 40, 38, 62], [32, 24, 24, 41], [17, 15, 15, 63], [68, 23, 14, 5], [60, 11, 14, 52]], ![[0, 1], [60, 48, 50, 16], [61, 15, 67, 45], [17, 14, 36, 33], [63, 16, 9, 29], [56, 19, 58, 57], [26, 53, 27, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [70, 12, 62], []]
 b := ![[], [], [41, 55, 31, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [45, 61, 45, 2, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-157183209293540, -23797751649103, 9578192226271, 17853599509443, 42620051818775]
  a := ![120, -180, -58, 54, -477]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23223732717615, -15942522520243, -4667355243999, -29762661851117, 42620051818775]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![265, 28, -13, -32, -56]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![265, 28, -13, -32, -56]] 
 ![![71, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![64, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![265, 28, -13, -32, -56], ![872, 93, -43, -106, -184], ![997, 107, -48, -121, -212], ![2149, 227, -105, -260, -454], ![2153, 229, -106, -261, -455]]]
  hmulB := by decide  
  f := ![![![390, 97, 8, -21, -70]], ![![81, 20, 2, -5, -14]], ![![361, 91, 8, -19, -66]], ![![43, 8, 1, -3, -6]], ![![148, 38, 3, -8, -27]]]
  g := ![![![31, 28, -13, -32, -56], ![102, 93, -43, -106, -184], ![116, 107, -48, -121, -212], ![251, 227, -105, -260, -454], ![252, 229, -106, -261, -455]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-390, -97, -8, 21, 70]] ![![265, 28, -13, -32, -56]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46, -3, 6, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-46, -3, 6, 1, 0]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![27, 70, 6, 1, 0], ![35, 51, 17, 0, 1]] where
  M :=![![![-46, -3, 6, 1, 0], ![-1, -48, -12, 11, 4], ![-35, 11, -32, -19, 22], ![-173, 17, 33, -10, -16], ![8, -38, 5, 6, -19]]]
  hmulB := by decide  
  f := ![![![-91, 30, -7, 24, -22]], ![![306, -103, 23, -82, 74]], ![![-667, 223, -52, 179, -164]], ![![216, -73, 16, -58, 52]], ![![7, -3, 0, -2, 1]]]
  g := ![![![-1, -1, 0, 1, 0], ![-6, -14, -2, 11, 4], ![-4, 3, -4, -19, 22], ![9, 21, 5, -10, -16], ![7, 7, 4, 6, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [55, 19, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 1, 55], [22, 71, 18], [0, 1]]
 g := ![![[24, 5, 25], [47, 23], [33, 50], [55, 71, 32], [16, 1], []], ![[12, 64, 45, 46], [36, 61], [58, 1], [45, 20, 29, 1], [39, 4], [38, 32]], ![[14, 0, 59, 2], [17, 3], [45, 6], [23, 32, 5, 46], [40, 1], [2, 32]]]
 h' := ![![[67, 1, 55], [41, 70, 5], [12, 32, 60], [41, 30, 59], [69, 6, 18], [0, 0, 1], [0, 1]], ![[22, 71, 18], [9, 10, 44], [23, 42, 34], [1, 52, 72], [72, 9, 2], [63, 61, 71], [67, 1, 55]], ![[0, 1], [20, 66, 24], [15, 72, 52], [64, 64, 15], [71, 58, 53], [9, 12, 1], [22, 71, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 70], []]
 b := ![[], [52, 56, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [55, 19, 57, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18048599, 3871848, -1695532, -2268977, -5499005]
  a := ![11, -15, -5, 6, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3722961, 6070541, 1443855, -2268977, -5499005]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, 36, 11, -12, 2]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-79, 36, 11, -12, 2]] 
 ![![73, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-79, 36, 11, -12, 2], ![-18, -49, 65, 38, -46], ![335, -59, -160, -19, 76], ![-393, 213, 17, -84, 38], ![-235, 37, 112, 15, -53]]]
  hmulB := by decide  
  f := ![![![-280, -255, 66, -41, 276]], ![![-83, -21, 6, 6, 28]], ![![-161, -178, 46, -34, 190]], ![![-181, -28, 9, 19, 44]], ![![-106, -86, 23, -12, 95]]]
  g := ![![![-10, 36, 11, -12, 2], ![-30, -49, 65, 38, -46], ![93, -59, -160, -19, 76], ![-33, 213, 17, -84, 38], ![-65, 37, 112, 15, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24, -13, -6, 3, 8]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-24, -13, -6, 3, 8]] 
 ![![73, 0, 0, 0, 0], ![54, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![-24, -13, -6, 3, 8], ![-123, -10, -4, 1, 20], ![-89, -31, 14, 15, 2], ![-67, -65, -29, 16, 32], ![-116, -22, -17, 2, 29]]]
  hmulB := by decide  
  f := ![![![379, 196, -63, 6, -242]], ![![330, 143, -47, -4, -182]], ![![251, 145, -46, 9, -176]], ![![343, 107, -37, -18, -146]], ![![217, 105, -34, 1, -131]]]
  g := ![![![8, -13, -6, 3, 8], ![-1, -10, -4, 1, 20], ![3, -31, 14, 15, 2], ![43, -65, -29, 16, 32], ![12, -22, -17, 2, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-46, -3, 6, 1, 0]] ![![-79, 36, 11, -12, 2]]
  ![![5305, -1650, -1644, 240, 540]] where
 M := ![![![5305, -1650, -1644, 240, 540]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![5305, -1650, -1644, 240, 540]] ![![-24, -13, -6, 3, 8]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![143226, -28981, -64386, -5475, 29492]]]
 hmul := by decide  
 g := ![![![![1962, -397, -882, -75, 404]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![100, 55, 3, 3, -38]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![100, 55, 3, 3, -38]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![1, 39, 1, 0, 0], ![1, 59, 0, 1, 0], ![10, 25, 0, 0, 1]] where
  M :=![![![100, 55, 3, 3, -38], ![567, 44, 31, -73, -26], ![-52, 208, -13, 78, -146], ![1030, 2, 62, -159, 10], ![143, 229, -1, 55, -157]]]
  hmulB := by decide  
  f := ![![![-144, 89, -9, -39, 26]], ![![-351, -16, 239, 73, -130]], ![![-161, -11, 113, 36, -62]], ![![-271, -5, 176, 51, -94]], ![![-140, 9, 78, 18, -39]]]
  g := ![![![6, 9, 3, 3, -38], ![11, 48, 31, -73, -26], ![17, -3, -13, 78, -146], ![13, 85, 62, -159, 10], ![21, 12, -1, 55, -157]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [44, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 78], [0, 1]]
 g := ![![[5, 9], [15, 32], [3, 9], [67, 5], [52], [1]], ![[0, 70], [6, 47], [77, 70], [73, 74], [52], [1]]]
 h' := ![![[17, 78], [51, 76], [26, 43], [54, 3], [43, 20], [35, 17], [0, 1]], ![[0, 1], [0, 3], [46, 36], [26, 76], [67, 59], [8, 62], [17, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [40, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [44, 62, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1194669, -88118, 231965, 80426, 368561]
  a := ![-52, 75, 27, -35, 209]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-65730, -292328, 231965, 80426, 368561]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-307, -36, 13, 36, 64]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-307, -36, 13, 36, 64]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![32, 66, 1, 0, 0], ![37, 71, 0, 1, 0], ![58, 72, 0, 0, 1]] where
  M :=![![![-307, -36, 13, 36, 64], ![-996, -115, 43, 118, 208], ![-1121, -127, 50, 133, 236], ![-2397, -267, 109, 286, 502], ![-2381, -265, 110, 285, 501]]]
  hmulB := by decide  
  f := ![![![-26, 13, 2, -9, 6]], ![![-81, -4, 36, 25, -30]], ![![-75, 1, 30, 17, -22]], ![![-88, 4, 33, 18, -24]], ![![-94, 6, 35, 16, -23]]]
  g := ![![![-73, -102, 13, 36, 64], ![-238, -333, 43, 118, 208], ![-270, -378, 50, 133, 236], ![-577, -809, 109, 286, 502], ![-576, -808, 110, 285, 501]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [4, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 78], [0, 1]]
 g := ![![[4, 20], [2, 10], [70, 31], [57, 8], [19], [1]], ![[0, 59], [0, 69], [48, 48], [8, 71], [19], [1]]]
 h' := ![![[63, 78], [71, 39], [36, 22], [9, 49], [19, 61], [75, 63], [0, 1]], ![[0, 1], [0, 40], [0, 57], [15, 30], [70, 18], [15, 16], [63, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [21, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [4, 16, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-49581, -12248, 17064, 305, 20395]
  a := ![14, -17, -7, 18, -57]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-22656, -33273, 17064, 305, 20395]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-69, -20, -3, 6, 12]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-69, -20, -3, 6, 12]] 
 ![![79, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![-69, -20, -3, 6, 12], ![-186, -47, -13, 12, 36], ![-183, -33, 2, 11, 24], ![-277, -83, -9, 26, 46], ![-219, -63, -16, 17, 43]]]
  hmulB := by decide  
  f := ![![![-682, -1, 12, 107, 70]], ![![-265, -5, 6, 40, 32]], ![![-377, 2, 6, 60, 36]], ![![-95, -12, 5, 11, 22]], ![![-602, -2, 11, 94, 63]]]
  g := ![![![-2, -20, -3, 6, 12], ![-8, -47, -13, 12, 36], ![-11, -33, 2, 11, 24], ![-7, -83, -9, 26, 46], ![-7, -63, -16, 17, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![100, 55, 3, 3, -38]] ![![-307, -36, 13, 36, 64]]
  ![![-5556, -1037, -38, 517, 1016]] where
 M := ![![![-5556, -1037, -38, 517, 1016]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-5556, -1037, -38, 517, 1016]] ![![-69, -20, -3, 6, 12]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![217487, 54194, 9164, -15484, -37446]]]
 hmul := by decide  
 g := ![![![![2753, 686, 116, -196, -474]]]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-58, -7, 28, 15, -18]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-58, -7, 28, 15, -18]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![77, 71, 73, 1, 0], ![72, 78, 27, 0, 1]] where
  M :=![![![-58, -7, 28, 15, -18], ![255, -104, -78, 5, 42], ![-445, 193, 16, -41, 10], ![-277, -35, 203, 26, -72], ![116, -110, -27, 68, -25]]]
  hmulB := by decide  
  f := ![![![4745, 504, -233, -576, -1004]], ![![15636, 1661, -767, -1898, -3308]], ![![17941, 1907, -880, -2177, -3796]], ![![34021, 3615, -1669, -4129, -7198]], ![![25112, 2668, -1232, -3048, -5313]]]
  g := ![![![1, 4, -7, 15, -18], ![-38, -45, -19, 5, 42], ![24, 28, 33, -41, 10], ![35, 45, 3, 26, -72], ![-40, -36, -52, 68, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [40, 46, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 19, 75], [36, 63, 8], [0, 1]]
 g := ![![[29, 76, 25], [78, 63, 10], [38, 30], [42, 21], [70, 38, 1], []], ![[39, 17, 19, 26], [56, 9, 13, 36], [53, 31], [63, 26], [44, 26, 10, 37], [53, 64]], ![[26, 34, 64, 53], [45, 26, 39, 34], [30, 41], [41, 26], [40, 51, 66, 66], [37, 64]]]
 h' := ![![[2, 19, 75], [34, 62, 5], [51, 79, 50], [49, 69, 69], [22, 74, 42], [0, 0, 1], [0, 1]], ![[36, 63, 8], [36, 57, 68], [68, 2, 28], [14, 1, 60], [25, 24, 62], [42, 58, 63], [2, 19, 75]], ![[0, 1], [18, 47, 10], [3, 2, 5], [46, 13, 37], [21, 68, 62], [65, 25, 19], [36, 63, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 41], []]
 b := ![[], [32, 1, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [40, 46, 45, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21000100, 1518300, -1348020, -2619612, -4549424]
  a := ![6, -12, -2, -14, -24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6629744, 6534528, 3767688, -2619612, -4549424]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4745, 504, -233, -576, -1004]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![4745, 504, -233, -576, -1004]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![2, 52, 1, 0, 0], ![63, 5, 0, 1, 0], ![52, 13, 0, 0, 1]] where
  M :=![![![4745, 504, -233, -576, -1004], ![15636, 1661, -767, -1898, -3308], ![17941, 1907, -880, -2177, -3796], ![38529, 4095, -1889, -4676, -8150], ![38641, 4109, -1894, -4689, -8175]]]
  hmulB := by decide  
  f := ![![![-58, -7, 28, 15, -18]], ![![255, -104, -78, 5, 42]], ![![153, -63, -48, 3, 26]], ![![-32, -12, 19, 12, -12]], ![![5, -22, 5, 11, -5]]]
  g := ![![![1129, 344, -233, -576, -1004], ![3720, 1133, -767, -1898, -3308], ![4268, 1300, -880, -2177, -3796], ![9165, 2791, -1889, -4676, -8150], ![9192, 2799, -1894, -4689, -8175]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [36, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 82], [0, 1]]
 g := ![![[39, 30], [35, 78], [10], [75], [5, 49], [1]], ![[0, 53], [0, 5], [10], [75], [16, 34], [1]]]
 h' := ![![[7, 82], [68, 14], [2, 59], [69, 33], [69, 65], [47, 7], [0, 1]], ![[0, 1], [0, 69], [0, 24], [51, 50], [26, 18], [13, 76], [7, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [34, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [36, 76, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10061, 547, 2079, 1458, 3909]
  a := ![0, 10, 7, 1, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3727, -1996, 2079, 1458, 3909]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-58, -7, 28, 15, -18]] ![![4745, 504, -233, -576, -1004]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7100, 755, -348, -861, -1502]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![7100, 755, -348, -861, -1502]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![35, 18, 41, 1, 0], ![3, 5, 14, 0, 1]] where
  M :=![![![7100, 755, -348, -861, -1502], ![23391, 2488, -1146, -2839, -4946], ![26819, 2857, -1312, -3253, -5678], ![57621, 6123, -2821, -6990, -12184], ![57770, 6148, -2831, -7008, -12221]]]
  hmulB := by decide  
  f := ![![![-83, -26, -7, 8, 16]], ![![-248, -53, -13, 10, 48]], ![![-241, -47, 8, 25, 20]], ![![-197, -44, -2, 17, 26]], ![![-58, -12, 0, 5, 7]]]
  g := ![![![469, 267, 629, -861, -1502], ![1546, 880, 2073, -2839, -4946], ![1772, 1009, 2377, -3253, -5678], ![3807, 2167, 5105, -6990, -12184], ![3817, 2173, 5119, -7008, -12221]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [44, 83, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 35, 17], [76, 53, 72], [0, 1]]
 g := ![![[40, 75, 85], [42, 47], [61, 44], [6, 61, 17], [55, 7, 1], []], ![[8, 65, 2, 21], [15, 73], [16, 67], [0, 60, 77, 34], [66, 25, 58, 49], [9, 22]], ![[83, 74, 56, 5], [49, 45], [31, 42], [72, 27, 74, 45], [82, 21, 69, 1], [43, 22]]]
 h' := ![![[20, 35, 17], [46, 30, 21], [84, 29, 15], [3, 44, 69], [72, 22, 27], [0, 0, 1], [0, 1]], ![[76, 53, 72], [18, 42, 21], [12, 28, 42], [2, 8, 44], [86, 8, 25], [4, 41, 53], [20, 35, 17]], ![[0, 1], [52, 17, 47], [28, 32, 32], [71, 37, 65], [79, 59, 37], [57, 48, 35], [76, 53, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 13], []]
 b := ![[], [78, 80, 83], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [44, 83, 82, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![393028, 58744, -21053, -48972, -70408]
  a := ![2, -5, -1, -3, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![26048, 14520, 33399, -48972, -70408]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-83, -26, -7, 8, 16]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-83, -26, -7, 8, 16]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![25, 4, 1, 0, 0], ![46, 45, 0, 1, 0], ![5, 11, 0, 0, 1]] where
  M :=![![![-83, -26, -7, 8, 16], ![-248, -53, -13, 10, 48], ![-241, -47, 8, 25, 20], ![-283, -125, -27, 28, 70], ![-299, -67, -26, 21, 55]]]
  hmulB := by decide  
  f := ![![![7100, 755, -348, -861, -1502]], ![![23391, 2488, -1146, -2839, -4946]], ![![3347, 356, -164, -406, -708]], ![![16144, 1717, -791, -1959, -3414]], ![![3939, 419, -193, -478, -833]]]
  g := ![![![-4, -6, -7, 8, 16], ![-7, -11, -13, 10, 48], ![-19, -16, 8, 25, 20], ![-14, -23, -27, 28, 70], ![-10, -17, -26, 21, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [46, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 88], [0, 1]]
 g := ![![[], [], [84], [0, 44], [], [1]], ![[], [], [84], [0, 45], [], [1]]]
 h' := ![![[0, 88], [34], [52], [0, 23], [0, 69], [43], [0, 1]], ![[0, 1], [34], [52], [0, 66], [0, 20], [43], [0, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [0, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [46, 0, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-53825, -22047, 24820, -1611, 31185]
  a := ![-16, 22, 13, -24, 67]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8496, -4403, 24820, -1611, 31185]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![7100, 755, -348, -861, -1502]] ![![-83, -26, -7, 8, 16]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0, 0, 0]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]] where
  M :=![![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 5 2 6 [29, 72, 30, 41, 24, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 76, 69, 5, 52], [79, 55, 69, 9, 39], [62, 86, 50, 84, 77], [18, 73, 6, 96, 26], [0, 1]]
 g := ![![[13, 60, 7, 14, 93], [89, 22, 7, 86], [37, 36, 34, 36], [48, 21, 92, 75], [73, 1], []], ![[44, 6, 29, 27, 5, 71], [30, 86, 21, 79], [35, 91, 13, 66], [85, 48, 38, 47], [32, 14, 94, 47], [39, 47, 26, 89, 15, 47, 52, 55]], ![[48, 80, 32, 91, 5, 90, 66, 69], [25, 84, 62, 4], [28, 55, 21, 43], [32, 85, 9, 94], [5, 9, 45, 75], [27, 16, 56, 55, 42, 43, 49, 52]], ![[37, 81, 13, 13, 77, 66, 94, 41], [57, 72, 47, 16], [52, 4, 79, 72], [12, 90, 2, 81], [9, 69, 25, 35], [66, 41, 0, 58, 31, 10, 54, 51]], ![[20, 82, 38, 68, 76, 53, 77, 56], [75, 80, 5, 3], [62, 74, 6, 2], [44, 77, 35, 53], [37, 38, 50, 1], [41, 6, 84, 81, 8, 79, 38, 19]]]
 h' := ![![[11, 76, 69, 5, 52], [6, 11, 10, 34, 53], [29, 23, 1, 94, 59], [61, 60, 94, 91, 6], [17, 50, 66, 81, 50], [0, 0, 0, 1], [0, 1]], ![[79, 55, 69, 9, 39], [36, 40, 34, 40], [79, 69, 9, 24, 46], [30, 16, 6, 64, 39], [78, 1, 40, 8, 85], [6, 40, 51, 38, 85], [11, 76, 69, 5, 52]], ![[62, 86, 50, 84, 77], [67, 83, 76, 55, 65], [93, 30, 47, 9, 95], [41, 3, 96, 23, 25], [22, 82, 14, 18, 71], [78, 30, 42, 64, 47], [79, 55, 69, 9, 39]], ![[18, 73, 6, 96, 26], [31, 42, 19, 64, 35], [36, 30, 27, 66, 4], [34, 3, 54, 21, 13], [73, 67, 76, 65, 9], [25, 0, 49, 54, 61], [62, 86, 50, 84, 77]], ![[0, 1], [25, 18, 55, 1, 41], [39, 42, 13, 1, 87], [73, 15, 41, 92, 14], [66, 91, 95, 22, 76], [84, 27, 52, 37, 1], [18, 73, 6, 96, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 94, 84, 45], [], [], []]
 b := ![[], [44, 24, 48, 54, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 5
  hpos := by decide
  P := [29, 72, 30, 41, 24, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-840585542883, -396223540108, 147694251550, -18580043286, 516056122758]
  a := ![-10, 13, 5, -11, 41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8665830339, -4084778764, 1522621150, -191546838, 5320166214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 8587340257 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, -132, 58, 72, -62]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![157, -132, 58, 72, -62]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![61, 51, 74, 64, 1]] where
  M :=![![![157, -132, 58, 72, -62], ![858, -89, -446, -80, 226], ![-2084, 728, 583, -140, -160], ![228, -624, 568, 423, -440], ![1426, -490, -406, 102, 131]]]
  hmulB := by decide  
  f := ![![![77, -24, 6, -20, 18]], ![![-250, 87, -18, 68, -62]], ![![556, -184, 43, -148, 136]], ![![-668, 224, -48, 179, -160]], ![![-91, 35, -4, 26, -21]]]
  g := ![![![39, 30, 46, 40, -62], ![-128, -115, -170, -144, 226], ![76, 88, 123, 100, -160], ![268, 216, 328, 283, -440], ![-65, -71, -100, -82, 131]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 4 2 6 [44, 15, 10, 94, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 98, 46, 98], [71, 24, 98, 12], [45, 79, 58, 92], [0, 1]]
 g := ![![[92, 40, 85, 96], [18, 59, 24], [80, 25, 31, 96], [68, 1, 95], [39, 7, 1], []], ![[51, 41, 7, 64, 96, 55], [90, 53, 88], [79, 42, 37, 80, 87, 12], [76, 83, 4], [1, 22, 70], [85, 71, 1, 30, 43, 74]], ![[99, 1, 45, 21, 47, 66], [35, 71, 20], [44, 40, 78, 50, 97, 44], [19, 85, 58], [67, 12, 49], [11, 37, 16, 29, 94, 11]], ![[10, 14, 6, 48, 62, 65], [45, 96, 97], [8, 89, 69, 1, 80, 23], [8, 74, 9], [79, 72, 45], [60, 56, 5, 10, 2, 79]]]
 h' := ![![[93, 98, 46, 98], [39, 24, 47, 55], [15, 29, 88, 78], [39, 79, 60, 46], [1, 16, 67, 87], [0, 0, 0, 1], [0, 1]], ![[71, 24, 98, 12], [1, 65, 87, 7], [74, 26, 35, 54], [95, 13, 63, 81], [56, 42, 62, 99], [91, 75, 92, 26], [93, 98, 46, 98]], ![[45, 79, 58, 92], [5, 33, 31, 37], [63, 18, 72, 90], [43, 50, 74, 24], [24, 87, 58, 19], [89, 84, 99, 7], [71, 24, 98, 12]], ![[0, 1], [18, 80, 37, 2], [33, 28, 7, 81], [58, 60, 5, 51], [39, 57, 15, 98], [9, 43, 11, 67], [45, 79, 58, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [82, 29, 56], []]
 b := ![[], [], [63, 14, 88, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 4
  hpos := by decide
  P := [44, 15, 10, 94, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-477018273, -61373887, 34127937, 57432369, 120317816]
  a := ![-3, 7, 3, -1, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-77390149, -61362203, -87815747, -75672355, 120317816]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 104060401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, 24, -6, 20, -18]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-77, 24, -6, 20, -18]] 
 ![![101, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-77, 24, -6, 20, -18], ![250, -87, 18, -68, 62], ![-556, 184, -43, 148, -136], ![668, -224, 48, -179, 160], ![-470, 158, -38, 126, -119]]]
  hmulB := by decide  
  f := ![![![-157, 132, -58, -72, 62]], ![![-80, 61, -22, -32, 26]], ![![-26, 32, -23, -20, 20]], ![![-52, 48, -24, -27, 24]], ![![-25, 14, 0, -6, 3]]]
  g := ![![![-15, 24, -6, 20, -18], ![54, -87, 18, -68, 62], ![-114, 184, -43, 148, -136], ![140, -224, 48, -179, 160], ![-97, 158, -38, 126, -119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![157, -132, 58, 72, -62]] ![![-77, 24, -6, 20, -18]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![268, 313, -533, -275, 362]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![268, 313, -533, -275, 362]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![49, 51, 7, 1, 0], ![98, 14, 1, 0, 1]] where
  M :=![![![268, 313, -533, -275, 362], ![-5155, 1392, 1883, -67, -738], ![8146, -3718, -1229, 1212, -134], ![4472, 760, -3852, -1363, 2290], ![-5773, 2605, 921, -833, 57]]]
  hmulB := by decide  
  f := ![![![688, -161, 39, -161, 106]], ![![-1429, 684, -149, 451, -538]], ![![4524, -1296, 295, -1138, 902]], ![![-111, 191, -39, 81, -168]], ![![547, -83, 22, -113, 43]]]
  g := ![![![-211, 90, 10, -275, 362], ![684, 147, 30, -67, -738], ![-370, -618, -93, 1212, -134], ![-1487, 371, 33, -1363, 2290], ![286, 430, 65, -833, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [22, 75, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 20, 63], [36, 82, 40], [0, 1]]
 g := ![![[36, 50, 46], [42, 41, 59], [17, 59, 1], [9, 61], [73, 92], [1]], ![[29, 94, 19, 19], [58, 31, 51, 52], [74, 27, 98, 14], [26, 82], [51, 8], [26, 80, 63, 66]], ![[39, 49, 14, 101], [92, 4, 75, 53], [65, 33, 71, 77], [61, 92], [14, 64], [102, 102, 81, 37]]]
 h' := ![![[32, 20, 63], [3, 70, 56], [38, 60, 33], [26, 56, 102], [11, 24, 79], [81, 28, 68], [0, 1]], ![[36, 82, 40], [64, 53, 41], [21, 77, 100], [82, 46, 47], [6, 42, 59], [60, 50, 27], [32, 20, 63]], ![[0, 1], [12, 83, 6], [58, 69, 73], [25, 1, 57], [53, 37, 68], [19, 25, 8], [36, 82, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 44], []]
 b := ![[], [8, 76, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [22, 75, 35, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1404369838, 773956485, -245539197, -88333706, -904311997]
  a := ![60, -75, -39, 62, -233]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![916070846, 174168383, 12399114, -88333706, -904311997]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-124, -13, 6, 15, 26]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-124, -13, 6, 15, 26]] 
 ![![103, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![53, 0, 0, 0, 1]] where
  M :=![![![-124, -13, 6, 15, 26], ![-405, -44, 20, 49, 86], ![-467, -49, 22, 57, 98], ![-997, -107, 49, 120, 212], ![-1004, -106, 49, 122, 211]]]
  hmulB := by decide  
  f := ![![![-273, -26, 9, 12, 28]], ![![-36, -5, 1, 2, 4]], ![![-70, -7, 1, 3, 8]], ![![-56, -5, 2, 2, 6]], ![![-148, -15, 5, 7, 15]]]
  g := ![![![-17, -13, 6, 15, 26], ![-56, -44, 20, 49, 86], ![-64, -49, 22, 57, 98], ![-138, -107, 49, 120, 212], ![-138, -106, 49, 122, 211]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, -4, -6, -6, -8]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![29, -4, -6, -6, -8]] 
 ![![103, 0, 0, 0, 0], ![77, 1, 0, 0, 0], ![87, 0, 1, 0, 0], ![93, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![29, -4, -6, -6, -8], ![126, -5, -18, -22, -32], ![188, 4, -19, -28, -44], ![438, 18, -40, -63, -100], ![476, 28, -38, -66, -107]]]
  hmulB := by decide  
  f := ![![![287, -112, 34, -62, 56]], ![![207, -81, 24, -44, 40]], ![![259, -100, 31, -58, 52]], ![![235, -94, 30, -49, 44]], ![![64, -24, 6, -14, 13]]]
  g := ![![![15, -4, -6, -6, -8], ![45, -5, -18, -22, -32], ![47, 4, -19, -28, -44], ![97, 18, -40, -63, -100], ![92, 28, -38, -66, -107]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![268, 313, -533, -275, 362]] ![![-124, -13, 6, 15, 26]]
  ![![-359, -86, 405, 140, -266]] where
 M := ![![![-359, -86, 405, 140, -266]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-359, -86, 405, 140, -266]] ![![29, -4, -6, -6, -8]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-10403, -1442, 515, 1442, 2266]]]
 hmul := by decide  
 g := ![![![![-101, -14, 5, 14, 22]]]]
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


lemma PB318I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB318I2 : PrimesBelowBoundCertificateInterval O 61 103 318 where
  m := 9
  g := ![1, 2, 3, 3, 2, 2, 1, 2, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB318I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
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
    · exact ![389017, 73, 73]
    · exact ![6241, 6241, 79]
    · exact ![571787, 6889]
    · exact ![704969, 7921]
    · exact ![8587340257]
    · exact ![104060401, 101]
    · exact ![1092727, 103, 103]
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
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
  β := ![I71N1, I73N1, I73N2, I79N2, I101N1, I103N1, I103N2]
  Il := ![[], [I71N1], [I73N1, I73N2], [I79N2], [], [], [], [I101N1], [I103N1, I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
