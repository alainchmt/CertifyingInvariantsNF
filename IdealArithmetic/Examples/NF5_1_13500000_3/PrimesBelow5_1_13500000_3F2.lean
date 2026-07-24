
import IdealArithmetic.Examples.NF5_1_13500000_3.RI5_1_13500000_3
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


def P67P0 : CertificateIrreducibleZModOfList' 67 5 2 6 [57, 1, 38, 60, 66, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 49, 51, 30, 61], [54, 37, 17, 66, 41], [44, 59, 15, 58, 2], [4, 55, 51, 47, 30], [0, 1]]
 g := ![![[10, 10, 38, 11, 39], [45, 31, 66, 13, 22], [9, 40, 14, 36], [44, 8, 1, 1], [], []], ![[66, 27, 25, 0, 24, 0, 1, 66], [0, 45, 3, 47, 28, 7, 58, 52], [56, 65, 17, 49], [6, 47, 26, 47], [9, 14, 20, 37], [57, 15, 11, 36]], ![[42, 3, 4, 45, 43, 5, 56, 41], [18, 4, 0, 57, 6, 60, 37, 42], [17, 42, 40, 9], [55, 66, 39, 49], [55, 62, 38, 21], [50, 21, 58, 6]], ![[24, 55, 46, 0, 49, 24, 7, 7], [22, 27, 28, 43, 18, 54, 63, 11], [37, 27, 51, 40], [19, 20, 38, 22], [33, 39, 7, 23], [62, 3, 35, 4]], ![[8, 35, 58, 4, 11, 40, 36, 53], [21, 15, 32, 24, 31, 18, 38, 66], [64, 21, 19, 64], [7, 19, 26, 15], [17, 28, 48, 33], [14, 13, 35, 29]]]
 h' := ![![[33, 49, 51, 30, 61], [48, 46, 31, 44, 21], [60, 45, 27, 36, 25], [38, 36, 5, 13, 61], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[54, 37, 17, 66, 41], [26, 10, 20, 27, 18], [22, 26, 32, 13, 61], [47, 41, 61, 31, 60], [11, 63, 21, 59, 39], [51, 44, 11, 54, 29], [33, 49, 51, 30, 61]], ![[44, 59, 15, 58, 2], [47, 37, 17, 10, 1], [6, 2, 49, 50, 32], [38, 15, 5, 6, 64], [15, 25, 65, 28, 7], [66, 2, 55, 34, 17], [54, 37, 17, 66, 41]], ![[4, 55, 51, 47, 30], [32, 8, 6, 15, 29], [58, 34, 47, 63, 46], [36, 54, 53, 10, 24], [28, 42, 13, 64, 42], [10, 1, 45, 30, 31], [44, 59, 15, 58, 2]], ![[0, 1], [28, 33, 60, 38, 65], [51, 27, 46, 39, 37], [58, 55, 10, 7, 59], [51, 4, 35, 50, 45], [22, 20, 22, 16, 57], [4, 55, 51, 47, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 24, 12, 1], [], [], []]
 b := ![[], [64, 16, 10, 25, 56], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 5
  hpos := by decide
  P := [57, 1, 38, 60, 66, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11662989825, -5189938456, -5243956938, 5426237138, 11914244783]
  a := ![-22, -8, 30, -26, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-174074475, -77461768, -78268014, 80988614, 177824549]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0, 0, 0]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]] where
  M :=![![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 5 2 6 [20, 58, 38, 19, 29, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 64, 44, 51, 35], [49, 17, 18, 57, 32], [10, 34, 69, 45, 6], [51, 26, 11, 60, 69], [0, 1]]
 g := ![![[46, 6, 4, 54, 29], [17, 28, 48, 4, 64], [6, 5, 35, 37, 50], [34, 41, 42, 1], [], []], ![[52, 34, 69, 64, 24, 25, 31, 34], [2, 17, 61, 17, 54, 8, 54, 55], [59, 17, 58, 57, 2, 16, 8, 14], [17, 10, 9, 5], [70, 27, 16, 30], [5, 17, 66, 18]], ![[53, 65, 36, 65, 6, 33, 0, 36], [10, 53, 49, 37, 45, 12, 48, 64], [34, 61, 63, 6, 63, 61, 55, 10], [70, 2, 55, 36], [19, 25, 23, 54], [42, 20, 9, 30]], ![[44, 21, 3, 21, 3, 63, 66, 1], [7, 36, 67, 50, 70, 55, 66, 16], [32, 54, 22, 23, 44, 46, 36, 50], [16, 40, 25, 36], [34, 64, 66, 5], [69, 29, 64, 36]], ![[17, 6, 13, 29, 20, 56, 64, 67], [43, 54, 63, 47, 10, 69, 37, 34], [2, 53, 21, 18, 52, 54, 15, 66], [42, 35, 68, 43], [43, 15, 26, 1], [0, 30, 70, 4]]]
 h' := ![![[3, 64, 44, 51, 35], [15, 3, 44, 44, 61], [22, 26, 29, 63, 8], [30, 48, 34, 26, 60], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[49, 17, 18, 57, 32], [24, 3, 41, 30, 28], [20, 10, 16, 10, 48], [51, 47, 66, 18, 16], [65, 57, 12, 8, 54], [51, 38, 18, 15, 39], [3, 64, 44, 51, 35]], ![[10, 34, 69, 45, 6], [43, 55, 50, 6, 9], [35, 47, 43, 48, 12], [28, 23, 28, 55, 49], [47, 28, 6, 9, 65], [70, 37, 40, 39, 14], [49, 17, 18, 57, 32]], ![[51, 26, 11, 60, 69], [21, 35, 16, 36, 56], [3, 32, 43, 41, 60], [55, 41, 32, 59, 48], [34, 2, 55, 24, 6], [69, 3, 5, 25, 17], [10, 34, 69, 45, 6]], ![[0, 1], [57, 46, 62, 26, 59], [11, 27, 11, 51, 14], [1, 54, 53, 55, 40], [29, 55, 69, 30, 16], [45, 64, 7, 63, 1], [51, 26, 11, 60, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 11, 65, 30], [], [], []]
 b := ![[], [55, 52, 30, 38, 60], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 5
  hpos := by decide
  P := [20, 58, 38, 19, 29, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31204676424563, -6198188290872, -6222226918776, 1874590106689, 20349282148049]
  a := ![17, -58, -22, -45, 58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![439502484853, -87298426632, -87636998856, 26402677559, 286609607719]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 1804229351 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3301, -3338, -2116, 488, 4454]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![3301, -3338, -2116, 488, 4454]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![39, 59, 12, 1, 0], ![37, 63, 58, 0, 1]] where
  M :=![![![3301, -3338, -2116, 488, 4454], ![-15864, 1673, 2642, -2280, -10984], ![34816, -15502, -6615, -3836, 12016], ![-23772, 11346, 14452, -13147, -45392], ![31116, -10656, -6588, 444, 17453]]]
  hmulB := by decide  
  f := ![![![67309, -6398, -24408, 11600, 25770]], ![![-56680, 54501, -24458, -2416, 59320]], ![![-246944, -83554, 187637, -58580, -271104]], ![![-44233, 25715, -3674, -4403, 18550]], ![![-214555, -22383, 117008, -43380, -152713]]]
  g := ![![![-2473, -4284, -3648, 488, 4454], ![6568, 11345, 9138, -2280, -10984], ![-3564, -7482, -9007, -3836, 12016], ![29705, 49955, 38424, -13147, -45392], ![-8657, -15567, -14030, 444, 17453]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [24, 61, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 22, 47], [27, 50, 26], [0, 1]]
 g := ![![[43, 16, 71], [43, 16], [62, 48], [54, 18, 8], [17, 1], []], ![[66, 70, 50, 17], [27, 18], [33, 1], [34, 63, 44, 22], [66, 18], [55, 19]], ![[61, 22, 64, 59], [68, 69], [19, 71], [68, 1, 53, 14], [70, 46], [3, 19]]]
 h' := ![![[63, 22, 47], [6, 69, 12], [4, 56, 69], [18, 21, 62], [30, 34, 9], [0, 0, 1], [0, 1]], ![[27, 50, 26], [6, 0, 47], [17, 59, 23], [15, 65, 72], [25, 11, 4], [21, 56, 50], [63, 22, 47]], ![[0, 1], [44, 4, 14], [56, 31, 54], [1, 60, 12], [72, 28, 60], [0, 17, 22], [27, 50, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 71], []]
 b := ![[], [57, 17, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [24, 61, 56, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17358, 23442, -8770, 17850, 38030]
  a := ![-7, -5, 10, -11, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28574, -46926, -33270, 17850, 38030]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, 0, 0, 1]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-1, 0, 0, 0, 1]] 
 ![![73, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![72, 0, 0, 0, 1]] where
  M :=![![![-1, 0, 0, 0, 1], ![-4, -1, 2, 0, -4], ![16, -2, -9, 4, 16], ![-22, 6, 2, -1, -2], ![14, -4, -4, 2, 7]]]
  hmulB := by decide  
  f := ![![![33, 8, 16, -22, -43]], ![![12, 3, 6, -8, -16]], ![![8, 2, 3, -4, -8]], ![![20, 6, 10, -13, -26]], ![![34, 8, 16, -22, -43]]]
  g := ![![![-1, 0, 0, 0, 1], ![4, -1, 2, 0, -4], ![-16, -2, -9, 4, 16], ![0, 6, 2, -1, -2], ![-6, -4, -4, 2, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51, 21, 1, -8, 26]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-51, 21, 1, -8, 26]] 
 ![![73, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![62, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![-51, 21, 1, -8, 26], ![-136, -58, 121, -30, -216], ![744, -45, -310, 122, 444], ![-576, 307, -5, -51, 74], ![472, -154, -86, 56, 105]]]
  hmulB := by decide  
  f := ![![![2477, -831, 1471, -3248, -6254]], ![![1013, -275, 588, -1250, -2422]], ![![1656, -253, 920, -1806, -3548]], ![![2870, -479, 1603, -3179, -6234]], ![![1335, -363, 775, -1648, -3193]]]
  g := ![![![-14, 21, 1, -8, 26], ![94, -58, 121, -30, -216], ![-155, -45, -310, 122, 444], ![-103, 307, -5, -51, 74], ![-1, -154, -86, 56, 105]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![3301, -3338, -2116, 488, 4454]] ![![-1, 0, 0, 0, 1]]
  ![![27815, -7318, -4472, -44, 12999]] where
 M := ![![![27815, -7318, -4472, -44, 12999]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![27815, -7318, -4472, -44, 12999]] ![![-51, 21, 1, -8, 26]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![2410387, -805555, -589037, 181624, 1679949]]]
 hmul := by decide  
 g := ![![![![33019, -11035, -8069, 2488, 23013]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4455, -1170, -928, 658, 451]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![4455, -1170, -928, 658, 451]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![33, 44, 6, 71, 1]] where
  M :=![![![4455, -1170, -928, 658, 451], ![828, 4185, -4216, 776, 7408], ![-26528, -2612, 14345, -5328, -18768], ![26466, -10848, -1982, 3301, -3464], ![-18330, 4000, 4596, -2810, -3421]]]
  hmulB := by decide  
  f := ![![![495, 302, 196, -84, -271]], ![![748, 607, 264, 56, -92]], ![![592, 1068, 87, 752, 1152]], ![![-1174, 412, -702, 1563, 3006]], ![![-387, 918, -396, 1461, 2630]]]
  g := ![![![-132, -266, -46, -397, 451], ![-3084, -4073, -616, -6648, 7408], ![7504, 10420, 1607, 16800, -18768], ![1782, 1792, 238, 3155, -3464], ![1197, 1956, 318, 3039, -3421]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 4 2 6 [6, 65, 11, 49, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 62, 28, 51], [12, 49, 12, 36], [72, 46, 39, 71], [0, 1]]
 g := ![![[9, 66, 36, 23], [52, 51, 33, 20], [40, 20, 27, 26], [66, 30, 33, 31], [1], []], ![[69, 73, 39, 30, 53, 22], [78, 28, 8, 21, 65, 32], [39, 34, 2, 25, 4, 13], [32, 14, 70, 22, 27, 50], [63, 20, 25], [1, 69, 73]], ![[43, 69, 25, 25, 19, 26], [43, 6, 11, 15, 78, 52], [48, 66, 43, 15, 74, 65], [52, 10, 22, 69, 27, 40], [60, 66, 4], [54, 7, 32]], ![[78, 13, 42, 41, 33, 48], [22, 46, 37, 49, 22, 7], [6, 36, 26, 39, 28, 43], [67, 41, 67, 7, 47, 34], [32, 65, 9], [14, 32, 64]]]
 h' := ![![[25, 62, 28, 51], [4, 36, 63, 55], [76, 46, 14, 39], [78, 69, 39, 42], [73, 14, 68, 30], [0, 0, 1], [0, 1]], ![[12, 49, 12, 36], [73, 33, 75, 45], [76, 46, 42, 53], [53, 5, 3, 61], [28, 3, 26, 7], [66, 14, 73, 74], [25, 62, 28, 51]], ![[72, 46, 39, 71], [64, 15, 63, 7], [35, 43, 20, 63], [51, 36, 2, 2], [45, 76, 1, 19], [57, 73, 26, 2], [12, 49, 12, 36]], ![[0, 1], [58, 74, 36, 51], [52, 23, 3, 3], [57, 48, 35, 53], [6, 65, 63, 23], [44, 71, 58, 3], [72, 46, 39, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 11, 42], []]
 b := ![[], [], [71, 30, 68, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 4
  hpos := by decide
  P := [6, 65, 11, 49, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2035300424, -1294072641, -629621425, 89041738, 594157572]
  a := ![31, 27, -42, 50, 108]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-273955700, -347303871, -53095783, -532862606, 594157572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 38950081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-495, -302, -196, 84, 271]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-495, -302, -196, 84, 271]] 
 ![![79, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![-495, -302, -196, 84, 271], ![-748, -607, -264, -56, 92], ![-592, -1068, -87, -752, -1152], ![1174, -412, 702, -1563, -3006], ![18, -188, 48, -242, -423]]]
  hmulB := by decide  
  f := ![![![-4455, 1170, 928, -658, -451]], ![![-2097, 495, 488, -318, -305]], ![![-2653, 818, 441, -374, -65]], ![![-1914, 552, 354, -275, -116]], ![![-1065, 290, 212, -156, -88]]]
  g := ![![![158, -302, -196, 84, 271], ![445, -607, -264, -56, 92], ![1153, -1068, -87, -752, -1152], ![1166, -412, 702, -1563, -3006], ![265, -188, 48, -242, -423]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![4455, -1170, -928, 658, 451]] ![![-495, -302, -196, 84, 271]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2733, 5119, -5921, 1276, 9922]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![2733, 5119, -5921, 1276, 9922]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![22, 16, 75, 80, 1]] where
  M :=![![![2733, 5119, -5921, 1276, 9922], ![-34584, -1912, 17307, -6738, -21824], ![60344, -24015, -5132, 7662, -7036], ![46688, 32393, -50683, 13561, 78618], ![-4376, -20190, 20470, -3840, -35655]]]
  hmulB := by decide  
  f := ![![![-545, -295, -225, 140, 382]], ![![-968, -630, -371, 110, 432]], ![![-1288, -1229, -426, -302, -188]], ![![256, -693, 289, -1085, -1954]], ![![-1250, -1981, -238, -1262, -1871]]]
  g := ![![![-2597, -1851, -9037, -9548, 9922], ![5368, 4184, 19929, 20954, -21824], ![2592, 1067, 6296, 6874, -7036], ![-20276, -14765, -71651, -75613, 78618], ![9398, 6630, 32465, 34320, -35655]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [51, 14, 14, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 18, 37, 37], [14, 51, 62, 75], [33, 13, 67, 54], [0, 1]]
 g := ![![[40, 56, 23, 27], [33, 58, 82, 64], [69, 59, 64], [10, 80, 3], [82, 1], []], ![[7, 52, 19, 59, 27, 29], [78, 78, 75, 60, 18, 3], [16, 63, 65], [41, 49, 70], [77, 61, 65, 57, 64, 64], [11, 41, 41]], ![[11, 75, 41, 51, 71, 29], [63, 9, 43, 72, 9, 10], [31], [62, 74, 75], [57, 13, 35, 57, 44, 48], [34, 23, 64]], ![[70, 5, 48, 24, 22, 80], [71, 54, 4, 57, 14, 72], [52, 82, 63], [2, 7, 1], [19, 77, 34, 58, 18, 52], [8, 4, 11]]]
 h' := ![![[35, 18, 37, 37], [60, 78, 73, 39], [57, 7, 22, 75], [16, 57, 39, 75], [51, 46, 0, 70], [0, 0, 1], [0, 1]], ![[14, 51, 62, 75], [49, 77, 35, 26], [30, 26, 34, 39], [79, 34, 13, 56], [57, 44, 67, 30], [0, 11, 12, 24], [35, 18, 37, 37]], ![[33, 13, 67, 54], [59, 19, 65, 61], [25, 40, 50, 71], [19, 78, 23], [44, 31, 12, 65], [39, 28, 26, 34], [14, 51, 62, 75]], ![[0, 1], [59, 75, 76, 40], [21, 10, 60, 64], [10, 80, 8, 35], [19, 45, 4, 1], [17, 44, 44, 25], [33, 13, 67, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [32, 63, 38], []]
 b := ![[], [], [8, 36, 65, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [51, 14, 14, 1, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![478524063, -54107351, -137559021, -5737124, 298542229]
  a := ![-35, -7, 48, -31, -122]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-73366325, -58202205, -271424412, -287820668, 298542229]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-545, -295, -225, 140, 382]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-545, -295, -225, 140, 382]] 
 ![![83, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![-545, -295, -225, 140, 382], ![-968, -630, -371, 110, 432], ![-1288, -1229, -426, -302, -188], ![256, -693, 289, -1085, -1954], ![-152, -238, -38, -136, -189]]]
  hmulB := by decide  
  f := ![![![2733, 5119, -5921, 1276, 9922]], ![![1098, 2814, -3073, 626, 5236]], ![![2110, 2301, -3058, 738, 4936]], ![![793, 822, -1110, 271, 1784]], ![![2351, 4259, -4961, 1076, 8297]]]
  g := ![![![-77, -295, -225, 140, 382], ![136, -630, -371, 110, 432], ![1072, -1229, -426, -302, -188], ![2051, -693, 289, -1085, -1954], ![327, -238, -38, -136, -189]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![2733, 5119, -5921, 1276, 9922]] ![![-545, -295, -225, 140, 382]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 29, 67, -94, -197]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![149, 29, 67, -94, -197]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![39, 50, 48, 19, 1]] where
  M :=![![![149, 29, 67, -94, -197], ![412, 122, 199, -242, -528], ![1144, 369, 518, -570, -1276], ![1206, 485, 519, -501, -1174], ![266, 90, 122, -126, -283]]]
  hmulB := by decide  
  f := ![![![3, -3, 1, 0, -1]], ![![4, 4, -5, 2, 4]], ![![-8, 1, 0, -2, 12]], ![![-30, -7, 21, -5, -40]], ![![-7, 0, 2, -1, 0]]]
  g := ![![![88, 111, 107, 41, -197], ![236, 298, 287, 110, -528], ![572, 721, 694, 266, -1276], ![528, 665, 639, 245, -1174], ![127, 160, 154, 59, -283]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [29, 51, 12, 33, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 10, 11, 43], [44, 85, 9, 86], [46, 82, 69, 49], [0, 1]]
 g := ![![[38, 67, 21, 5], [54, 46, 55], [6, 63, 71], [39, 43, 66, 81], [56, 1], []], ![[37, 66, 58, 9, 27, 41], [62, 69, 81], [76, 48, 79], [52, 35, 47, 31, 48, 86], [85, 1, 32, 53, 38, 75], [21, 4, 69]], ![[7, 19, 66, 3, 33, 70], [19, 67, 2], [30, 47, 16], [76, 61, 1, 39, 81, 3], [62, 22, 25, 28, 4, 51], [10, 5, 9]], ![[21, 37, 64, 63, 88, 47], [65, 84, 72], [50, 85, 36], [81, 56, 41, 3, 50, 36], [35, 86, 22, 17, 51, 36], [29, 64, 87]]]
 h' := ![![[55, 10, 11, 43], [81, 14, 33, 19], [57, 11, 59, 12], [26, 7, 79, 31], [67, 52, 78, 9], [0, 0, 1], [0, 1]], ![[44, 85, 9, 86], [81, 22, 12, 11], [30, 79, 85, 80], [86, 73, 36, 48], [66, 8, 37, 64], [13, 2, 10, 67], [55, 10, 11, 43]], ![[46, 82, 69, 49], [83, 11, 70, 6], [10, 26, 8, 25], [41, 28, 83, 4], [82, 12, 86, 55], [44, 61, 83, 61], [44, 85, 9, 86]], ![[0, 1], [53, 42, 63, 53], [46, 62, 26, 61], [28, 70, 69, 6], [24, 17, 66, 50], [29, 26, 84, 50], [46, 82, 69, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [57, 64, 36], []]
 b := ![[], [], [11, 71, 38, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [29, 51, 12, 33, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1227567921, -546469166, -227460026, 40671094, 996655982]
  a := ![28, -2, -38, 10, 98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-422943993, -566059194, -540078058, -212312276, 996655982]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 3, -1, 0, 1]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-3, 3, -1, 0, 1]] 
 ![![89, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![64, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![-3, 3, -1, 0, 1], ![-4, -4, 5, -2, -4], ![8, -1, 0, 2, -12], ![30, 7, -21, 5, 40], ![-14, -2, 10, -2, -23]]]
  hmulB := by decide  
  f := ![![![-149, -29, -67, 94, 197]], ![![-13, -3, -6, 8, 17]], ![![-120, -25, -54, 74, 156]], ![![-114, -25, -51, 69, 146]], ![![-80, -16, -36, 50, 105]]]
  g := ![![![0, 3, -1, 0, 1], ![0, -4, 5, -2, -4], ![5, -1, 0, 2, -12], ![-9, 7, -21, 5, 40], ![6, -2, 10, -2, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![149, 29, 67, -94, -197]] ![![-3, 3, -1, 0, 1]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 5 2 6 [74, 40, 35, 26, 96, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 83, 40, 84, 10], [93, 46, 45, 63, 48], [60, 9, 21, 28, 12], [4, 55, 88, 19, 27], [0, 1]]
 g := ![![[86, 51, 19, 87, 36], [13, 76, 7, 73], [47, 79, 69, 43], [88, 37, 86, 43], [1, 1], []], ![[77, 47, 74, 78, 79, 47, 58, 41], [72, 8, 5, 9], [80, 3, 15, 25], [60, 40, 75, 73], [79, 84, 79, 81], [84, 46, 61, 88, 91, 4, 10, 30]], ![[89, 61, 58, 92, 39, 18, 6, 31], [35, 31, 68, 86], [54, 8, 93, 93], [11, 34, 37, 33], [32, 80, 96, 54], [52, 62, 6, 42, 13, 84, 35, 12]], ![[67, 69, 88, 3, 61, 18, 23, 70], [59, 82, 44, 6], [18, 35, 95, 32], [80, 43, 23, 44], [80, 17, 5, 89], [81, 14, 76, 56, 75, 81, 50, 79]], ![[21, 85, 94, 49, 32, 78, 2, 44], [20, 5, 5, 27], [45, 3, 65, 50], [4, 82, 11, 54], [24, 28, 51, 48], [64, 47, 3, 23, 26, 95, 29, 89]]]
 h' := ![![[38, 83, 40, 84, 10], [33, 22, 39, 77, 6], [5, 54, 36, 31, 49], [31, 41, 77, 15, 72], [23, 80, 22, 36, 72], [0, 0, 0, 1], [0, 1]], ![[93, 46, 45, 63, 48], [77, 54, 88, 37, 84], [19, 6, 45, 33, 94], [33, 49, 43, 1, 92], [60, 96, 16, 2, 49], [59, 3, 90, 43, 9], [38, 83, 40, 84, 10]], ![[60, 9, 21, 28, 12], [91, 47, 80, 35, 36], [16, 29, 65, 84, 38], [61, 22, 21, 0, 44], [14, 44, 64, 54, 18], [65, 2, 57, 63, 65], [93, 46, 45, 63, 48]], ![[4, 55, 88, 19, 27], [49, 68, 62, 96, 64], [27, 28, 4, 23, 43], [1, 20, 64, 43, 56], [95, 0, 29, 86, 23], [1, 95, 46, 64, 63], [60, 9, 21, 28, 12]], ![[0, 1], [7, 3, 22, 46, 4], [41, 77, 44, 23, 67], [49, 62, 86, 38, 27], [32, 71, 63, 16, 32], [81, 94, 1, 23, 57], [4, 55, 88, 19, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87, 63, 71, 79], [], [], []]
 b := ![[], [68, 27, 73, 40, 60], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 5
  hpos := by decide
  P := [74, 40, 35, 26, 96, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-75101045842, 10657427151, 22315774313, -7604831622, -36593480860]
  a := ![-13, 7, 23, 2, -52]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-774237586, 109870383, 230059529, -78400326, -377252380]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![373, 145, 165, -164, -378]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![373, 145, 165, -164, -378]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![55, 57, 77, 1, 0], ![0, 66, 22, 0, 1]] where
  M :=![![![373, 145, 165, -164, -378], ![856, 374, 373, -326, -784], ![1832, 903, 762, -558, -1428], ![1312, 831, 511, -191, -658], ![376, 198, 154, -96, -263]]]
  hmulB := by decide  
  f := ![![![177, -63, -41, 12, 126]], ![![-456, 148, 117, -34, -336]], ![![1208, -373, -320, 98, 868]], ![![747, -231, -197, 61, 532]], ![![-24, 12, 4, 0, -23]]]
  g := ![![![93, 341, 209, -164, -378], ![186, 700, 423, -326, -784], ![322, 1257, 744, -558, -1428], ![117, 546, 294, -191, -658], ![56, 228, 132, -96, -263]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [49, 20, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 11, 84], [73, 89, 17], [0, 1]]
 g := ![![[22, 52, 16], [21, 5], [90, 14, 100], [84, 5], [26, 25], [1]], ![[14, 13, 0, 100], [31, 14], [64, 3, 2, 68], [64, 88], [16, 24], [41, 9, 21, 36]], ![[69, 3, 54, 19], [93, 68], [85, 59, 54, 84], [41, 81], [41, 21], [15, 53, 21, 65]]]
 h' := ![![[33, 11, 84], [26, 54, 97], [34, 18, 56], [79, 6, 10], [16, 13, 45], [52, 81, 5], [0, 1]], ![[73, 89, 17], [15, 28, 39], [76, 42, 32], [63, 67, 81], [88, 97, 47], [93, 33, 78], [33, 11, 84]], ![[0, 1], [64, 19, 66], [50, 41, 13], [76, 28, 10], [41, 92, 9], [38, 88, 18], [73, 89, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 26], []]
 b := ![[], [51, 57, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [49, 20, 96, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![655442, -265688, -128201, 45574, 378186]
  a := ![13, -1, -18, 8, 46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18328, -275482, -118391, 45574, 378186]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 3, -9, 18, 36]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-13, 3, -9, 18, 36]] 
 ![![101, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![55, 0, 0, 1, 0], ![66, 0, 0, 0, 1]] where
  M :=![![![-13, 3, -9, 18, 36], ![-72, -4, -33, 54, 108], ![-216, -51, -112, 150, 324], ![-312, -87, -135, 161, 348], ![-48, -18, -30, 36, 83]]]
  hmulB := by decide  
  f := ![![![1255, 3, -567, 234, 684]], ![![765, 11, -354, 144, 432]], ![![853, -18, -367, 156, 432]], ![![773, -6, -342, 143, 408]], ![![774, 0, -348, 144, 419]]]
  g := ![![![-29, 3, -9, 18, 36], ![-75, -4, -33, 54, 108], ![-185, -51, -112, 150, 324], ![-169, -87, -135, 161, 348], ![-42, -18, -30, 36, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-301, -395, -75, -204, -277]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-301, -395, -75, -204, -277]] 
 ![![101, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![78, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![-301, -395, -75, -204, -277], ![292, -580, 275, -966, -1748], ![3128, -399, 1720, -3314, -6532], ![6290, 1057, 3073, -4425, -9260], ![990, 34, 510, -854, -1729]]]
  hmulB := by decide  
  f := ![![![-959, 4881, -4045, 550, 7555]], ![![-1094, 4112, -3279, 410, 6210]], ![![-82, 3599, -3264, 522, 5910]], ![![-169, 2118, -1866, 285, 3409]], ![![-239, 1505, -1273, 180, 2362]]]
  g := ![![![562, -395, -75, -204, -277], ![1244, -580, 275, -966, -1748], ![2520, -399, 1720, -3314, -6532], ![1619, 1057, 3073, -4425, -9260], ![499, 34, 510, -854, -1729]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![373, 145, 165, -164, -378]] ![![-13, 3, -9, 18, 36]]
  ![![18383, 13196, 6858, -718, -5898]] where
 M := ![![![18383, 13196, 6858, -718, -5898]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![18383, 13196, 6858, -718, -5898]] ![![-301, -395, -75, -204, -277]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![9416533, -18610765, 8831541, -31010838, -56108833]]]
 hmul := by decide  
 g := ![![![![93233, -184265, 87441, -307038, -555533]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, -5, -5, 0, 9]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![21, -5, -5, 0, 9]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![57, 21, 11, 1, 0], ![71, 91, 91, 0, 1]] where
  M :=![![![21, -5, -5, 0, 9], ![-36, 16, 13, -10, -36], ![104, -33, 4, -14, 4], ![-18, 39, 23, -19, -88], ![66, -26, -6, -2, 33]]]
  hmulB := by decide  
  f := ![![![-3, -3, -1, 2, 3]], ![![-4, -2, -9, 6, 16]], ![![-40, -7, -6, 6, 20]], ![![-7, -3, -3, 3, 7]], ![![-41, -10, -14, 12, 34]]]
  g := ![![![-6, -8, -8, 0, 9], ![30, 34, 33, -10, -36], ![6, -1, -2, -14, 4], ![71, 82, 80, -19, -88], ![-21, -29, -29, -2, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [88, 27, 98, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 25, 67], [84, 77, 36], [0, 1]]
 g := ![![[84, 29, 50], [96, 24, 76], [93], [32, 36], [61, 25], [1]], ![[48, 73], [64, 60, 29, 12], [85, 77, 67, 73], [92, 29], [42, 15], [30, 102, 86, 3]], ![[1, 68, 50, 49], [17, 61, 42, 56], [38, 82, 85, 30], [74, 19], [39, 14], [4, 50, 43, 100]]]
 h' := ![![[24, 25, 67], [101, 80, 16], [56, 54, 73], [14, 89], [7, 81, 97], [15, 76, 5], [0, 1]], ![[84, 77, 36], [98, 92], [78, 35, 72], [90, 62, 92], [7, 11, 21], [60, 42, 18], [24, 25, 67]], ![[0, 1], [40, 34, 87], [41, 14, 61], [74, 55, 11], [71, 11, 88], [102, 88, 80], [84, 77, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 92], []]
 b := ![[], [41, 2, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [88, 27, 98, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3258256, -4673809, -2967865, 2437242, 7021486]
  a := ![45, 13, -59, 47, 156]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6220452, -6745739, -6492551, 2437242, 7021486]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 3, 1, -2, -3]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![3, 3, 1, -2, -3]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![26, 81, 1, 0, 0], ![80, 29, 0, 1, 0], ![23, 41, 0, 0, 1]] where
  M :=![![![3, 3, 1, -2, -3], ![4, 2, 9, -6, -16], ![40, 7, 6, -6, -20], ![26, 19, -3, -3, 6], ![6, -2, 6, -2, -13]]]
  hmulB := by decide  
  f := ![![![-21, 5, 5, 0, -9]], ![![36, -16, -13, 10, 36]], ![![22, -11, -9, 8, 26]], ![![-6, -1, 0, 3, 4]], ![![9, -5, -4, 4, 12]]]
  g := ![![![2, 1, 1, -2, -3], ![6, 1, 9, -6, -16], ![8, 5, 6, -6, -20], ![2, 1, -3, -3, 6], ![3, 1, 6, -2, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [99, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 102], [0, 1]]
 g := ![![[38, 17], [90, 55], [87, 25], [56], [60], [49, 1]], ![[47, 86], [4, 48], [76, 78], [56], [60], [98, 102]]]
 h' := ![![[49, 102], [51, 74], [39, 63], [52, 98], [31, 57], [93, 36], [0, 1]], ![[0, 1], [72, 29], [36, 40], [13, 5], [43, 46], [3, 67], [49, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [89, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [99, 54, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1842, -1628, -2051, 2068, 6868]
  a := ![19, 5, -26, 18, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2640, -1719, -2051, 2068, 6868]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![21, -5, -5, 0, 9]] ![![3, 3, 1, -2, -3]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB229I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB229I2 : PrimesBelowBoundCertificateInterval O 61 103 229 where
  m := 9
  g := ![1, 1, 3, 2, 2, 2, 1, 3, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB229I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0]
    · exact ![I71N0]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
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
    · exact ![1350125107]
    · exact ![1804229351]
    · exact ![389017, 73, 73]
    · exact ![38950081, 79]
    · exact ![47458321, 83]
    · exact ![62742241, 89]
    · exact ![8587340257]
    · exact ![1030301, 101, 101]
    · exact ![1092727, 10609]
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
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
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I73N1, I73N2, I79N1, I83N1, I89N1, I101N1, I101N2]
  Il := ![[], [], [I73N1, I73N2], [I79N1], [I83N1], [I89N1], [], [I101N1, I101N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
