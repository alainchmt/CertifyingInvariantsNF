
import IdealArithmetic.Examples.NF5_3_1822500000_2.RI5_3_1822500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 75, 25, 34, 114]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![53, 75, 25, 34, 114]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![14, 24, 27, 1, 0], ![23, 8, 26, 0, 1]] where
  M :=![![![53, 75, 25, 34, 114], ![-288, -157, -65, -99, -328], ![744, 288, 160, 233, 758], ![-1416, -486, -137, -318, -1086], ![144, 15, -24, 1, 17]]]
  hmulB := by decide  
  f := ![![![1, 27, -13, -18, -56]], ![![48, 73, 1, -17, -44]], ![![-168, 36, -156, -145, -486]], ![![-74, 132, -129, -145, -468]], ![![-149, 64, -155, -151, -501]]]
  g := ![![![-105, -57, -133, 34, 114], ![298, 167, 384, -99, -328], ![-688, -392, -891, 233, 758], ![966, 546, 1265, -318, -1086], ![-9, -5, -17, 1, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [14, 8, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 4, 25], [13, 24, 4], [0, 1]]
 g := ![![[26, 20, 28], [12, 20], [13, 21, 9], [1]], ![[9, 22], [16, 13], [15, 12, 25, 9], [19, 24, 7, 23]], ![[26, 25, 25, 25], [27, 9], [20, 19, 12, 1], [14, 26, 3, 6]]]
 h' := ![![[13, 4, 25], [12, 14, 12], [21, 1, 7], [15, 21, 26], [0, 1]], ![[13, 24, 4], [2, 3], [9, 19, 19], [17, 3, 18], [13, 4, 25]], ![[0, 1], [12, 12, 17], [10, 9, 3], [0, 5, 14], [13, 24, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 8], []]
 b := ![[], [24, 18, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [14, 8, 3, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3283302370, -413949815, -4269059028, -3193753823, -9283567132]
  a := ![-180, -61, -183, -126, -395]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8791423972, 5189816517, 11149484125, -3193753823, -9283567132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 27, -13, -18, -56]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![1, 27, -13, -18, -56]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![22, 2, 1, 0, 0], ![14, 18, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![1, 27, -13, -18, -56], ![48, 73, 1, -17, -44], ![-168, 36, -156, -145, -486], ![1224, 726, 629, 370, 1390], ![-360, -285, -148, -59, -253]]]
  hmulB := by decide  
  f := ![![![53, 75, 25, 34, 114]], ![![-288, -157, -65, -99, -328]], ![![46, 56, 20, 27, 90]], ![![-202, -78, -33, -56, -186]], ![![47, 60, 19, 27, 91]]]
  g := ![![![63, 13, -13, -18, -56], ![44, 13, 1, -17, -44], ![568, 102, -156, -145, -486], ![-1716, -248, 629, 370, 1390], ![329, 37, -148, -59, -253]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [24, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 28], [0, 1]]
 g := ![![[13, 23], [24], [6, 16], [7, 1]], ![[0, 6], [24], [2, 13], [14, 28]]]
 h' := ![![[7, 28], [5, 20], [1, 13], [6, 25], [0, 1]], ![[0, 1], [0, 9], [5, 16], [7, 4], [7, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [27, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [24, 22, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2448903, 622196, 2449046, 1796942, 5532486]
  a := ![309, 41, 314, 215, 678]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7028775, -1262788, 2449046, 1796942, 5532486]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![53, 75, 25, 34, 114]] ![![1, 27, -13, -18, -56]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-179, -36, -1, -25, -90]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-179, -36, -1, -25, -90]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![27, 8, 25, 1, 0], ![0, 3, 22, 0, 1]] where
  M :=![![![-179, -36, -1, -25, -90], ![360, 31, 209, 189, 550], ![408, -54, 1178, 859, 2362], ![5160, -234, 8327, 6336, 17622], ![-1584, 102, -2850, -2146, -5951]]]
  hmulB := by decide  
  f := ![![![43, -12, 41, 39, 130]], ![![-312, -191, -155, -89, -338]], ![![1704, 594, 1086, 803, 2838]], ![![999, 272, 676, 524, 1830]], ![![1272, 447, 809, 597, 2111]]]
  g := ![![![16, 14, 84, -25, -90], ![-153, -101, -536, 189, 550], ![-735, -452, -2331, 859, 2362], ![-5352, -3348, -17347, 6336, 17622], ![1818, 1133, 5862, -2146, -5951]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [10, 11, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 25, 16], [15, 5, 15], [0, 1]]
 g := ![![[4, 23, 16], [5, 5, 18], [16, 22, 5], [1]], ![[26, 26, 18, 2], [5, 19, 0, 20], [22, 6, 10, 25], [10, 4, 4, 4]], ![[24, 2, 2, 29], [10, 8, 0, 23], [17, 22, 28, 27], [13, 28, 3, 27]]]
 h' := ![![[22, 25, 16], [12, 13, 27], [26, 14, 24], [21, 20, 6], [0, 1]], ![[15, 5, 15], [11, 15, 2], [10, 9, 3], [8, 4, 9], [22, 25, 16]], ![[0, 1], [4, 3, 2], [28, 8, 4], [21, 7, 16], [15, 5, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 30], []]
 b := ![[], [17, 10, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [10, 11, 25, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-347029, 17204, -594897, -451240, -1252493]
  a := ![-5, -4, -5, -4, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![381821, 238213, 1233579, -451240, -1252493]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, 12, -41, -39, -130]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-43, 12, -41, -39, -130]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![14, 6, 1, 0, 0], ![9, 9, 0, 1, 0], ![8, 7, 0, 0, 1]] where
  M :=![![![-43, 12, -41, -39, -130], ![312, 191, 155, 89, 338], ![-1704, -594, -1086, -803, -2838], ![10296, 4566, 6061, 4172, 15026], ![-2880, -1362, -1652, -1108, -4019]]]
  hmulB := by decide  
  f := ![![![179, 36, 1, 25, 90]], ![![-360, -31, -209, -189, -550]], ![![-2, 12, -78, -53, -142]], ![![-219, 9, -329, -252, -702]], ![![16, -1, 45, 33, 91]]]
  g := ![![![62, 49, -41, -39, -130], ![-173, -126, 155, 89, 338], ![1401, 1065, -1086, -803, -2838], ![-7494, -5630, 6061, 4172, 15026], ![2012, 1505, -1652, -1108, -4019]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [5, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 30], [0, 1]]
 g := ![![[9, 25], [14, 1], [9, 25], [17, 1]], ![[0, 6], [0, 30], [0, 6], [3, 30]]]
 h' := ![![[17, 30], [23, 26], [17, 30], [8, 5], [0, 1]], ![[0, 1], [0, 5], [0, 1], [0, 26], [17, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [20, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [5, 14, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2512832, 602592, 2592143, 1911590, 5831054]
  a := ![319, 126, 324, 221, 700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3149352, -2353934, 2592143, 1911590, 5831054]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-179, -36, -1, -25, -90]] ![![-43, 12, -41, -39, -130]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [23, 14, 14, 3, 15, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 29, 22, 27, 32], [6, 25, 5, 32, 22], [7, 30, 18, 0, 32], [25, 26, 29, 15, 25], [0, 1]]
 g := ![![[20, 12, 36, 18, 4], [31, 33, 23, 3], [27, 31, 0, 22, 1], [], []], ![[5, 21, 31, 15, 5, 31, 24, 20], [7, 21, 35, 11], [13, 29, 18, 19, 20, 18, 0, 13], [1, 24, 13, 10], [32, 8, 21, 25]], ![[3, 4, 33, 16, 1, 1, 9, 31], [10, 19, 13, 3], [21, 34, 18, 8, 20, 5, 25, 6], [15, 16, 34, 7], [21, 30, 31, 3]], ![[9, 36, 21, 18, 24, 13, 33, 2], [0, 36, 13, 16], [17, 24, 14, 31, 22, 22, 10, 2], [0, 22, 5, 26], [30, 5, 32, 25]], ![[19, 31, 21, 21, 12, 0, 9, 1], [1, 33, 30, 26], [27, 5, 26, 28, 33, 18, 32, 28], [25, 27, 4, 33], [9, 8, 33, 33]]]
 h' := ![![[21, 29, 22, 27, 32], [17, 36, 4, 36, 35], [8, 19, 2, 15, 22], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[6, 25, 5, 32, 22], [35, 13, 27, 11, 25], [23, 29, 22, 14, 23], [15, 14, 17, 22, 29], [1, 31, 19, 1, 26], [21, 29, 22, 27, 32]], ![[7, 30, 18, 0, 32], [32, 12, 0, 33, 20], [15, 11, 17, 34, 15], [34, 11, 8, 20, 9], [34, 19, 35, 18, 9], [6, 25, 5, 32, 22]], ![[25, 26, 29, 15, 25], [30, 5, 3, 3, 9], [17, 6, 27, 27, 4], [33, 34, 0, 16, 9], [25, 33, 0, 8, 27], [7, 30, 18, 0, 32]], ![[0, 1], [4, 8, 3, 28, 22], [29, 9, 6, 21, 10], [27, 15, 12, 16, 26], [11, 28, 19, 10, 12], [25, 26, 29, 15, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 1, 26, 10], [], [], []]
 b := ![[], [6, 29, 1, 9, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [23, 14, 14, 3, 15, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2874971155418608154, -250534317922307778, -4004242842314331705, -3006306271403651802, -8630069846954088328]
  a := ![-391, -131, -396, -270, -858]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-77701923119421842, -6771197781683994, -108222779522008965, -81251520848747346, -233245130998759144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 69343957 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [25, 19, 5, 5, 26, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 8, 8, 28, 24], [17, 6, 11, 10, 16], [32, 3, 5, 31, 16], [37, 23, 17, 13, 26], [0, 1]]
 g := ![![[34, 15, 33, 12, 10], [31, 40, 5, 1], [18, 16, 27, 20], [1], []], ![[36, 22, 7, 8, 22, 22, 38, 11], [27, 1, 4, 1], [10, 24, 30, 25], [16, 25, 27, 27, 31, 29, 20, 15], [16, 38, 21, 2]], ![[8, 40, 13, 18, 30, 27, 4, 2], [37, 28, 39, 2], [3, 7, 22, 39], [23, 10, 35, 39, 33, 34, 19, 25], [35, 31, 19, 10]], ![[0, 38, 19, 34, 10, 32, 38, 4], [21, 31, 11, 40], [8, 8, 33, 36], [36, 18, 17, 14, 19, 9, 31, 20], [13, 38, 35, 10]], ![[36, 15, 17, 5, 14, 2, 1, 7], [20, 31, 33, 23], [38, 7, 3, 32], [22, 2, 40, 16, 15, 11, 4, 12], [10, 13, 33, 20]]]
 h' := ![![[11, 8, 8, 28, 24], [2, 35, 4, 29, 16], [11, 3, 34, 36, 1], [16, 22, 36, 36, 15], [0, 0, 1], [0, 1]], ![[17, 6, 11, 10, 16], [26, 34, 39, 20, 38], [39, 21, 37, 26, 40], [17, 13, 21, 14, 36], [8, 29, 20, 25, 4], [11, 8, 8, 28, 24]], ![[32, 3, 5, 31, 16], [39, 31, 21, 5, 35], [12, 29, 9, 13, 24], [28, 1, 17, 21, 11], [29, 35, 32, 23, 9], [17, 6, 11, 10, 16]], ![[37, 23, 17, 13, 26], [13, 32, 27, 18, 21], [13, 18, 29, 6, 9], [7, 3, 36, 9, 6], [2, 20, 20, 24, 14], [32, 3, 5, 31, 16]], ![[0, 1], [12, 32, 32, 10, 13], [26, 11, 14, 1, 8], [22, 2, 13, 2, 14], [12, 39, 9, 10, 14], [37, 23, 17, 13, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 6, 19, 37], [], [], []]
 b := ![[], [35, 27, 1, 21, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [25, 19, 5, 5, 26, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![332816195804789233, 137415817963170408, 205765279244726432, 144845252861634848, 513694424174174362]
  a := ![216, 72, 220, 140, 474]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8117468190360713, 3351605316174888, 5018665347432352, 3532811045405728, 12529132296931082]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 115856201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![869, 370, 502, 352, 1276]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![869, 370, 502, 352, 1276]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![27, 35, 1, 24, 1]] where
  M :=![![![869, 370, 502, 352, 1276], ![-5280, -2167, -3282, -2314, -8184], ![29808, 12840, 17143, 11962, 43588], ![-184848, -75396, -116458, -82165, -289404], ![51648, 20922, 32892, 23234, 81525]]]
  hmulB := by decide  
  f := ![![![-145, -406, 118, 192, 580]], ![![-96, -757, 270, 438, 1336]], ![![-528, -1608, 489, 794, 2404]], ![![-528, -3108, 1062, 1725, 5252]], ![![-465, -2597, 883, 1434, 4365]]]
  g := ![![![-781, -1030, -18, -704, 1276], ![5016, 6611, 114, 4514, -8184], ![-26676, -35180, -615, -24050, 43588], ![177420, 233808, 4022, 159617, -289404], ![-49989, -65871, -1131, -44962, 81525]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [37, 2, 0, 34, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 10, 39, 33], [5, 17, 42, 5], [17, 15, 5, 5], [0, 1]]
 g := ![![[5, 35, 8, 11], [8, 21, 22, 36], [7, 30, 25], [9, 1], []], ![[23, 33, 25, 34, 4, 8], [16, 18, 6, 14, 17, 22], [13, 16, 11], [13, 23, 5, 10, 15, 39], [36, 34, 14]], ![[10, 13, 29, 8, 8, 37], [14, 32, 24, 21, 38, 5], [7, 21, 23], [19, 8, 1, 5], [42, 0, 25]], ![[42, 17, 9, 29, 24, 12], [39, 22, 37, 17, 14, 39], [21, 11, 1], [6, 26, 16, 35, 41, 2], [27, 17, 25]]]
 h' := ![![[30, 10, 39, 33], [5, 19, 5, 21], [34, 31, 18, 37], [11, 31, 41, 38], [0, 0, 1], [0, 1]], ![[5, 17, 42, 5], [13, 4, 10, 5], [23, 14, 10, 12], [26, 32, 3, 22], [41, 1, 5, 3], [30, 10, 39, 33]], ![[17, 15, 5, 5], [0, 25, 26, 39], [40, 4, 35, 42], [27, 41, 41, 25], [19, 0, 42], [5, 17, 42, 5]], ![[0, 1], [23, 38, 2, 21], [18, 37, 23, 38], [8, 25, 1, 1], [21, 42, 38, 40], [17, 15, 5, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [30, 33, 25], []]
 b := ![[], [], [19, 27, 3, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [37, 2, 0, 34, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2517939697657970, 46012983924768, 3919294146131580, 2957946480856320, 8334662706982728]
  a := ![619, 214, 629, 437, 1358]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5174836125369202, -6782957715359784, -102682989787236, -4583115313644864, 8334662706982728]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![145, 406, -118, -192, -580]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![145, 406, -118, -192, -580]] 
 ![![43, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![145, 406, -118, -192, -580], ![96, 757, -270, -438, -1336], ![528, 1608, -489, -794, -2404], ![528, 3108, -1062, -1725, -5252], ![-480, -1986, 644, 1046, 3177]]]
  hmulB := by decide  
  f := ![![![-869, -370, -502, -352, -1276]], ![![-726, -311, -414, -290, -1056]], ![![-1542, -660, -889, -622, -2260]], ![![3450, 1392, 2218, 1567, 5484]], ![![-1383, -564, -870, -614, -2163]]]
  g := ![![![31, 406, -118, -192, -580], ![234, 757, -270, -438, -1336], ![198, 1608, -489, -794, -2404], ![798, 3108, -1062, -1725, -5252], ![-387, -1986, 644, 1046, 3177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![869, 370, 502, 352, 1276]] ![![145, 406, -118, -192, -580]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-195065, -39368, -27922, -46036, -149396]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-195065, -39368, -27922, -46036, -149396]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![16, 35, 1, 0, 0], ![4, 13, 0, 1, 0], ![0, 2, 0, 0, 1]] where
  M :=![![![-195065, -39368, -27922, -46036, -149396], ![270912, 44635, 36112, 60614, 196112], ![-342480, -39360, -41119, -70980, -228588], ![375552, 11292, 36624, 67289, 214560], ![85200, 26148, 14574, 23070, 75395]]]
  hmulB := by decide  
  f := ![![![21689, 9304, 12938, 9012, 32356]], ![![-127680, -53227, -77008, -54158, -193904]], ![![-71648, -29711, -43303, -30506, -109164]], ![![-128228, -53685, -77224, -54233, -194240]], ![![20880, 8762, 12566, 8818, 31587]]]
  g := ![![![9273, 39046, -27922, -46036, -149396], ![-11688, -51053, 36112, 60614, 196112], ![12752, 59143, -41119, -70980, -228588], ![-10204, -54775, 36624, 67289, 214560], ![-5112, -19886, 14574, 23070, 75395]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [26, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 46], [0, 1]]
 g := ![![[43, 37], [10, 16], [31, 34], [10, 6], [1]], ![[37, 10], [29, 31], [42, 13], [23, 41], [1]]]
 h' := ![![[10, 46], [22, 15], [40, 4], [22, 9], [21, 10], [0, 1]], ![[0, 1], [31, 32], [33, 43], [18, 38], [27, 37], [10, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [21, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [26, 37, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![63056, 23438, 45625, 32403, 109512]
  a := ![41, 10, 42, 27, 90]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16948, -47100, 45625, 32403, 109512]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![385, 125, 68, 107, 350]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![385, 125, 68, 107, 350]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![18, 27, 1, 0, 0], ![31, 41, 0, 1, 0], ![8, 14, 0, 0, 1]] where
  M :=![![![385, 125, 68, 107, 350], ![-696, -197, -114, -182, -594], ![1152, 282, 179, 290, 944], ![-1776, -384, -260, -425, -1380], ![-24, -33, -12, -17, -57]]]
  hmulB := by decide  
  f := ![![![-25, -13, -14, -9, -32]], ![![120, 47, 66, 48, 178]], ![![42, 15, 21, 16, 62]], ![![175, 72, 92, 66, 250]], ![![8, 1, 6, 5, 17]]]
  g := ![![![-148, -234, 68, 107, 350], ![250, 397, -114, -182, -594], ![-396, -631, 179, 290, 944], ![577, 923, -260, -425, -1380], ![25, 38, -12, -17, -57]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [30, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 46], [0, 1]]
 g := ![![[39, 7], [40, 34], [22, 24], [13, 25], [1]], ![[27, 40], [22, 13], [1, 23], [44, 22], [1]]]
 h' := ![![[5, 46], [22, 30], [45, 9], [33, 27], [17, 5], [0, 1]], ![[0, 1], [31, 17], [43, 38], [27, 20], [42, 42], [5, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [42, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [30, 42, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5416545, 1441152, 5256090, 3857232, 11945874]
  a := ![453, 153, 463, 312, 994]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6475197, -9911958, 5256090, 3857232, 11945874]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-157, -7, -235, -182, -510]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-157, -7, -235, -182, -510]] 
 ![![47, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![-157, -7, -235, -182, -510], ![-864, 65, -1563, -1175, -3256], ![-6456, 240, -10822, -8217, -22850], ![-43224, 1986, -74051, -56072, -155786], ![14976, -663, 25562, 19365, 53811]]]
  hmulB := by decide  
  f := ![![![144637, 602411, -196351, -318786, -968460]], ![![104656, 435895, -142077, -230669, -700764]], ![![43190, 179878, -58628, -95187, -289174]], ![![52611, 219195, -71458, -116006, -352426]], ![![52058, 216799, -70660, -114723, -348523]]]
  g := ![![![325, -7, -235, -182, -510], ![2019, 65, -1563, -1175, -3256], ![14271, 240, -10822, -8217, -22850], ![97142, 1986, -74051, -56072, -155786], ![-33565, -663, 25562, 19365, 53811]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-195065, -39368, -27922, -46036, -149396]] ![![385, 125, 68, 107, 350]]
  ![![5479399, -1893741, -12394, 300673, 798726]] where
 M := ![![![5479399, -1893741, -12394, 300673, 798726]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![5479399, -1893741, -12394, 300673, 798726]] ![![-157, -7, -235, -182, -510]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-178626931, -96842278, -41716025, -62270911, -205669086]]]
 hmul := by decide  
 g := ![![![![-3800573, -2060474, -887575, -1324913, -4375938]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 5 2 5 [49, 47, 31, 50, 31, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 31, 15, 15, 20], [30, 4, 0, 11, 52], [22, 37, 2, 22, 6], [34, 33, 36, 5, 28], [0, 1]]
 g := ![![[37, 38, 36, 39, 15], [48, 17, 28, 37], [51, 6, 24, 38, 47], [22, 1], []], ![[19, 8, 31, 41, 25, 2, 31, 32], [25, 44, 11, 46], [52, 26, 20, 39, 40, 38, 35, 14], [31, 27, 32, 9], [9, 27, 4, 38, 14, 25, 20, 50]], ![[27, 51, 29, 22, 1, 29, 6, 38], [12, 47, 4, 16], [16, 52, 26, 15, 19, 19, 30, 46], [30, 51, 39, 49], [21, 16, 43, 43, 4, 35, 11, 52]], ![[37, 2, 14, 5, 8, 36, 42, 43], [46, 21, 7, 24], [44, 0, 47, 25, 51, 0, 51, 10], [42, 35, 12, 16], [41, 27, 16, 48, 37, 25, 26, 4]], ![[30, 24, 51, 9, 24, 44, 36, 6], [29, 3, 42, 42], [13, 43, 2, 11, 15, 15, 17, 17], [40, 50, 50, 37], [36, 7, 47, 50, 49, 32, 2, 10]]]
 h' := ![![[42, 31, 15, 15, 20], [44, 15, 29, 6, 42], [45, 18, 15, 6, 14], [35, 30, 13, 35, 10], [0, 0, 0, 1], [0, 1]], ![[30, 4, 0, 11, 52], [3, 12, 20, 51, 16], [50, 17, 20, 20, 24], [17, 10, 10, 43, 18], [30, 20, 25, 43, 3], [42, 31, 15, 15, 20]], ![[22, 37, 2, 22, 6], [47, 10, 16, 15, 42], [30, 40, 19, 36, 4], [15, 51, 46, 47, 31], [1, 19, 50, 28, 7], [30, 4, 0, 11, 52]], ![[34, 33, 36, 5, 28], [34, 10, 45, 18, 4], [50, 23, 10, 20, 36], [9, 21, 22, 38, 14], [0, 18, 46, 37, 4], [22, 37, 2, 22, 6]], ![[0, 1], [14, 6, 49, 16, 2], [2, 8, 42, 24, 28], [45, 47, 15, 49, 33], [16, 49, 38, 50, 39], [34, 33, 36, 5, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 9, 13, 19], [], [], []]
 b := ![[], [6, 15, 32, 15, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 5
  hpos := by decide
  P := [49, 47, 31, 50, 31, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![303143065253606261, 20599727590902690, 436047572992216921, 327893102023260457, 936015465930607590]
  a := ![247, 84, 250, 171, 542]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5719680476483137, 388674105488730, 8227312697966357, 6186662302325669, 17660669168502030]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 418195493 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2203, -889, -1344, -955, -3410]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-2203, -889, -1344, -955, -3410]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![13, 25, 42, 1, 0], ![25, 57, 15, 0, 1]] where
  M :=![![![-2203, -889, -1344, -955, -3410], ![13080, 5567, 7826, 5466, 19610], ![-77088, -32226, -46445, -32634, -116872], ![455280, 191544, 273548, 191807, 687428], ![-126456, -53307, -75920, -53199, -190701]]]
  hmulB := by decide  
  f := ![![![-5417, -1675, -930, -1471, -4808]], ![![9480, 2551, 1526, 2448, 7982]], ![![-15312, -3606, -2331, -3786, -12316]], ![![-7687, -1776, -1162, -1890, -6146]], ![![2981, 847, 491, 784, 2559]]]
  g := ![![![1618, 3684, 1524, -955, -3410], ![-9292, -21167, -8744, 5466, 19610], ![55406, 126192, 52157, -32634, -116872], ![-325829, -742153, -306674, 191807, 687428], ![90384, 205875, 85067, -53199, -190701]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [39, 20, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 11, 39], [2, 47, 20], [0, 1]]
 g := ![![[29, 50, 26], [6, 7, 20], [53, 46], [41, 44, 5], [1]], ![[16, 58, 48, 31], [0, 47, 30, 47], [27, 5], [14, 39, 42, 44], [54, 37, 28, 24]], ![[48, 51, 4, 36], [44, 15, 4, 4], [9, 26], [40, 19, 13, 46], [55, 45, 11, 35]]]
 h' := ![![[49, 11, 39], [2, 55, 12], [34, 4, 43], [53, 47, 39], [20, 39, 51], [0, 1]], ![[2, 47, 20], [16, 24, 54], [9, 32, 53], [0, 30, 8], [21, 10, 24], [49, 11, 39]], ![[0, 1], [13, 39, 52], [56, 23, 22], [17, 41, 12], [46, 10, 43], [2, 47, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 18], []]
 b := ![[], [33, 17, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [39, 20, 8, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7266595331, 548408232, 10322767503, 7757647950, 22192822125]
  a := ![232, 80, 235, 164, 509]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10989887816, -24718366977, -10989674208, 7757647950, 22192822125]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2441, -499, 4448, 3479, 9720]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![2441, -499, 4448, 3479, 9720]] 
 ![![59, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![2441, -499, 4448, 3479, 9720], ![17208, -1543, 29908, 22878, 63682], ![118848, -6858, 203865, 154896, 430624], ![817536, -39264, 1396198, 1058681, 2942368], ![-281856, 14439, -482026, -365751, -1016639]]]
  hmulB := by decide  
  f := ![![![-1824101, -688369, -346162, -536449, -1759782]], ![![-31557, -15694, -6994, -10533, -34732]], ![![-1654238, -613048, -310947, -482782, -1583200]], ![![-657957, -272613, -131320, -201544, -662302]], ![![-590197, -219350, -111106, -172454, -565563]]]
  g := ![![![-8425, -499, 4448, 3479, 9720], ![-55953, -1543, 29908, 22878, 63682], ![-379964, -6858, 203865, 154896, 430624], ![-2599389, -39264, 1396198, 1058681, 2942368], ![897755, 14439, -482026, -365751, -1016639]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49, 38, -12, -12, -4]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![49, 38, -12, -12, -4]] 
 ![![59, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![49, 38, -12, -12, -4], ![-768, -203, -746, -548, -1696], ![1248, 1344, -1199, -1010, -1784], ![-29904, -6936, -31354, -23155, -70380], ![9120, 1890, 10098, 7484, 22473]]]
  hmulB := by decide  
  f := ![![![-11413, -2770, -2000, -3204, -10404]], ![![-2386, -567, -430, -688, -2232]], ![![-8216, -1952, -1435, -2302, -7472]], ![![-5106, -1236, -942, -1503, -4876]], ![![-2674, -670, -454, -728, -2367]]]
  g := ![![![7, 38, -12, -12, -4], ![1222, -203, -746, -548, -1696], ![1452, 1344, -1199, -1010, -1784], ![50870, -6936, -31354, -23155, -70380], ![-16278, 1890, 10098, 7484, 22473]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-2203, -889, -1344, -955, -3410]] ![![2441, -499, 4448, 3479, 9720]]
  ![![-25067, -51694, -42146, -12448, -7564]] where
 M := ![![![-25067, -51694, -42146, -12448, -7564]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-25067, -51694, -42146, -12448, -7564]] ![![49, 38, -12, -12, -4]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![289135813, 24940480, 403310902, 302821040, 869066224]]]
 hmul := by decide  
 g := ![![![![4900607, 422720, 6835778, 5132560, 14729936]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![624493, 127533, 89789, 147878, 479982]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![624493, 127533, 89789, 147878, 479982]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![5, 18, 57, 1, 0], ![60, 10, 50, 0, 1]] where
  M :=![![![624493, 127533, 89789, 147878, 479982], ![-872352, -146273, -116959, -196023, -634376], ![1111368, 132480, 134696, 231907, 747166], ![-1234680, -47358, -123127, -224610, -716994], ![-268272, -83211, -46122, -72931, -238391]]]
  hmulB := by decide  
  f := ![![![-11735, -4875, -7081, -4986, -17852]], ![![69456, 29269, 41743, 29251, 104812]], ![![-409416, -171828, -246084, -172699, -618942]], ![![-323359, -135663, -194328, -136397, -488880]], ![![-346764, -145469, -208464, -146319, -524373]]]
  g := ![![![-473997, -120231, -530137, 147878, 479982], ![625743, 159441, 701232, -196023, -634376], ![-735707, -188746, -826923, 231907, 747166], ![703410, 183042, 795563, -224610, -716994], ![236063, 59237, 262795, -72931, -238391]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [59, 15, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 43, 9], [54, 17, 52], [0, 1]]
 g := ![![[53, 27, 36], [4, 16], [28, 4, 12], [30, 52, 41], [1]], ![[20, 16, 20, 22], [27, 48], [58, 42], [7, 57, 56, 3], [55, 37, 26, 58]], ![[25, 13, 19, 25], [49, 52], [20, 9, 9, 14], [34, 9], [47, 54, 36, 3]]]
 h' := ![![[45, 43, 9], [33, 56, 6], [56, 16, 4], [60, 24, 16], [2, 46, 38], [0, 1]], ![[54, 17, 52], [49, 48, 57], [42, 50, 29], [34, 5], [40, 4, 23], [45, 43, 9]], ![[0, 1], [15, 18, 59], [51, 56, 28], [15, 32, 45], [56, 11], [54, 17, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 22], []]
 b := ![[], [35, 53, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [59, 15, 23, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31250817310, -7708791188, -31673030242, -23336065955, -71491416224]
  a := ![-359, -113, -376, -246, -788]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![71719909605, 18479582922, 79886123613, -23336065955, -71491416224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11735, 4875, 7081, 4986, 17852]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![11735, 4875, 7081, 4986, 17852]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![14, 4, 1, 0, 0], ![5, 59, 0, 1, 0], ![42, 55, 0, 0, 1]] where
  M :=![![![11735, 4875, 7081, 4986, 17852], ![-69456, -29269, -41743, -29251, -104812], ![409416, 171828, 246084, 172699, 618942], ![-2420280, -1016286, -1456811, -1022038, -3660658], ![672264, 282399, 404674, 283859, 1016653]]]
  hmulB := by decide  
  f := ![![![-624493, -127533, -89789, -147878, -479982]], ![![872352, 146273, 116959, 196023, 634376]], ![![-104342, -21850, -15146, -24887, -80810]], ![![812803, 131800, 107783, 181157, 585988]], ![![360966, 45440, 44389, 76120, 245407]]]
  g := ![![![-14133, -21303, 7081, 4986, 17852], ![83005, 125052, -41743, -29251, -104812], ![-490079, -738419, 246084, 172699, 618942], ![2898900, 4367990, -1456811, -1022038, -3660658], ![-805113, -1213113, 404674, 283859, 1016653]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [26, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 60], [0, 1]]
 g := ![![[56, 60], [19], [59, 27], [14, 41], [8, 1]], ![[48, 1], [19], [31, 34], [37, 20], [16, 60]]]
 h' := ![![[8, 60], [14, 11], [52, 18], [2, 37], [36, 38], [0, 1]], ![[0, 1], [41, 50], [13, 43], [54, 24], [35, 23], [8, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [12, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [26, 53, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1232630, 283094, 1300155, 960631, 2915872]
  a := ![-221, -70, -227, -154, -485]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2364579, -3638815, 1300155, 960631, 2915872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![624493, 127533, 89789, 147878, 479982]] ![![11735, 4875, 7081, 4986, 17852]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)


lemma PB2088I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB2088I1 : PrimesBelowBoundCertificateInterval O 23 61 2088 where
  m := 9
  g := ![2, 2, 1, 1, 2, 3, 1, 3, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB2088I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![24389, 841]
    · exact ![29791, 961]
    · exact ![69343957]
    · exact ![115856201]
    · exact ![3418801, 43]
    · exact ![2209, 2209, 47]
    · exact ![418195493]
    · exact ![205379, 59, 59]
    · exact ![226981, 3721]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I29N1, I31N1, I43N1, I47N2, I59N1, I59N2]
  Il := ![[I29N1], [I31N1], [], [], [I43N1], [I47N2], [], [I59N1, I59N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
