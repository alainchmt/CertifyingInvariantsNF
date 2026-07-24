
import IdealArithmetic.Examples.NF5_1_48600000_1.RI5_1_48600000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![-9, -36, 15, 14, 29]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0], ![-9, -36, 15, 14, 29]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![18, 14, 28, 1, 0], ![1, 6, 26, 0, 1]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![-9, -36, 15, 14, 29], ![172, -16, 28, -16, -4], ![-126, 84, -66, -4, -54], ![-358, -12, -2, 76, 130], ![318, -27, 75, -55, -55]]]
  hmulB := by decide  
  f := ![![![12223, -1800, 2286, -900, 234], ![-522, -2088, 0, 0, 0]], ![![-3051, 469, -579, 218, -73], ![145, 522, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![6111, -902, 1145, -449, 119], ![-263, -1044, 0, 0, 0]], ![![-202, 66, -53, 2, -32], ![37, 36, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-18, -14, -28, 29, 0], ![-1, -6, -26, 0, 29]], ![![-10, -14, -39, 14, 29], ![16, 8, 20, -16, -4], ![0, 16, 50, -4, -54], ![-64, -64, -190, 76, 130], ![47, 37, 105, -55, -55]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [23, 15, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 4, 23], [15, 24, 6], [0, 1]]
 g := ![![[5, 19, 22], [16, 28], [0, 20, 24], [1]], ![[12, 8, 2, 7], [25, 13], [26, 0, 9, 9], [10, 3, 21, 16]], ![[10, 5, 19, 5], [17, 4], [28, 2, 24, 25], [21, 14, 16, 13]]]
 h' := ![![[1, 4, 23], [9, 15, 15], [0, 11, 12], [6, 14, 16], [0, 1]], ![[15, 24, 6], [28, 11, 9], [20, 28, 19], [3, 25, 10], [1, 4, 23]], ![[0, 1], [24, 3, 5], [26, 19, 27], [21, 19, 3], [15, 24, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 2], []]
 b := ![[], [4, 7, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [23, 15, 13, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4973300, -6181279, -648442, 967448, 6059896]
  a := ![-31, -5, -24, -32, -62]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-980940, -1933963, -6389458, 967448, 6059896]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![-7, 6, 1, 1, 2]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0], ![-7, 6, 1, 1, 2]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![18, 1, 1, 0, 0], ![11, 18, 0, 1, 0], ![11, 8, 0, 0, 1]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![-7, 6, 1, 1, 2], ![12, 1, 19, -1, 0], ![-8, 6, -19, 8, -4], ![8, 0, 16, 33, 76], ![56, 6, 31, -29, -43]]]
  hmulB := by decide  
  f := ![![![-820728, -98286, -1355021, 66751, -9298], ![132733, 2060160, -1044, 0, 0]], ![![-113, -15, -191, 9, -2], ![29, 290, 0, 0, 0]], ![![-502325, -60153, -829333, 40855, -5690], ![81227, 1260910, -639, 0, 0]], ![![-311381, -37290, -514092, 25325, -3528], ![50364, 781620, -396, 0, 0]], ![![-311343, -37284, -514026, 25322, -3527], ![50350, 781520, -396, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-18, -1, 29, 0, 0], ![-11, -18, 0, 29, 0], ![-11, -8, 0, 0, 29]], ![![-2, -1, 1, 1, 2], ![-11, 0, 19, -1, 0], ![10, -3, -19, 8, -4], ![-51, -42, 16, 33, 76], ![10, 29, 31, -29, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [24, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 28], [0, 1]]
 g := ![![[19, 23], [25], [21, 5], [8, 1]], ![[0, 6], [25], [3, 24], [16, 28]]]
 h' := ![![[8, 28], [14, 20], [18, 24], [11, 11], [0, 1]], ![[0, 1], [0, 9], [7, 5], [12, 18], [8, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [7, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [24, 21, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26060, 2229, 16730, -1908, 3035]
  a := ![-23, -4, -18, -24, -47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9913, -153, 16730, -1908, 3035]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0, 0, 0], ![-9, -36, 15, 14, 29]] ![![29, 0, 0, 0, 0], ![-7, 6, 1, 1, 2]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![841, 0, 0, 0, 0], ![-203, 174, 29, 29, 58]], ![![-261, -1044, 435, 406, 841], ![1247, 174, 145, -232, -261]]]
 hmul := by decide  
 g := ![![![![29, 0, 0, 0, 0]], ![![-7, 6, 1, 1, 2]]], ![![![-9, -36, 15, 14, 29]], ![![43, 6, 5, -8, -9]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -1, 1, -1, -1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![9, -1, 1, -1, -1]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![19, 5, 1, 0, 0], ![15, 10, 0, 1, 0], ![26, 27, 0, 0, 1]] where
  M :=![![![9, -1, 1, -1, -1], ![-8, 7, -8, 0, -4], ![-4, -6, 9, 2, 10], ![44, -6, 22, -11, -14], ![-38, 8, -26, 8, 1]]]
  hmulB := by decide  
  f := ![![![37, 23, 27, 11, 13]], ![![96, 73, 80, 32, 36]], ![![41, 28, 32, 13, 15]], ![![61, 43, 49, 20, 23]], ![![112, 81, 90, 36, 41]]]
  g := ![![![1, 1, 1, -1, -1], ![8, 5, -8, 0, -4], ![-15, -11, 9, 2, 10], ![5, 12, 22, -11, -14], ![10, 1, -26, 8, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [7, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 30], [0, 1]]
 g := ![![[27, 9], [19, 28], [10, 4], [28, 1]], ![[0, 22], [28, 3], [29, 27], [25, 30]]]
 h' := ![![[28, 30], [22, 28], [23, 11], [21, 2], [0, 1]], ![[0, 1], [0, 3], [21, 20], [15, 29], [28, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [23, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [7, 3, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![759295, 72867, 478581, -51789, 87217]
  a := ![125, 23, 99, 124, 249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-316921, -134097, 478581, -51789, 87217]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![3, 1, 0, 0, 0], ![0, 4, 2, 0, 0], ![0, 0, 2, 1, 0], ![4, 0, 2, 7, 8], ![4, 1, 3, -3, -1]]]
  hmulB := by decide  
  f := ![![![6282, 1971, 15144, 7750, 208], ![-63829, 682, -234608, -806, 0]], ![![958, 298, 2336, 1196, 32], ![-9733, 124, -36208, -124, 0]], ![![5312, 1663, 12805, 6554, 176], ![-53973, 605, -198400, -682, 0]], ![![2416, 756, 5824, 2981, 80], ![-24548, 278, -90240, -310, 0]], ![![1416, 441, 3418, 1750, 47], ![-14387, 179, -52976, -182, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 31, 0, 0, 0], ![-25, 0, 31, 0, 0], ![-12, 0, 0, 31, 0], ![-7, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![-2, 4, 2, 0, 0], ![-2, 0, 2, 1, 0], ![-6, 0, 2, 7, 8], ![-1, 1, 3, -3, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![7, 1, 0, 0, 0], ![0, 8, 2, 0, 0], ![0, 0, 6, 1, 0], ![4, 0, 2, 11, 8], ![4, 1, 3, -3, 3]]]
  hmulB := by decide  
  f := ![![![46522, -142161, -38010, 887, 768], ![-204321, 576414, 5239, -2976, 0]], ![![11611, -35539, -9506, 221, 192], ![-50994, 144088, 1333, -744, 0]], ![![7744, -23675, -6335, 147, 128], ![-34011, 95992, 899, -496, 0]], ![![19370, -59247, -15844, 369, 320], ![-85071, 240216, 2202, -1240, 0]], ![![13503, -41272, -11038, 257, 223], ![-59304, 167342, 1537, -864, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-7, 31, 0, 0, 0], ![-3, 0, 31, 0, 0], ![-13, 0, 0, 31, 0], ![-9, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![-2, 8, 2, 0, 0], ![-1, 0, 6, 1, 0], ![-7, 0, 2, 11, 8], ![0, 1, 3, -3, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2

def I31N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4243, -3033, -3555, -1477, -1695]] i)))

def SI31N3: IdealEqSpanCertificate' Table ![![-4243, -3033, -3555, -1477, -1695]] 
 ![![31, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-4243, -3033, -3555, -1477, -1695], ![-12688, -8971, -10550, -4378, -5036], ![-12484, -8862, -10353, -4288, -4922], ![-49324, -35130, -41066, -17027, -19538], ![11622, 8298, 9666, 4004, 4589]]]
  hmulB := by decide  
  f := ![![![-2015, -1833, 523, 1467, 4051]], ![![-68, -703, 554, 382, 1424]], ![![-1991, -603, -494, 823, 1577]], ![![-3461, -2073, -1, 1962, 4799]], ![![2261, -267, 1357, -441, 120]]]
  g := ![![![4250, -3033, -3555, -1477, -1695], ![12596, -8971, -10550, -4378, -5036], ![12371, -8862, -10353, -4288, -4922], ![49085, -35130, -41066, -17027, -19538], ![-11559, 8298, 9666, 4004, 4589]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N3 : Nat.card (O ⧸ I31N3) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N3)

lemma isPrimeI31N3 : Ideal.IsPrime I31N3 := prime_ideal_of_norm_prime hp31.out _ NI31N3
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![9, -1, 1, -1, -1]] ![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0]]
  ![![31, 0, 0, 0, 0], ![19, 27, -13, -14, -27]] where
 M := ![![![279, -31, 31, -31, -31], ![19, 4, -5, -3, -7]]]
 hmul := by decide  
 g := ![![![![201105, -49463, 67509, -3417, 29511], ![27776, 41230, 0, 0, 0]], ![![13481, -3325, 4531, -225, 1987], ![1872, 2765, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![31, 0, 0, 0, 0], ![19, 27, -13, -14, -27]] ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0]]
  ![![2015, 1833, -523, -1467, -4051]] where
 M := ![![![961, 0, 0, 0, 0], ![217, 31, 0, 0, 0]], ![![589, 837, -403, -434, -837], ![-31, 208, -133, -86, -193]]]
 hmul := by decide  
 g := ![![![![131533, 94023, 110205, 45787, 52545]], ![![42389, 30202, 35435, 14717, 16901]]], ![![![-115841, -83136, -96136, -39745, -45438]], ![![-37149, -26657, -30932, -12807, -14654]]]]
 hle2 := by decide  

def MulI31N2 : IdealMulLeCertificate' Table 
  ![![2015, 1833, -523, -1467, -4051]] ![![-4243, -3033, -3555, -1477, -1695]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2, I31N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
    exact isPrimeI31N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1 ⊙ MulI31N2)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![13, 20, -12, -13, -25]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0], ![13, 20, -12, -13, -25]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![13, 17, 5, 1, 0], ![9, 17, 26, 0, 1]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![13, 20, -12, -13, -25], ![-152, 8, -49, 11, -4], ![90, -78, 62, -2, 54], ![298, -12, 2, -110, -178], ![-322, 29, -108, 74, 67]]]
  hmulB := by decide  
  f := ![![![57032, -6580, 21186, -2041, 5885], ![6401, 14430, 0, 0, 0]], ![![-1911, 205, -697, 78, -177], ![-185, -481, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![19162, -2215, 7122, -683, 1983], ![2159, 4849, 0, 0, 0]], ![![12989, -1515, 4839, -455, 1361], ![1488, 3289, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-13, -17, -5, 37, 0], ![-9, -17, -26, 0, 37]], ![![11, 18, 19, -13, -25], ![-7, -3, 0, 11, -4], ![-10, -26, -36, -2, 54], ![90, 132, 140, -110, -178], ![-51, -64, -60, 74, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [27, 27, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 26], [10, 10], [0, 1]]
 g := ![![[11, 32, 11], [9, 30], [29, 7, 30], [9, 1], []], ![[27, 1, 36], [16, 3], [15, 28, 4], [8, 26], []], ![[25, 4, 27], [13, 4], [28, 2, 3], [19, 10], []]]
 h' := ![![[36, 26], [15, 28, 14], [31, 24, 20], [16, 26, 17], [0, 0, 1], [0, 1]], ![[10, 10], [1, 0, 29], [27, 28, 15], [7, 14, 22], [1, 22, 10], [36, 26]], ![[0, 1], [30, 9, 31], [14, 22, 2], [15, 34, 35], [26, 15, 26], [10, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24], []]
 b := ![[], [18, 25, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [27, 27, 28, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![435381, -5225187, 2738262, 659048, 6387029]
  a := ![-30, -3, -22, -28, -59]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1773392, -3378608, -4503236, 659048, 6387029]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![7, 5, 1, 1, 2]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0], ![7, 5, 1, 1, 2]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![1, 35, 1, 0, 0], ![5, 26, 0, 1, 0], ![19, 9, 0, 0, 1]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![7, 5, 1, 1, 2], ![12, 14, 17, -1, 0], ![-8, 6, -4, 7, -4], ![4, 0, 14, 43, 68], ![52, 5, 28, -26, -25]]]
  hmulB := by decide  
  f := ![![![-202739, -242520, -305802, 20562, 4056], ![-78588, 669774, -1776, 0, 0]], ![![-2235327, -2673970, -3371732, 226714, 44742], ![-866799, 7384867, -19536, 0, 0]], ![![-2118149, -2533797, -3194980, 214829, 42396], ![-821350, 6997739, -18512, 0, 0]], ![![-1598169, -1911780, -2410650, 162091, 31988], ![-619714, 5279876, -13968, 0, 0]], ![![-647834, -774960, -977184, 65706, 12967], ![-251217, 2140257, -5664, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-1, -35, 37, 0, 0], ![-5, -26, 0, 37, 0], ![-19, -9, 0, 0, 37]], ![![-1, -2, 1, 1, 2], ![0, -15, 17, -1, 0], ![1, 0, -4, 7, -4], ![-41, -60, 14, 43, 68], ![17, -2, 28, -26, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [17, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 36], [0, 1]]
 g := ![![[22, 4], [4], [27, 4], [16], [1]], ![[6, 33], [4], [11, 33], [16], [1]]]
 h' := ![![[33, 36], [9, 35], [22, 2], [17, 35], [20, 33], [0, 1]], ![[0, 1], [17, 2], [14, 35], [25, 2], [36, 4], [33, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [20, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [17, 4, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1881, 3252, 4432, 4316, 6128]
  a := ![-12, -6, -8, -22, -24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3799, -8628, 4432, 4316, 6128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0, 0, 0], ![13, 20, -12, -13, -25]] ![![37, 0, 0, 0, 0], ![7, 5, 1, 1, 2]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![1369, 0, 0, 0, 0], ![259, 185, 37, 37, 74]], ![![481, 740, -444, -481, -925], ![-925, 148, -481, 0, -185]]]
 hmul := by decide  
 g := ![![![![37, 0, 0, 0, 0]], ![![7, 5, 1, 1, 2]]], ![![![13, 20, -12, -13, -25]], ![![-25, 4, -13, 0, -5]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![50, -10, 4, -8, -5]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0], ![50, -10, 4, -8, -5]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![31, 2, 32, 18, 1]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![50, -10, 4, -8, -5], ![-52, 35, -55, -13, -44], ![-88, -48, 11, 19, 58], ![220, -126, 116, -68, -22], ![-158, 89, -134, 22, -58]]]
  hmulB := by decide  
  f := ![![![-49, 10, -4, 8, 5], ![41, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![-9, 2, 0, 2, 1], ![8, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-31, -2, -32, -18, 41]], ![![5, 0, 4, 2, -5], ![32, 3, 33, 19, -44], ![-46, -4, -45, -25, 58], ![22, -2, 20, 8, -22], ![40, 5, 42, 26, -58]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [5, 28, 7, 9, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 34, 25, 12], [3, 39, 29, 38], [39, 8, 28, 32], [0, 1]]
 g := ![![[2, 22, 19, 5], [27, 24, 4], [38, 12, 23], [32, 1], []], ![[33, 37, 30, 23, 35, 19], [31, 29, 21], [32, 38, 16], [32, 0, 31, 28, 31, 12], [14, 1, 21]], ![[12, 39, 30, 1, 6, 38], [21, 6, 18], [20, 22, 20], [38, 24, 27, 11, 24, 14], [10, 32, 9]], ![[31, 8, 13, 17, 40, 32], [6, 16, 2], [9, 25, 32], [34, 18, 7, 33, 11, 5], [18, 38, 40]]]
 h' := ![![[31, 34, 25, 12], [6, 1, 7, 28], [31, 32, 15, 2], [4, 1, 35, 33], [0, 0, 1], [0, 1]], ![[3, 39, 29, 38], [4, 15, 18, 13], [6, 31, 33, 12], [24, 19, 8, 37], [30, 30, 15, 1], [31, 34, 25, 12]], ![[39, 8, 28, 32], [22, 8, 19, 40], [2, 13, 33, 10], [15, 5, 37, 26], [0, 40, 28, 38], [3, 39, 29, 38]], ![[0, 1], [36, 17, 38, 1], [5, 6, 1, 17], [3, 16, 2, 27], [37, 12, 38, 2], [39, 8, 28, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [21, 32, 24], []]
 b := ![[], [], [20, 3, 37, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [5, 28, 7, 9, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1215540358, 878994836, 913277625, 322011866, 265225811]
  a := ![25, 10, 19, 26, 37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-170889263, 8501054, -184730447, -108586652, 265225811]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![-17, 1, 0, 0, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0], ![-17, 1, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![-17, 1, 0, 0, 0], ![0, -16, 2, 0, 0], ![0, 0, -18, 1, 0], ![4, 0, 2, -13, 8], ![4, 1, 3, -3, -21]]]
  hmulB := by decide  
  f := ![![![3409833, -10529608, 1513506, -22561, 6336], ![8216072, -26468616, 502865, -32472, 0]], ![![2131095, -6580858, 945930, -14101, 3960], ![5134923, -16542516, 314306, -20295, 0]], ![![2415279, -7458399, 1072063, -15981, 4488], ![5819671, -18748418, 356208, -23001, 0]], ![![994566, -3071134, 441452, -6581, 1848], ![2396430, -7720004, 146699, -9471, 0]], ![![1081179, -3338646, 479900, -7154, 2009], ![2605126, -8392460, 159466, -10296, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-24, 41, 0, 0, 0], ![-28, 0, 41, 0, 0], ![-12, 0, 0, 41, 0], ![-13, 0, 0, 0, 41]], ![![-1, 1, 0, 0, 0], ![8, -16, 2, 0, 0], ![12, 0, -18, 1, 0], ![0, 0, 2, -13, 8], ![5, 1, 3, -3, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0, 0, 0], ![50, -10, 4, -8, -5]] ![![41, 0, 0, 0, 0], ![-17, 1, 0, 0, 0]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![1681, 0, 0, 0, 0], ![-697, 41, 0, 0, 0]], ![![2050, -410, 164, -328, -205], ![-902, 205, -123, 123, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0, 0, 0]], ![![-17, 1, 0, 0, 0]]], ![![![50, -10, 4, -8, -5]], ![![-22, 5, -3, 3, 1]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [31, 32, 16, 35, 34, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 24, 12, 42, 31], [20, 16, 17, 33, 6], [33, 23, 41, 19, 8], [20, 22, 16, 35, 41], [0, 1]]
 g := ![![[9, 27, 33, 3, 31], [38, 13, 27, 6, 9], [7, 25, 13, 38], [1], []], ![[3, 24, 18, 3, 4, 13, 33, 17], [3, 25, 13, 26, 4, 36, 33, 41], [8, 10, 1, 23], [3, 11, 21, 26, 30, 6, 39, 4], [26, 17, 30, 15]], ![[22, 31, 1, 22, 5, 1, 34, 36], [36, 18, 12, 24, 9, 39, 18, 24], [36, 27, 41, 23], [24, 2, 11, 1, 6, 21, 37, 14], [13, 20, 32, 36]], ![[19, 32, 14, 11, 26, 7, 3, 34], [18, 20, 29, 9, 5, 40, 35, 37], [35, 15, 4, 36], [28, 41, 14, 24, 14, 8, 32, 30], [17, 32, 20, 21]], ![[28, 0, 11, 19, 40, 24, 25, 6], [40, 40, 42, 18, 13, 4, 20, 4], [0, 29, 22, 10], [36, 42, 22, 10, 12, 16, 27, 41], [41, 42, 25, 4]]]
 h' := ![![[22, 24, 12, 42, 31], [26, 12, 13, 2, 17], [13, 39, 13, 9, 3], [12, 11, 27, 8, 9], [0, 0, 1], [0, 1]], ![[20, 16, 17, 33, 6], [21, 20, 18, 4, 34], [23, 42, 30, 23, 37], [20, 41, 18, 32, 25], [22, 41, 31, 32, 10], [22, 24, 12, 42, 31]], ![[33, 23, 41, 19, 8], [5, 3, 41, 14, 36], [27, 5, 18, 40, 2], [38, 7, 33, 36, 18], [40, 34, 42, 24, 26], [20, 16, 17, 33, 6]], ![[20, 22, 16, 35, 41], [9, 14, 22, 5, 12], [5, 13, 34, 35, 28], [31, 23, 42, 2, 6], [3, 25, 29, 11, 6], [33, 23, 41, 19, 8]], ![[0, 1], [3, 37, 35, 18, 30], [24, 30, 34, 22, 16], [14, 4, 9, 8, 28], [32, 29, 26, 19, 1], [20, 22, 16, 35, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 41, 14, 21], [], [], []]
 b := ![[], [18, 13, 29, 22, 34], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [31, 32, 16, 35, 34, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-708328121, -200560170, -1273807920, -853039676, -1823128448]
  a := ![-9, -3, -7, -10, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16472747, -4664190, -29623440, -19838132, -42398336]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 147008443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![-13, -41, 16, 15, 31]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![-13, -41, 16, 15, 31]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![4, 21, 29, 1, 0], ![31, 34, 35, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![-13, -41, 16, 15, 31], ![184, -23, 25, -17, -4], ![-134, 90, -71, -7, -58], ![-394, -12, -8, 68, 118], ![330, -32, 73, -51, -51]]]
  hmulB := by decide  
  f := ![![![25293, -4696, 4076, -1840, 556], ![-1692, -6580, 0, 0, 0]], ![![-1801, 354, -298, 125, -53], ![141, 470, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![1349, -238, 213, -102, 21], ![-77, -350, 0, 0, 0]], ![![15377, -2850, 2477, -1120, 335], ![-1024, -4000, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-4, -21, -29, 47, 0], ![-31, -34, -35, 0, 47]], ![![-22, -30, -32, 15, 31], ![8, 10, 14, -17, -4], ![36, 47, 46, -7, -58], ![-92, -116, -130, 68, 118], ![45, 59, 71, -51, -51]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [30, 35, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 17, 22], [24, 29, 25], [0, 1]]
 g := ![![[3, 31, 36], [4, 37, 8], [12, 13, 28], [44, 28, 1], []], ![[38, 22, 23, 11], [46, 17, 9, 35], [31, 27, 3, 10], [1, 16, 38, 31], [12, 14]], ![[26, 29, 2, 27], [26, 35, 24, 1], [13, 28, 23, 8], [41, 26, 23, 34], [9, 14]]]
 h' := ![![[4, 17, 22], [21, 40, 6], [16, 5, 33], [43, 17, 34], [0, 0, 1], [0, 1]], ![[24, 29, 25], [44, 28, 20], [11, 24, 33], [24, 41, 44], [32, 1, 29], [4, 17, 22]], ![[0, 1], [44, 26, 21], [35, 18, 28], [45, 36, 16], [24, 46, 17], [24, 29, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 25], []]
 b := ![[], [9, 8, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [30, 35, 19, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-753834, 10198830, -4237685, -170389, -10115223]
  a := ![38, 6, 32, 34, 73]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6670205, 7610523, 7547583, -170389, -10115223]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![-11, 10, 1, 1, 2]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![-11, 10, 1, 1, 2]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![41, 33, 1, 0, 0], ![14, 44, 0, 1, 0], ![14, 37, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![-11, 10, 1, 1, 2], ![12, 1, 27, -1, 0], ![-8, 6, -27, 12, -4], ![24, 0, 24, 45, 108], ![72, 10, 43, -41, -63]]]
  hmulB := by decide  
  f := ![![![-4505706, -542261, -10534366, 375624, -31214], ![721685, 18304949, -5922, 0, 0]], ![![-1503504, -180948, -3515205, 125341, -10416], ![240828, 6108167, -1974, 0, 0]], ![![-4970167, -598161, -11620284, 414344, -34432], ![796090, 20191886, -6531, 0, 0]], ![![-2749655, -330928, -6428727, 229228, -19050], ![440451, 11170822, -3612, 0, 0]], ![![-2525727, -303980, -5905186, 210560, -17499], ![404591, 10261095, -3318, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-41, -33, 47, 0, 0], ![-14, -44, 0, 47, 0], ![-14, -37, 0, 0, 47]], ![![-2, -3, 1, 1, 2], ![-23, -18, 27, -1, 0], ![21, 11, -27, 12, -4], ![-66, -144, 24, 45, 108], ![-5, 58, 43, -41, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [28, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 46], [0, 1]]
 g := ![![[21, 42], [45, 8], [44, 8], [22, 12], [1]], ![[0, 5], [41, 39], [40, 39], [16, 35], [1]]]
 h' := ![![[23, 46], [9, 18], [37, 14], [42, 14], [19, 23], [0, 1]], ![[0, 1], [0, 29], [30, 33], [35, 33], [31, 24], [23, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [4, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [28, 24, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25485, 2082, 15860, -1517, 3578]
  a := ![23, 3, 17, 22, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13907, -12488, 15860, -1517, 3578]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0, 0, 0], ![-13, -41, 16, 15, 31]] ![![47, 0, 0, 0, 0], ![-11, 10, 1, 1, 2]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![2209, 0, 0, 0, 0], ![-517, 470, 47, 47, 94]], ![![-611, -1927, 752, 705, 1457], ![2115, 235, 141, -376, -423]]]
 hmul := by decide  
 g := ![![![![47, 0, 0, 0, 0]], ![![-11, 10, 1, 1, 2]]], ![![![-13, -41, 16, 15, 31]], ![![45, 5, 3, -8, -9]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
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


def P53P0 : CertificateIrreducibleZModOfList' 53 5 2 5 [46, 29, 40, 12, 50, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 18, 34, 20, 51], [25, 30, 51, 34, 36], [4, 16, 27, 40, 32], [52, 41, 47, 12, 40], [0, 1]]
 g := ![![[4, 51, 15, 45, 15], [19, 33, 0, 46], [38, 36, 8, 6, 9], [3, 1], []], ![[25, 27, 52, 37, 24, 12, 51, 48], [11, 22, 51, 25], [50, 29, 2, 45, 13, 28, 43, 41], [23, 20, 12, 9], [2, 16, 51, 18, 29, 24, 4, 45]], ![[39, 14, 9, 13, 19, 10], [7, 17, 50, 29], [17, 21, 49, 21, 41, 39, 35, 49], [41, 21, 51, 36], [23, 19, 37, 0, 37, 30, 5, 16]], ![[9, 9, 39, 3, 9, 49, 20, 41], [46, 32, 22, 28], [49, 51, 36, 13, 32, 42, 44, 48], [14, 6, 9, 28], [41, 29, 5, 4, 40, 41, 15, 14]], ![[7, 24, 23, 11, 45, 49, 47, 52], [23, 34, 11, 11], [29, 33, 35, 21, 24, 51, 7, 49], [12, 25, 14, 6], [25, 41, 36, 34, 43, 20, 23, 29]]]
 h' := ![![[28, 18, 34, 20, 51], [28, 28, 22, 0, 11], [1, 15, 15, 17, 24], [21, 26, 10, 30, 50], [0, 0, 0, 1], [0, 1]], ![[25, 30, 51, 34, 36], [18, 34, 25, 21, 20], [43, 51, 0, 13, 48], [48, 0, 6, 44, 18], [24, 43, 43, 24, 3], [28, 18, 34, 20, 51]], ![[4, 16, 27, 40, 32], [12, 4, 3, 42], [49, 42, 48, 42, 33], [33, 22, 5, 9, 43], [45, 13, 51, 35, 6], [25, 30, 51, 34, 36]], ![[52, 41, 47, 12, 40], [14, 3, 5, 18, 29], [40, 0, 44, 26, 9], [21, 35, 24, 38, 9], [33, 47, 14, 40, 9], [4, 16, 27, 40, 32]], ![[0, 1], [46, 37, 51, 25, 46], [16, 51, 52, 8, 45], [44, 23, 8, 38, 39], [15, 3, 51, 6, 35], [52, 41, 47, 12, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 25, 38, 26], [], [], []]
 b := ![[], [31, 46, 28, 4, 13], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 5
  hpos := by decide
  P := [46, 29, 40, 12, 50, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6869914378, 12702000246, 9320504952, 8957725464, 9036095292]
  a := ![14, 4, 10, 15, 24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![129621026, 239660382, 175858584, 169013688, 170492364]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [48, 19, 57, 52, 37, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 55, 47, 54, 13], [43, 47, 8, 58, 49], [54, 30, 41, 37, 1], [10, 44, 22, 28, 55], [0, 1]]
 g := ![![[3, 14, 6, 36, 19], [35, 22, 47, 17, 19], [10, 24, 45, 20], [19, 22, 1], []], ![[0, 17, 5, 17, 10, 43, 52, 24], [40, 53, 39, 2, 58, 41, 11, 23], [52, 25, 38, 25], [40, 31, 14, 56, 52, 57, 26, 24], [39, 29, 19, 22, 37, 39, 15, 14]], ![[16, 0, 19, 36, 38, 33, 51, 17], [47, 39, 5, 37, 58, 7, 43, 35], [30, 25, 12, 36], [9, 9, 48, 45, 48, 14, 38, 49], [8, 57, 23, 15, 24, 16, 2, 3]], ![[47, 27, 55, 29, 58, 24, 31, 15], [0, 38, 36, 3, 34, 32, 28, 28], [54, 44, 24, 57], [44, 12, 3, 18, 43, 37, 45, 36], [5, 28, 16, 1, 5, 24, 15, 1]], ![[13, 56, 41, 34, 6, 26, 41, 8], [31, 53, 18, 7, 18, 36, 34, 55], [7, 54, 8, 5], [29, 28, 33, 31, 43, 28, 5, 6], [44, 8, 23, 14, 9, 58, 54, 54]]]
 h' := ![![[33, 55, 47, 54, 13], [31, 41, 16, 1, 45], [13, 10, 44, 8, 45], [32, 58, 44, 40, 43], [0, 0, 0, 1], [0, 1]], ![[43, 47, 8, 58, 49], [20, 2, 14, 32, 16], [23, 52, 22, 1, 41], [10, 53, 53, 4, 54], [22, 21, 53, 43, 16], [33, 55, 47, 54, 13]], ![[54, 30, 41, 37, 1], [30, 49, 16, 9, 4], [22, 2, 54, 13, 12], [20, 3, 20, 53, 6], [4, 50, 11, 10, 58], [43, 47, 8, 58, 49]], ![[10, 44, 22, 28, 55], [40, 24, 54, 31, 30], [13, 3, 29, 40, 21], [56, 37, 28, 22, 23], [48, 44, 26, 48, 6], [54, 30, 41, 37, 1]], ![[0, 1], [26, 2, 18, 45, 23], [23, 51, 28, 56, 58], [8, 26, 32, 58, 51], [9, 3, 28, 16, 38], [10, 44, 22, 28, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 34, 58, 43], [], [], []]
 b := ![[], [22, 5, 26, 22, 33], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [48, 19, 57, 52, 37, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-869505365613918, 140097578832963, -674302813924994, 23337602176222, -383841785282333]
  a := ![-104, -15, -90, -104, -215]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14737379078202, 2374535234457, -11428861252966, 395552579258, -6505792970887]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 714924299 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![7, -31, 1, 1, 2]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![7, -31, 1, 1, 2]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![53, 12, 1, 0, 0], ![1, 33, 0, 1, 0], ![7, 23, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![7, -31, 1, 1, 2], ![12, -22, -55, -1, 0], ![-8, 6, 32, -29, -4], ![-140, 0, -58, -101, -220], ![-92, -31, -80, 82, 119]]]
  hmulB := by decide  
  f := ![![![20668355, -32750144, -104086605, -2159857, -564340], ![17255070, -115115357, 21350, 0, 0]], ![![11156607, -17678254, -56185094, -1165871, -304626], ![9314151, -62138321, 11529, 0, 0]], ![![20145718, -31921993, -101454593, -2105241, -550070], ![16818757, -112204463, 20811, 0, 0]], ![![6374364, -10100520, -32101553, -666125, -174050], ![5321699, -35502950, 6587, 0, 0]], ![![6578362, -10423758, -33128909, -687444, -179621], ![5492035, -36639162, 6797, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-53, -12, 61, 0, 0], ![-1, -33, 0, 61, 0], ![-7, -23, 0, 0, 61]], ![![-1, -2, 1, 1, 2], ![48, 11, -55, -1, 0], ![-27, 11, 32, -29, -4], ![75, 149, -58, -101, -220], ![53, -74, -80, 82, 119]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [31, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 60], [0, 1]]
 g := ![![[29, 39], [58], [34, 14], [41, 56], [16, 1]], ![[43, 22], [58], [14, 47], [22, 5], [32, 60]]]
 h' := ![![[16, 60], [16, 10], [44, 27], [10, 21], [53, 42], [0, 1]], ![[0, 1], [54, 51], [49, 34], [41, 40], [54, 19], [16, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [26, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [31, 45, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39285, 3789, 24980, -3474, 3059]
  a := ![-29, -4, -24, -30, -59]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21354, -4126, 24980, -3474, 3059]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![28, -24, 1, 1, 2]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![28, -24, 1, 1, 2]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![56, 32, 1, 0, 0], ![10, 24, 0, 1, 0], ![42, 21, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![28, -24, 1, 1, 2], ![12, 6, -41, -1, 0], ![-8, 6, 46, -22, -4], ![-112, 0, -44, -52, -164], ![-64, -24, -59, 61, 112]]]
  hmulB := by decide  
  f := ![![![14361525, 8619204, -52736997, -1318397, -74978], ![2312449, -78391588, 12810, 0, 0]], ![![7176332, 4306951, -26352251, -658791, -37466], ![1155523, -39171638, 6405, 0, 0]], ![![16943400, 10168718, -62217851, -1555412, -88456], ![2728138, -92484524, 15115, 0, 0]], ![![5177826, 3107520, -19013508, -475327, -27032], ![833716, -28262872, 4620, 0, 0]], ![![12358794, 7417263, -45382806, -1134546, -64523], ![1990002, -67459854, 11025, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-56, -32, 61, 0, 0], ![-10, -24, 0, 61, 0], ![-42, -21, 0, 0, 61]], ![![-2, -2, 1, 1, 2], ![38, 22, -41, -1, 0], ![-36, -14, 46, -22, -4], ![160, 100, -44, -52, -164], ![-34, -32, -59, 61, 112]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [19, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 60], [0, 1]]
 g := ![![[20, 45], [57], [21, 1], [25, 36], [47, 1]], ![[0, 16], [57], [7, 60], [9, 25], [33, 60]]]
 h' := ![![[47, 60], [6, 44], [28, 39], [13, 60], [22, 55], [0, 1]], ![[0, 1], [0, 17], [31, 22], [27, 1], [45, 6], [47, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [7, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [19, 14, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![87569, 10275, 63532, 5240, 29726]
  a := ![46, 10, 35, 51, 89]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-78215, -45455, 63532, 5240, 29726]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![-25, 1, 0, 0, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![-25, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![-25, 1, 0, 0, 0], ![0, -24, 2, 0, 0], ![0, 0, -26, 1, 0], ![4, 0, 2, -21, 8], ![4, 1, 3, -3, -29]]]
  hmulB := by decide  
  f := ![![![1715805, -27355436, 2645294, -20059, 2208], ![4183868, -69354072, 870043, -16836, 0]], ![![1044423, -16650662, 1610144, -12210, 1344], ![2546751, -42214318, 529602, -10248, 0]], ![![149226, -2378569, 230031, -1745, 192], ![363877, -6030368, 75701, -1464, 0]], ![![223872, -3568120, 345056, -2617, 288], ![545896, -9046226, 113522, -2196, 0]], ![![140700, -2242219, 216846, -1645, 181], ![343087, -5684678, 71365, -1380, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-36, 61, 0, 0, 0], ![-5, 0, 61, 0, 0], ![-8, 0, 0, 61, 0], ![-5, 0, 0, 0, 61]], ![![-1, 1, 0, 0, 0], ![14, -24, 2, 0, 0], ![2, 0, -26, 1, 0], ![2, 0, 2, -21, 8], ![2, 1, 3, -3, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0, 0, 0], ![7, -31, 1, 1, 2]] ![![61, 0, 0, 0, 0], ![28, -24, 1, 1, 2]]
  ![![61, 0, 0, 0, 0], ![-48, -69, 13, 27, 39]] where
 M := ![![![3721, 0, 0, 0, 0], ![1708, -1464, 61, 61, 122]], ![![427, -1891, 61, 61, 122], ![-424, -396, 1162, 86, 70]]]
 hmul := by decide  
 g := ![![![![61, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![76, 45, -12, -26, -37], ![61, 0, 0, 0, 0]]], ![![![55, 38, -12, -26, -37], ![61, 0, 0, 0, 0]], ![![8, 15, 15, -7, -11], ![19, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0, 0, 0], ![-48, -69, 13, 27, 39]] ![![61, 0, 0, 0, 0], ![-25, 1, 0, 0, 0]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![3721, 0, 0, 0, 0], ![-1525, 61, 0, 0, 0]], ![![-2928, -4209, 793, 1647, 2379], ![1464, 1647, -305, -671, -915]]]
 hmul := by decide  
 g := ![![![![61, 0, 0, 0, 0]], ![![-25, 1, 0, 0, 0]]], ![![![-48, -69, 13, 27, 39]], ![![24, 27, -5, -11, -15]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)


lemma PB434I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB434I1 : PrimesBelowBoundCertificateInterval O 23 61 434 where
  m := 9
  g := ![2, 4, 2, 2, 1, 2, 1, 1, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB434I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1, I31N2, I31N3]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
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
    · exact ![961, 31, 31, 31]
    · exact ![50653, 1369]
    · exact ![2825761, 41]
    · exact ![147008443]
    · exact ![103823, 2209]
    · exact ![418195493]
    · exact ![714924299]
    · exact ![3721, 3721, 61]
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
      exact NI31N2
      exact NI31N3
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I31N1, I31N2, I31N3, I41N1, I61N2]
  Il := ![[], [I31N1, I31N2, I31N3], [], [I41N1], [], [], [], [], [I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
