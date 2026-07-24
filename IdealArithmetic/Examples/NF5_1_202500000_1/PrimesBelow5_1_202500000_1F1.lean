
import IdealArithmetic.Examples.NF5_1_202500000_1.RI5_1_202500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![50959, -104844, 50121, -8105, -8693]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![50959, -104844, 50121, -8105, -8693]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![7, 7, 1, 0, 0], ![1, 19, 0, 1, 0], ![27, 7, 0, 0, 1]] where
  M :=![![![50959, -104844, 50121, -8105, -8693], ![-86930, 224231, -107469, 107759, -41113], ![-411130, 586458, -278788, -471569, 389923], ![2155180, -3967278, 1893744, 623527, -943138], ![-1404770, 3081852, -1474449, 620135, 3376]]]
  hmulB := by decide  
  f := ![![![-56428149, 27818292, 2406027, 287755, -4031117]], ![![-40311170, 19875319, 1718745, 205427, -2880097]], ![![-24344007, 12002087, 1037978, 124097, -1739203]], ![![-28214891, 13911299, 1203006, 143787, -2015858]], ![![-62766527, 30943817, 2676279, 320039, -4484024]]]
  g := ![![![-1968, -8305, 50121, -8105, -8693], ![57505, -27004, -107469, 107759, -41113], ![-293654, 302356, -278788, -471569, 389923], ![473799, -774777, 1893744, 623527, -943138], ![282934, 55062, -1474449, 620135, 3376]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [19, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 28], [0, 1]]
 g := ![![[17, 24], [16], [1, 9], [25, 1]], ![[8, 5], [16], [23, 20], [21, 28]]]
 h' := ![![[25, 28], [28, 16], [10, 4], [18, 26], [0, 1]], ![[0, 1], [22, 13], [23, 25], [1, 3], [25, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [2, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [19, 4, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![40819, -70274, 24339, 12760, -8158]
  a := ![0, 6, 2, 5, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2688, -14689, 24339, 12760, -8158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56428149, -27818292, -2406027, -287755, 4031117]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![56428149, -27818292, -2406027, -287755, 4031117]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![15, 4, 26, 1, 0], ![1, 26, 23, 0, 1]] where
  M :=![![![56428149, -27818292, -2406027, -287755, 4031117], ![40311170, -19875319, -1718745, -205427, 2880097], ![28800970, -14205246, -1227958, -146539, 2058389], ![-4108540, 2021682, 175008, 21045, -293078], ![14491070, -7149576, -618147, -73757, 1035858]]]
  hmulB := by decide  
  f := ![![![-50959, 104844, -50121, 8105, 8693]], ![![86930, -224231, 107469, -107759, 41113]], ![![411130, -586458, 278788, 471569, -389923]], ![![279915, -365686, 173545, 390614, -306897]], ![![450689, -768812, 366574, 256287, -272206]]]
  g := ![![![1955633, -4533666, -3022072, -287755, 4031117], ![1396982, -3239177, -2159306, -205427, 2880097], ![997954, -2315076, -1543479, -146539, 2058389], ![-142453, 329570, 219608, 21045, -293078], ![502123, -1165064, -776731, -73757, 1035858]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 3 2 4 [21, 2, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 7, 21], [26, 21, 8], [0, 1]]
 g := ![![[0, 1, 28], [24, 25], [12, 14, 9], [1]], ![[25, 24, 19, 18], [10, 23], [0, 7, 1, 18], [14, 24, 9, 10]], ![[22, 7, 13, 27], [2, 16], [1, 28, 12, 19], [12, 17, 2, 19]]]
 h' := ![![[0, 7, 21], [12, 17, 17], [9, 7, 5], [8, 27, 26], [0, 1]], ![[26, 21, 8], [22, 19, 18], [0, 23, 20], [25, 19, 11], [0, 7, 21]], ![[0, 1], [7, 22, 23], [22, 28, 4], [11, 12, 21], [26, 21, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 22], []]
 b := ![[], [4, 18, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 3
  hpos := by decide
  P := [21, 2, 3, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![114095361, -283154536, 204250516, -42866124, -74711224]
  a := ![3, -2, -1, -3, -56]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![28682705, 63131096, 104728548, -42866124, -74711224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![50959, -104844, 50121, -8105, -8693]] ![![56428149, -27818292, -2406027, -287755, 4031117]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-549, 839, -38, -51, -135]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-549, 839, -38, -51, -135]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![17, 18, 17, 1, 0], ![19, 15, 12, 0, 1]] where
  M :=![![![-549, 839, -38, -51, -135], ![-1350, 2067, -93, -109, -339], ![-3390, 5200, -290, -307, -775], ![-2180, 3221, 41, -217, -614], ![-3810, 5853, -280, -237, -956]]]
  hmulB := by decide  
  f := ![![![1331181, -656213, -56762, -6791, 95091]], ![![950910, -468757, -40547, -4851, 67927]], ![![679270, -334852, -28964, -3465, 48523]], ![![1651517, -814126, -70421, -8425, 117974]], ![![1549969, -764067, -66091, -7907, 110720]]]
  g := ![![![93, 122, 79, -51, -135], ![224, 294, 188, -109, -339], ![534, 721, 459, -307, -775], ![425, 527, 358, -217, -614], ![593, 789, 491, -237, -956]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [21, 1, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 21, 9], [20, 9, 22], [0, 1]]
 g := ![![[9, 25, 4], [2, 27, 14], [8, 12, 10], [1]], ![[23, 0, 17, 16], [20, 18, 17, 7], [8, 10, 5, 4], [23, 20, 12, 16]], ![[13, 24, 29, 24], [20, 30, 30, 27], [12, 10, 8, 17], [12, 28, 24, 15]]]
 h' := ![![[28, 21, 9], [20, 3, 29], [18, 26, 18], [10, 30, 17], [0, 1]], ![[20, 9, 22], [16, 4, 9], [19, 23, 24], [17, 0, 20], [28, 21, 9]], ![[0, 1], [28, 24, 24], [14, 13, 20], [29, 1, 25], [20, 9, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 14], []]
 b := ![[], [11, 9, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [21, 1, 14, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4801047, -9402053, 5067460, 877289, -2363369]
  a := ![1, 3, 1, 2, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1122295, 330880, 597225, 877289, -2363369]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17931, 8757, 774, 99, -1267]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-17931, 8757, 774, 99, -1267]] 
 ![![31, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![-17931, 8757, 774, 99, -1267], ![-12670, 6043, 563, 83, -871], ![-8710, 3796, 426, 89, -539], ![1660, -1177, -33, 23, 178], ![-4070, 1435, 234, 71, -196]]]
  hmulB := by decide  
  f := ![![![59, -267, 130, -309, 167]], ![![71, -168, 81, -56, 14]], ![![-322, 572, -272, -135, 165]], ![![678, -1473, 705, -269, -20]], ![![235, -420, 202, 96, -121]]]
  g := ![![![-2405, 8757, 774, 99, -1267], ![-1684, 6043, 563, 83, -871], ![-1119, 3796, 426, 89, -539], ![263, -1177, -33, 23, 178], ![-485, 1435, 234, 71, -196]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-111, 50, 8, 2, -10]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-111, 50, 8, 2, -10]] 
 ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-111, 50, 8, 2, -10], ![-100, 77, -14, 2, -2], ![-20, -64, 47, -34, 6], ![40, -18, 6, 101, -68], ![-180, 302, -136, -22, 51]]]
  hmulB := by decide  
  f := ![![![9759, -15462, 1336, 1146, 2678]], ![![7160, -11339, 974, 838, 1962]], ![![3287, -5182, 419, 372, 888]], ![![6695, -10572, 874, 767, 1818]], ![![5612, -8838, 704, 630, 1511]]]
  g := ![![![-35, 50, 8, 2, -10], ![-52, 77, -14, 2, -2], ![51, -64, 47, -34, 6], ![-19, -18, 6, 101, -68], ![-190, 302, -136, -22, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-549, 839, -38, -51, -135]] ![![-17931, 8757, 774, 99, -1267]]
  ![![9759, -15462, 1336, 1146, 2678]] where
 M := ![![![9759, -15462, 1336, 1146, 2678]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![9759, -15462, 1336, 1146, 2678]] ![![-111, 50, 8, 2, -10]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)
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


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [2, 9, 5, 15, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 22, 2, 23, 18], [28, 14, 29, 23, 2], [4, 30, 10, 14, 23], [36, 7, 33, 14, 31], [0, 1]]
 g := ![![[16, 5, 14, 32, 16], [9, 22, 34, 34], [34, 24, 23, 36, 1], [], []], ![[19, 34, 16, 34, 1, 32, 11, 32], [28, 10, 5, 25], [22, 20, 10, 0, 16, 21, 10, 6], [12, 35, 31, 36], [19, 10, 23, 28]], ![[6, 7, 13, 22, 27, 2, 1, 29], [33, 35, 6, 7], [30, 25, 33, 23, 27, 19, 13, 2], [23, 8, 2, 16], [34, 16, 14, 4]], ![[2, 15, 2, 28, 7, 16, 6, 31], [11, 0, 22, 25], [11, 7, 33, 1, 23, 21, 16, 32], [2, 21, 29, 25], [22, 6, 4, 11]], ![[6, 7, 16, 14, 14, 6, 6, 32], [1, 26, 21, 3], [17, 11, 9, 36, 23, 20, 16, 23], [4, 9, 24, 25], [1, 19, 18, 36]]]
 h' := ![![[5, 22, 2, 23, 18], [18, 30, 15, 31, 33], [6, 16, 12, 16, 16], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[28, 14, 29, 23, 2], [19, 31, 5, 17, 11], [1, 22, 10, 34, 32], [34, 30, 3, 23, 5], [24, 29, 14, 16, 31], [5, 22, 2, 23, 18]], ![[4, 30, 10, 14, 23], [29, 33, 0, 36, 25], [13, 4, 24, 11, 9], [12, 14, 20, 35, 1], [13, 2, 35, 7, 33], [28, 14, 29, 23, 2]], ![[36, 7, 33, 14, 31], [26, 36, 31, 7, 14], [14, 22, 27, 36, 32], [3, 36, 17, 9, 22], [9, 30, 31, 35, 5], [4, 30, 10, 14, 23]], ![[0, 1], [5, 18, 23, 20, 28], [28, 10, 1, 14, 22], [30, 31, 34, 7, 8], [36, 13, 30, 16, 5], [36, 7, 33, 14, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 34, 18, 20], [], [], []]
 b := ![[], [8, 36, 15, 29, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [2, 9, 5, 15, 1, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-378280134172627, 757535531258990, -363718083068729, 15158844744607, 92899650224577]
  a := ![1, -6, -3, -7, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10223787410071, 20473933277270, -9830218461317, 409698506611, 2510801357421]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13941, -6927, -560, -93, 999]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![13941, -6927, -560, -93, 999]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![3, 13, 1, 0, 0], ![20, 13, 0, 1, 0], ![1, 3, 0, 0, 1]] where
  M :=![![![13941, -6927, -560, -93, 999], ![9990, -4947, -401, 65, 627], ![6270, -1988, -1024, -305, 887], ![1300, -4145, 2263, -123, -610], ![3190, -553, -732, 919, -202]]]
  hmulB := by decide  
  f := ![![![-104939, 149203, 6172, -3055, -19533]], ![![-195330, 269243, 21699, -1079, -31753]], ![![-77357, 106264, 9033, -229, -12377]], ![![-113650, 157480, 11632, -1076, -18923]], ![![-18559, 23621, 4423, 963, -1952]]]
  g := ![![![402, -35, -560, -93, 999], ![226, -60, -401, 65, 627], ![355, 308, -1024, -305, 887], ![-59, -735, 2263, -123, -610], ![-312, -58, -732, 919, -202]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [37, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 40], [0, 1]]
 g := ![![[17, 10], [20], [39], [14, 32], [1]], ![[0, 31], [20], [39], [17, 9], [1]]]
 h' := ![![[27, 40], [19, 16], [12, 26], [15, 30], [4, 27], [0, 1]], ![[0, 1], [0, 25], [17, 15], [5, 11], [36, 14], [27, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [39, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [37, 14, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![46304, -78204, 29366, 19615, -15484]
  a := ![-1, 7, 5, 9, -28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10210, -16305, 29366, 19615, -15484]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-82341, 40591, 3511, 420, -5882]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-82341, 40591, 3511, 420, -5882]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![37, 35, 1, 0, 0], ![31, 24, 0, 1, 0], ![18, 13, 0, 0, 1]] where
  M :=![![![-82341, 40591, 3511, 420, -5882], ![-58820, 28997, 2508, 300, -4202], ![-42020, 20718, 1791, 214, -3002], ![6000, -2957, -255, -31, 428], ![-21140, 10425, 901, 108, -1511]]]
  hmulB := by decide  
  f := ![![![299, -471, 37, 34, 82]], ![![820, -1293, 106, 88, 218]], ![![1023, -1612, 130, 112, 274]], ![![749, -1180, 94, 81, 202]], ![![462, -728, 59, 50, 123]]]
  g := ![![![-2912, -388, 3511, 420, -5882], ![-2080, -277, 2508, 300, -4202], ![-1485, -197, 1791, 214, -3002], ![212, 28, -255, -31, 428], ![-747, -99, 901, 108, -1511]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [26, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 40], [0, 1]]
 g := ![![[33, 36], [25], [32], [35, 9], [1]], ![[18, 5], [25], [32], [21, 32], [1]]]
 h' := ![![[3, 40], [4, 6], [11, 36], [33, 14], [15, 3], [0, 1]], ![[0, 1], [22, 35], [37, 5], [34, 27], [24, 38], [3, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [25, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [26, 38, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23226, -41280, 10088, 200, 4240]
  a := ![0, 4, -2, -6, -16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10550, -11080, 10088, 200, 4240]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![280501, -708178, 339340, -315920, 113728]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![280501, -708178, 339340, -315920, 113728]] 
 ![![41, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![280501, -708178, 339340, -315920, 113728], ![1137280, -1564411, 743178, 1424248, -1149952], ![-11499520, 21562120, -10295145, -2512092, 4547040], ![28484960, -58471654, 27951746, -4253487, -5024184], ![-908540, 7813086, -3771046, 12447866, -7172353]]]
  hmulB := by decide  
  f := ![![![101218710821, -49896293550, -4316003152, -516368736, 7230407744]], ![![85700981594, -42246747519, -3654321486, -437204832, 6121921856]], ![![82728458173, -40781426142, -3527572065, -422040508, 5909584000]], ![![41788801517, -20600008000, -1781890002, -213186247, 2985120648]], ![![35196200714, -17350150634, -1500779122, -179554030, 2514187983]]]
  g := ![![![413141, -708178, 339340, -315920, 113728], ![529012, -1564411, 743178, 1424248, -1149952], ![-10385971, 21562120, -10295145, -2512092, 4547040], ![30164913, -58471654, 27951746, -4253487, -5024184], ![-6178286, 7813086, -3771046, 12447866, -7172353]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![13941, -6927, -560, -93, 999]] ![![-82341, 40591, 3511, 420, -5882]]
  ![![-738615401, 364104408, 31494789, 3768055, -52761881]] where
 M := ![![![-738615401, 364104408, 31494789, 3768055, -52761881]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-738615401, 364104408, 31494789, 3768055, -52761881]] ![![280501, -708178, 339340, -315920, 113728]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![521849599, -865769366, 412625435, 347326785, -345304911]]]
 hmul := by decide  
 g := ![![![![12728039, -21116326, 10064035, 8471385, -8422071]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
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


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [18, 11, 7, 38, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 38, 22, 12, 19], [12, 31, 41, 37, 17], [35, 12, 2, 4, 16], [1, 4, 21, 33, 34], [0, 1]]
 g := ![![[22, 39, 23, 40, 1], [29, 36, 15, 36, 24], [2, 18, 25, 16], [1], []], ![[41, 11, 30, 17, 42, 12, 29, 12], [14, 23, 21, 0, 21, 5, 42, 20], [3, 1, 33, 25], [10, 41, 7, 6, 4, 26, 21, 26], [22, 29, 1, 17]], ![[34, 16, 1, 18, 7, 23, 41, 16], [24, 37, 30, 26, 26, 10, 33, 16], [5, 10, 13, 35], [41, 2, 31, 11, 34, 27, 21, 21], [17, 16, 16, 31]], ![[27, 6, 0, 22, 27, 11, 21, 15], [6, 7, 8, 9, 25, 3, 11, 36], [14, 24, 37, 38], [18, 16, 0, 33, 5, 8, 20, 4], [23, 42, 7, 41]], ![[27, 41, 42, 4, 23, 8, 37, 27], [23, 25, 21, 20, 5, 30, 42, 33], [9, 37, 3, 24], [40, 39, 31, 14, 22, 37, 35, 30], [10, 15, 28, 38]]]
 h' := ![![[34, 38, 22, 12, 19], [37, 19, 24, 21, 42], [30, 7, 12, 26, 29], [25, 32, 36, 5, 39], [0, 0, 1], [0, 1]], ![[12, 31, 41, 37, 17], [24, 26, 2, 1, 35], [27, 8, 21, 11, 32], [34, 23, 3, 34, 38], [29, 14, 41, 14, 14], [34, 38, 22, 12, 19]], ![[35, 12, 2, 4, 16], [6, 25, 26, 35, 36], [31, 41, 5, 17, 7], [32, 7, 18, 38, 32], [10, 11, 29, 3, 29], [12, 31, 41, 37, 17]], ![[1, 4, 21, 33, 34], [3, 0, 0, 26, 3], [20, 23, 29, 12, 23], [33, 19, 34, 11, 34], [37, 3, 8, 22, 21], [35, 12, 2, 4, 16]], ![[0, 1], [20, 16, 34, 3, 13], [41, 7, 19, 20, 38], [17, 5, 38, 41, 29], [36, 15, 7, 4, 22], [1, 4, 21, 33, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 32, 7, 18], [], [], []]
 b := ![[], [35, 17, 38, 18, 33], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [18, 11, 7, 38, 4, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![37014809900037, -70265549727400, 33573746691712, 6326836101943, -13605139965851]
  a := ![13, 6, 4, 7, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![860809532559, -1634082551800, 780784806784, 147135723301, -316398603857]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, -164, 78, 0, -22]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![83, -164, 78, 0, -22]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![3, 46, 32, 1, 0], ![24, 16, 5, 0, 1]] where
  M :=![![![83, -164, 78, 0, -22], ![-220, 501, -240, 134, -22], ![-220, 64, -27, -770, 514], ![2680, -4640, 2216, 1385, -1540], ![-2620, 5460, -2606, 564, 353]]]
  hmulB := by decide  
  f := ![![![22949, -11332, -978, -116, 1642]], ![![16420, -8133, -700, -82, 1178]], ![![11780, -5880, -505, -58, 850]], ![![25521, -12670, -1090, -127, 1834]], ![![18688, -9244, -797, -94, 1339]]]
  g := ![![![13, 4, 4, 0, -22], ![-2, -113, -94, 134, -22], ![-218, 580, 469, -770, 514], ![755, -930, -732, 1385, -1540], ![-272, -556, -477, 564, 353]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [25, 15, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 0, 44], [14, 46, 3], [0, 1]]
 g := ![![[40, 26, 34], [40, 2, 18], [11, 44, 2], [33, 1, 1], []], ![[23, 29, 40, 43], [5, 3, 29, 41], [42, 38, 20, 31], [15, 8, 46, 44], [9, 9]], ![[7, 14, 24, 21], [21, 17, 1, 2], [44, 17, 15, 8], [35, 16], [3, 9]]]
 h' := ![![[34, 0, 44], [34, 10, 9], [7, 22, 21], [21, 44, 40], [0, 0, 1], [0, 1]], ![[14, 46, 3], [11, 3, 8], [2, 7, 7], [29, 29, 16], [38, 16, 46], [34, 0, 44]], ![[0, 1], [41, 34, 30], [36, 18, 19], [25, 21, 38], [27, 31], [14, 46, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 29], []]
 b := ![[], [21, 1, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [25, 15, 46, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-113865, 127796, -67494, -210688, 162668]
  a := ![-1, -2, -1, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-72039, 153548, 124706, -210688, 162668]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22949, 11332, 978, 116, -1642]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-22949, 11332, 978, 116, -1642]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![18, 31, 1, 0, 0], ![41, 30, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-22949, 11332, 978, 116, -1642], ![-16420, 8133, 700, 82, -1178], ![-11780, 5880, 505, 58, -850], ![1640, -784, -64, -7, 116], ![-5940, 2972, 262, 32, -427]]]
  hmulB := by decide  
  f := ![![![-83, 164, -78, 0, 22]], ![![220, -501, 240, -134, 22]], ![![118, -269, 129, -72, 12]], ![![11, -78, 38, -115, 66]], ![![1, -8, 4, -12, 7]]]
  g := ![![![119, -478, 978, 116, -1642], ![88, -341, 700, 82, -1178], ![66, -245, 505, 58, -850], ![-11, 30, -64, -7, 116], ![27, -130, 262, 32, -427]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [44, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 46], [0, 1]]
 g := ![![[31, 6], [39, 16], [16, 32], [40, 1], [1]], ![[25, 41], [23, 31], [31, 15], [39, 46], [1]]]
 h' := ![![[46, 46], [23, 10], [1, 4], [26, 19], [3, 46], [0, 1]], ![[0, 1], [13, 37], [44, 43], [7, 28], [4, 1], [46, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [18, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [44, 1, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5536, -7243, 2289, 6364, -3888]
  a := ![3, -3, 0, -7, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3746, -5726, 2289, 6364, -3888]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![83, -164, 78, 0, -22]] ![![-22949, 11332, 978, 116, -1642]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-483, 778, -51, -51, -129]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-483, 778, -51, -51, -129]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![13, 11, 49, 1, 0], ![6, 4, 18, 0, 1]] where
  M :=![![![-483, 778, -51, -51, -129], ![-1290, 2019, -125, -129, -333], ![-3330, 5166, -308, -325, -849], ![-2580, 3980, -226, -245, -650], ![-4070, 6290, -359, -389, -1028]]]
  hmulB := by decide  
  f := ![![![9, -10, 3, 1, -1]], ![![-10, 27, -15, 3, 3]], ![![30, -70, 30, -33, 15]], ![![29, -63, 26, -28, 13]], ![![8, -18, 7, -11, 6]]]
  g := ![![![18, 35, 90, -51, -129], ![45, 90, 230, -129, -333], ![113, 229, 583, -325, -849], ![85, 175, 443, -245, -650], ![135, 277, 702, -389, -1028]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [4, 17, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 3, 7], [13, 49, 46], [0, 1]]
 g := ![![[51, 17, 13], [10, 9], [40, 10, 29], [14, 17], [1]], ![[13, 12, 49, 52], [], [6, 50, 14, 28], [28, 28], [5, 26, 12, 25]], ![[10, 40, 38, 38], [15, 9], [13, 6, 32, 4], [25, 52], [18, 39, 0, 28]]]
 h' := ![![[8, 3, 7], [14, 48, 15], [52, 32, 3], [13, 42, 20], [49, 36, 21], [0, 1]], ![[13, 49, 46], [9, 48, 11], [50, 45], [7, 51, 2], [15, 16, 9], [8, 3, 7]], ![[0, 1], [30, 10, 27], [39, 29, 50], [31, 13, 31], [5, 1, 23], [13, 49, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 45], []]
 b := ![[], [21, 3, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [4, 17, 32, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8195146, 14978312, -7688404, -3195614, 4620226]
  a := ![1, -4, -3, -5, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![106160, 597154, 1240238, -3195614, 4620226]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3223753, 1589166, 137462, 16446, -230284]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-3223753, 1589166, 137462, 16446, -230284]] 
 ![![53, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![43, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-3223753, 1589166, 137462, 16446, -230284], ![-2302840, 1135197, 98194, 11748, -164500], ![-1645000, 810912, 70143, 8392, -117508], ![234960, -115826, -10018, -1199, 16784], ![-827520, 407930, 35286, 4222, -59113]]]
  hmulB := by decide  
  f := ![![![-6701, 9746, 130, -314, -1364]], ![![-1901, 2759, 44, -86, -384]], ![![-5931, 8598, 149, -262, -1192]], ![![-2329, 3348, 92, -89, -452]], ![![-1199, 1684, 96, -24, -213]]]
  g := ![![![-537007, 1589166, 137462, 16446, -230284], ![-383603, 1135197, 98194, 11748, -164500], ![-274021, 810912, 70143, 8392, -117508], ![39139, -115826, -10018, -1199, 16784], ![-137847, 407930, 35286, 4222, -59113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-87, 132, -3, -9, -25]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-87, 132, -3, -9, -25]] 
 ![![53, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-87, 132, -3, -9, -25], ![-250, 397, -37, -13, -61], ![-610, 922, -54, -109, -113], ![-260, 362, 120, 53, -218], ![-890, 1468, -237, -25, -154]]]
  hmulB := by decide  
  f := ![![![55874701, -27543732, -2382517, -285045, 3991327]], ![![52410823, -25836195, -2234816, -267374, 3743890]], ![![39544819, -19493830, -1686205, -201738, 2824826]], ![![30496113, -15033222, -1300365, -155576, 2178445]], ![![12921494, -6369720, -550977, -65919, 923028]]]
  g := ![![![-111, 132, -3, -9, -25], ![-325, 397, -37, -13, -61], ![-741, 922, -54, -109, -113], ![-403, 362, 120, 53, -218], ![-1160, 1468, -237, -25, -154]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-483, 778, -51, -51, -129]] ![![-3223753, 1589166, 137462, 16446, -230284]]
  ![![-55874701, 27543732, 2382517, 285045, -3991327]] where
 M := ![![![-55874701, 27543732, 2382517, 285045, -3991327]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![-55874701, 27543732, 2382517, 285045, -3991327]] ![![-87, 132, -3, -9, -25]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24761, 38023, -1674, -2143, -6049]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-24761, 38023, -1674, -2143, -6049]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![39, 28, 29, 1, 0], ![44, 1, 21, 0, 1]] where
  M :=![![![-24761, 38023, -1674, -2143, -6049], ![-60490, 92313, -3851, -5111, -14621], ![-146210, 222420, -8774, -12101, -35065], ![-102220, 154853, -5467, -8155, -24202], ![-163290, 247553, -8858, -13087, -38728]]]
  hmulB := by decide  
  f := ![![![-539, 1067, -510, -3, 145]], ![![1450, -3291, 1575, -869, 133]], ![![1330, -208, 84, 5021, -3343]], ![![691, -450, 209, 1899, -1314]], ![![386, 62, -35, 1709, -1120]]]
  g := ![![![5508, 1764, 3178, -2143, -6049], ![13257, 4238, 7651, -5111, -14621], ![31671, 10107, 18280, -12101, -35065], ![21707, 6905, 12530, -8155, -24202], ![34765, 11063, 20067, -13087, -38728]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [41, 26, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 51, 7], [20, 7, 52], [0, 1]]
 g := ![![[23, 21, 53], [44, 37, 19], [8, 41], [32, 27, 28], [1]], ![[45, 27, 16, 12], [37, 56, 27, 25], [10, 35], [52, 35, 43, 20], [4, 19, 9, 48]], ![[21, 44, 49, 23], [38, 15, 31, 24], [53, 48], [15, 48, 27, 44], [36, 1, 21, 11]]]
 h' := ![![[1, 51, 7], [25, 13, 17], [45, 25, 14], [45, 37, 10], [18, 33, 21], [0, 1]], ![[20, 7, 52], [53, 2, 33], [6, 40, 37], [11, 44, 34], [14, 37, 24], [1, 51, 7]], ![[0, 1], [39, 44, 9], [37, 53, 8], [26, 37, 15], [34, 48, 14], [20, 7, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 54], []]
 b := ![[], [36, 13, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [41, 26, 38, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3783, 9540, -5150, 693, 1700]
  a := ![4, 0, 0, 1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1790, -196, -1033, 693, 1700]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![539, -1067, 510, 3, -145]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![539, -1067, 510, 3, -145]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![2, 2, 1, 0, 0], ![56, 57, 0, 1, 0], ![0, 29, 0, 0, 1]] where
  M :=![![![539, -1067, 510, 3, -145], ![-1450, 3291, -1575, 869, -133], ![-1330, 208, -84, -5021, 3343], ![17380, -30017, 14315, 9119, -10042], ![-17110, 35631, -17036, 3609, 2390]]]
  hmulB := by decide  
  f := ![![![24761, -38023, 1674, 2143, 6049]], ![![60490, -92313, 3851, 5111, 14621]], ![![5368, -8188, 336, 451, 1295]], ![![83674, -127898, 5402, 7110, 20277]], ![![32500, -49570, 2043, 2734, 7843]]]
  g := ![![![-11, 33, 510, 3, -145], ![-796, -665, -1575, 869, -133], ![4746, 3214, -84, -5021, 3343], ![-8846, -4868, 14315, 9119, -10042], ![-3138, -3480, -17036, 3609, 2390]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [17, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 58], [0, 1]]
 g := ![![[39, 7], [26, 1], [29], [11, 4], [45, 1]], ![[0, 52], [12, 58], [29], [14, 55], [31, 58]]]
 h' := ![![[45, 58], [30, 19], [20, 1], [49, 18], [2, 2], [0, 1]], ![[0, 1], [0, 40], [6, 58], [33, 41], [33, 57], [45, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [34, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [17, 14, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![502764, -839524, 279142, 205871, -118828]
  a := ![7, 23, -1, 23, -90]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-196344, -164177, 279142, 205871, -118828]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-24761, 38023, -1674, -2143, -6049]] ![![539, -1067, 510, 3, -145]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26144037541, -12887840865, -1114791247, -133374098, 1867560492]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![26144037541, -12887840865, -1114791247, -133374098, 1867560492]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![42, 12, 32, 55, 1]] where
  M :=![![![26144037541, -12887840865, -1114791247, -133374098, 1867560492], ![18675604920, -9206237709, -796334570, -95273806, 1334064100], ![13340641000, -6576339174, -568849773, -68057428, 952968876], ![-1905476120, 939314479, 81250193, 9720807, -136114856], ![6711036280, -3308240647, -286161021, -34236426, 479392909]]]
  hmulB := by decide  
  f := ![![![-4599, 7033, -325, -404, -1124]], ![![-11240, 17161, -756, -966, -2740]], ![![-27400, 41786, -1809, -2320, -6604]], ![![-19320, 29305, -1061, -1631, -4640]], ![![-37678, 57332, -2308, -3197, -9083]]]
  g := ![![![-857270543, -578665029, -997979131, -1686052478, 1867560492], ![-612378480, -413360769, -712891570, -1204406546, 1334064100], ![-437443472, -295278126, -509243505, -860349928, 952968876], ![62481112, 42175291, 72736485, 122885867, -136114856], ![-220056818, -148540255, -256175969, -432800761, 479392909]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [26, 35, 36, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 42, 60, 4], [41, 7, 9, 50], [55, 11, 53, 7], [0, 1]]
 g := ![![[60, 19, 31, 27], [44, 53, 46], [16, 8, 9, 60], [26, 25, 0, 1], []], ![[56, 22, 43, 47, 22, 45], [30, 3, 27], [24, 38, 49, 43, 5, 22], [22, 10, 34, 54, 50, 60], [6, 0, 32, 29, 13, 3]], ![[30, 11, 42, 49, 11, 28], [42, 54, 27], [8, 29, 46, 38, 12, 37], [2, 0, 50, 32, 43, 31], [48, 33, 24, 21, 34, 11]], ![[34, 10, 28, 49, 37, 29], [28, 14, 19], [30, 54, 7, 50, 13, 59], [3, 57, 27, 0, 4, 31], [59, 46, 48, 7, 44, 38]]]
 h' := ![![[26, 42, 60, 4], [14, 12, 7, 24], [11, 50, 53, 31], [56, 26, 19, 50], [0, 0, 0, 1], [0, 1]], ![[41, 7, 9, 50], [47, 56, 20, 39], [41, 7, 42, 24], [46, 43, 25, 6], [35, 54, 11, 25], [26, 42, 60, 4]], ![[55, 11, 53, 7], [2, 59, 50, 8], [22, 32, 24, 24], [18, 32, 31, 38], [24, 6, 22, 6], [41, 7, 9, 50]], ![[0, 1], [19, 56, 45, 51], [36, 33, 3, 43], [13, 21, 47, 28], [19, 1, 28, 29], [55, 11, 53, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [60, 59, 55], []]
 b := ![[], [], [20, 23, 15, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [26, 35, 36, 0, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![85609817498, -155637680239, 72930294158, 27214790221, -37645183831]
  a := ![1, 9, 1, 8, -33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![27323074400, 4854172553, 20943871750, 34388522966, -37645183831]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4599, -7033, 325, 404, 1124]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![4599, -7033, 325, 404, 1124]] 
 ![![61, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![4599, -7033, 325, 404, 1124], ![11240, -17161, 756, 966, 2740], ![27400, -41786, 1809, 2320, 6604], ![19320, -29305, 1061, 1631, 4640], ![30920, -47007, 1823, 2512, 7447]]]
  hmulB := by decide  
  f := ![![![-26144037541, 12887840865, 1114791247, 133374098, -1867560492]], ![![-10163745383, 5010271764, 433385791, 51850460, -726032056]], ![![-8790514620, 4333330434, 374830733, 44844908, -627937356]], ![![-1683125804, 829705721, 71769095, 8586485, -120231592]], ![![-2252970885, 1110613852, 96067496, 11493556, -160937629]]]
  g := ![![![2502, -7033, 325, 404, 1124], ![6119, -17161, 756, 966, 2740], ![14918, -41786, 1809, 2320, 6604], ![10531, -29305, 1061, 1631, 4640], ![16858, -47007, 1823, 2512, 7447]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![26144037541, -12887840865, -1114791247, -133374098, 1867560492]] ![![4599, -7033, 325, 404, 1124]]
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


lemma PB886I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB886I1 : PrimesBelowBoundCertificateInterval O 23 61 886 where
  m := 9
  g := ![2, 3, 1, 3, 1, 2, 3, 2, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB886I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
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
    · exact ![841, 24389]
    · exact ![29791, 31, 31]
    · exact ![69343957]
    · exact ![1681, 1681, 41]
    · exact ![147008443]
    · exact ![103823, 2209]
    · exact ![148877, 53, 53]
    · exact ![205379, 3481]
    · exact ![13845841, 61]
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
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
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
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I29N0, I31N1, I31N2, I41N2, I53N1, I53N2, I61N1]
  Il := ![[I29N0], [I31N1, I31N2], [], [I41N2], [], [], [I53N1, I53N2], [], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
