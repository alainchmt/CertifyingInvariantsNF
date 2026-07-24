
import IdealArithmetic.Examples.NF5_1_40500000_1.RI5_1_40500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-90, 22, 67, -126, -191]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-90, 22, 67, -126, -191]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![21, 12, 1, 0, 0], ![27, 23, 0, 1, 0], ![21, 12, 0, 0, 1]] where
  M :=![![![-90, 22, 67, -126, -191], ![-825, 119, 209, -90, -435], ![-1485, 130, -46, 950, 585], ![778, -136, -318, 401, 802], ![-322, 28, -8, 202, 121]]]
  hmulB := by decide  
  f := ![![![-6128, -1758, 823, -2476, -3561]], ![![-15635, -4489, 2109, -6320, -9125]], ![![-12287, -3524, 1653, -4964, -7154]], ![![-18187, -5221, 2450, -7351, -10600]], ![![-11300, -3242, 1521, -4566, -6582]]]
  g := ![![![204, 152, 67, -126, -191], ![219, 169, 209, -90, -435], ![-1326, -972, -46, 950, 585], ![-697, -523, -318, 401, 802], ![-281, -206, -8, 202, 121]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [4, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 28], [0, 1]]
 g := ![![[17, 22], [1], [26, 23], [19, 1]], ![[0, 7], [1], [28, 6], [9, 28]]]
 h' := ![![[19, 28], [24, 14], [12, 1], [11, 9], [0, 1]], ![[0, 1], [0, 15], [2, 28], [8, 20], [19, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [13, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [4, 10, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-351, 280, 696, -145, -2200]
  a := ![-11, -7, 13, -19, -44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1212, 747, 696, -145, -2200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 3, 1, 2, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-1, 3, 1, 2, 0]] 
 ![![29, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-1, 3, 1, 2, 0], ![4, 6, -3, 16, 16], ![80, 5, -26, 50, 80], ![32, -3, -5, -3, 8], ![20, 2, -6, 12, 19]]]
  hmulB := by decide  
  f := ![![![15, 7, 13, 8, -64]], ![![-4, 4, -1, 2, 0]], ![![35, -16, 15, -4, -48]], ![![4, 9, 7, 7, -40]], ![![20, -6, 10, 0, -37]]]
  g := ![![![-2, 3, 1, 2, 0], ![-17, 6, -3, 16, 16], ![-58, 5, -26, 50, 80], ![1, -3, -5, -3, 8], ![-14, 2, -6, 12, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![315, -30, -2, -170, -86]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![315, -30, -2, -170, -86]] 
 ![![29, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![315, -30, -2, -170, -86], ![-598, 135, 394, -702, -1102], ![-4710, 670, 1139, -370, -2310], ![-468, -6, -250, 917, 948], ![-1010, 144, 246, -84, -501]]]
  hmulB := by decide  
  f := ![![![6219, 1734, -810, 2478, 3542]], ![![1824, 519, -242, 734, 1050]], ![![6112, 1702, -801, 2434, 3506]], ![![1589, 440, -204, 631, 894]], ![![4252, 1188, -558, 1696, 2439]]]
  g := ![![![113, -30, -2, -170, -86], ![506, 135, 394, -702, -1102], ![358, 670, 1139, -370, -2310], ![-635, -6, -250, 917, 948], ![80, 144, 246, -84, -501]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2

def I29N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![775773, 222359, -104271, 313318, 451366]] i)))

def SI29N3: IdealEqSpanCertificate' Table ![![775773, 222359, -104271, 313318, 451366]] 
 ![![29, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![775773, 222359, -104271, 313318, 451366], ![1980734, 567736, -266229, 799976, 1152446], ![5057290, 1449565, -679746, 2042530, 2942470], ![300880, 86241, -40441, 121519, 175060], ![1438146, 412214, -193300, 580836, 836753]]]
  hmulB := by decide  
  f := ![![![361, -101, -279, 552, 810]], ![![209, -41, -100, 150, 264]], ![![351, -56, -85, 32, 180]], ![![201, -68, -192, 413, 574]], ![![237, -57, -145, 256, 407]]]
  g := ![![![-498129, 222359, -104271, 313318, 451366], ![-1271843, 567736, -266229, 799976, 1152446], ![-3247319, 1449565, -679746, 2042530, 2942470], ![-193197, 86241, -40441, 121519, 175060], ![-923443, 412214, -193300, 580836, 836753]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N3 : Nat.card (O ⧸ I29N3) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N3)

lemma isPrimeI29N3 : Ideal.IsPrime I29N3 := prime_ideal_of_norm_prime hp29.out _ NI29N3
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-90, 22, 67, -126, -191]] ![![-1, 3, 1, 2, 0]]
  ![![-2314, 193, -122, 1608, 1075]] where
 M := ![![![-2314, 193, -122, 1608, 1075]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-2314, 193, -122, 1608, 1075]] ![![315, -30, -2, -170, -86]]
  ![![-2107998, 158887, -195838, 1687270, 1253947]] where
 M := ![![![-2107998, 158887, -195838, 1687270, 1253947]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N2 : IdealMulLeCertificate' Table 
  ![![-2107998, 158887, -195838, 1687270, 1253947]] ![![775773, 222359, -104271, 313318, 451366]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![51446, -7192, -11687, 2030, 22765]]]
 hmul := by decide  
 g := ![![![![1774, -248, -403, 70, 785]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2, I29N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
    exact isPrimeI29N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1 ⊙ MulI29N2)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [15, 8, 28, 21, 25, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 9, 13, 28, 3], [20, 18, 5, 7, 4], [8, 9, 24, 28, 18], [8, 25, 20, 30, 6], [0, 1]]
 g := ![![[2, 1, 3, 27, 1], [25, 4, 6, 4, 4], [15, 6, 1], []], ![[20, 18, 1, 5, 1, 29, 9, 22], [20, 4, 14, 30, 17, 5, 25, 27], [1, 15, 1, 6, 14, 6, 17, 15], [8, 2, 1, 21, 0, 10, 19, 27]], ![[22, 25, 14, 17, 17, 23, 7, 5], [18, 17, 21, 7, 15, 24, 3, 8], [0, 0, 22, 1, 23, 3, 24, 4], [6, 24, 25, 19, 23, 22, 7, 2]], ![[11, 17, 3, 26, 5, 26, 30, 18], [14, 7, 25, 0, 2, 22, 5, 20], [29, 30, 29, 17, 9, 3, 7, 18], [22, 2, 22, 2, 13, 23, 22, 4]], ![[24, 28, 17, 12, 5, 21, 24, 30], [19, 22, 25, 22, 4, 6, 14, 23], [28, 20, 8, 23, 30, 16, 16, 30], [22, 18, 9, 4, 6, 27, 10, 30]]]
 h' := ![![[1, 9, 13, 28, 3], [28, 21, 27, 26, 1], [23, 7, 13, 5, 29], [0, 0, 0, 1], [0, 1]], ![[20, 18, 5, 7, 4], [17, 16, 10, 2, 20], [10, 4, 7, 13, 28], [5, 26, 27, 7, 6], [1, 9, 13, 28, 3]], ![[8, 9, 24, 28, 18], [19, 28, 2, 30, 3], [4, 3, 22, 14, 23], [5, 19, 29, 3, 1], [20, 18, 5, 7, 4]], ![[8, 25, 20, 30, 6], [17, 9, 18, 16, 1], [3, 14, 4, 7, 16], [27, 3, 10, 1, 30], [8, 9, 24, 28, 18]], ![[0, 1], [13, 19, 5, 19, 6], [18, 3, 16, 23, 28], [27, 14, 27, 19, 25], [8, 25, 20, 30, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 28, 12, 15], [], [], []]
 b := ![[], [28, 9, 4, 21, 26], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [15, 8, 28, 21, 25, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2042364445953, 457532996954, -19310187153, -224043715468, -408930951744]
  a := ![-49, -56, 48, -106, -199]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-65882724063, 14759128934, -622909263, -7227216628, -13191321024]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 28629151 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀

instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-177, -40, 22, -64, -104]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-177, -40, 22, -64, -104]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![17, 26, 19, 12, 1]] where
  M :=![![![-177, -40, 22, -64, -104], ![-440, -131, 48, -180, -200], ![-960, -380, 209, -460, -840], ![-124, 28, -8, -7, -16], ![-222, -148, 74, -148, -259]]]
  hmulB := by decide  
  f := ![![![-5, 0, -2, 8, 8]], ![![40, -7, -16, 20, 40]], ![![160, -20, -27, -20, 40]], ![![-12, 4, 16, -35, -48]], ![![105, -14, -21, -4, 37]]]
  g := ![![![43, 72, 54, 32, -104], ![80, 137, 104, 60, -200], ![360, 580, 437, 260, -840], ![4, 12, 8, 5, -16], ![113, 178, 135, 80, -259]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [32, 16, 30, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 29, 13, 27], [21, 33, 4, 12], [30, 11, 20, 35], [0, 1]]
 g := ![![[11, 23, 12, 27], [16, 5, 3], [9, 27, 27, 25], [1], []], ![[9, 12, 4, 24, 9, 11], [1, 10, 12], [8, 29, 32, 30, 6, 30], [23, 0, 4], [19, 17, 26]], ![[23, 6, 10, 24, 13, 11], [9, 0, 4], [9, 36, 33, 13, 35, 28], [10, 31, 3], [15, 5, 33]], ![[31, 12, 8, 26, 34, 6], [30, 0, 21], [29, 0, 20, 28, 31, 19], [32, 5, 30], [33, 11, 4]]]
 h' := ![![[18, 29, 13, 27], [33, 25, 30, 8], [8, 16, 13, 15], [5, 21, 7, 32], [0, 0, 1], [0, 1]], ![[21, 33, 4, 12], [14, 25, 4, 11], [3, 17, 5, 7], [0, 7, 15, 16], [12, 11, 5, 2], [18, 29, 13, 27]], ![[30, 11, 20, 35], [15, 28, 35, 2], [9, 26, 5, 2], [17, 10, 1, 29], [35, 24, 4, 15], [21, 33, 4, 12]], ![[0, 1], [1, 33, 5, 16], [6, 15, 14, 13], [2, 36, 14, 34], [29, 2, 27, 20], [30, 11, 20, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [35, 1, 28], []]
 b := ![[], [], [26, 15, 25, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [32, 16, 30, 5, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21445, 9286, 37291, 47388, -109123]
  a := ![-4, -4, 5, -9, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![49558, 76932, 57044, 36672, -109123]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 2, -8, -8]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![5, 0, 2, -8, -8]] 
 ![![37, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![5, 0, 2, -8, -8], ![-40, 7, 16, -20, -40], ![-160, 20, 27, 20, -40], ![12, -4, -16, 35, 48], ![-34, 4, 6, 4, -9]]]
  hmulB := by decide  
  f := ![![![177, 40, -22, 64, 104]], ![![98, 23, -12, 36, 56]], ![![69, 20, -11, 28, 48]], ![![166, 36, -20, 59, 96]], ![![6, 4, -2, 4, 7]]]
  g := ![![![7, 0, 2, -8, -8], ![10, 7, 16, -20, -40], ![-39, 20, 27, 20, -40], ![-26, -4, -16, 35, 48], ![-8, 4, 6, 4, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-177, -40, 22, -64, -104]] ![![5, 0, 2, -8, -8]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3014615, -864076, 405192, -1217538, -1753986]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-3014615, -864076, 405192, -1217538, -1753986]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![14, 26, 37, 1, 0], ![24, 12, 10, 0, 1]] where
  M :=![![![-3014615, -864076, 405192, -1217538, -1753986], ![-7697034, -2206193, 1034552, -3108666, -4478346], ![-19652370, -5632940, 2641459, -7937170, -11434290], ![-1169204, -335128, 157152, -472217, -680276], ![-5588562, -1601844, 751154, -2257100, -3251579]]]
  hmulB := by decide  
  f := ![![![-3, -4, 12, 14, -38]], ![![-86, 71, -84, 86, 226]], ![![850, -420, 39, -130, 10]], ![![712, -334, -13, -59, 134]], ![![186, -88, -8, 0, 49]]]
  g := ![![![1368941, 1264384, 1536438, -1217538, -1753986], ![3495234, 3228275, 3922894, -3108666, -4478346], ![8924170, 8242560, 10016089, -7937170, -11434290], ![530938, 490386, 595901, -472217, -680276], ![2537774, 2343944, 2848284, -2257100, -3251579]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [8, 2, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 8, 25], [24, 32, 16], [0, 1]]
 g := ![![[40, 9, 31], [35, 31], [11, 16], [38, 32, 1], []], ![[5, 16], [24, 36], [31, 37], [32, 18, 14, 16], [23, 10]], ![[27, 40, 9, 4], [6, 20], [38, 32], [33, 0, 28, 40], [32, 10]]]
 h' := ![![[8, 8, 25], [23, 40, 20], [37, 27, 21], [24, 37, 37], [0, 0, 1], [0, 1]], ![[24, 32, 16], [34, 32], [29, 12, 35], [21, 1, 18], [3, 2, 32], [8, 8, 25]], ![[0, 1], [3, 10, 21], [25, 2, 26], [1, 3, 27], [33, 39, 8], [24, 32, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 17], []]
 b := ![[], [0, 15, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [8, 2, 9, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4120776, -1597204, -519114, -353104, 3446458]
  a := ![36, 27, -39, 62, 143]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1796360, -823756, -534606, -353104, 3446458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -11, 5, -14, -20]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-31, -11, 5, -14, -20]] 
 ![![41, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![-31, -11, 5, -14, -20], ![-88, -20, 11, -32, -52], ![-220, -65, 24, -90, -100], ![-4, -9, 5, -7, -16], ![-70, -14, 4, -24, -21]]]
  hmulB := by decide  
  f := ![![![229, -27, -27, -56, 20]], ![![49, -5, -2, -22, -8]], ![![-51, 8, 17, -16, -40]], ![![47, -6, -8, -5, 12]], ![![122, -14, -12, -36, 3]]]
  g := ![![![17, -11, 5, -14, -20], ![41, -20, 11, -32, -52], ![91, -65, 24, -90, -100], ![13, -9, 5, -7, -16], ![20, -14, 4, -24, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-435, 51, 43, 130, -14]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-435, 51, 43, 130, -14]] 
 ![![41, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-435, 51, 43, 130, -14], ![218, -90, -353, 792, 1082], ![4830, -755, -1384, 1010, 3090], ![1020, -63, 107, -859, -660], ![1048, -174, -294, 216, 663]]]
  hmulB := by decide  
  f := ![![![207998685, 59618451, -27956937, 84006192, 121019366]], ![![170220237, 48790053, -22879166, 68748290, 99038824]], ![![149754145, 42923878, -20128335, 60482476, 87131088]], ![![144015476, 41279009, -19357005, 58164751, 83792172]], ![![55062949, 15782637, -7400967, 22238740, 32037141]]]
  g := ![![![-159, 51, 43, 130, -14], ![-507, -90, -353, 792, 1082], ![97, -755, -1384, 1010, 3090], ![744, -63, 107, -859, -660], ![29, -174, -294, 216, 663]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-3014615, -864076, 405192, -1217538, -1753986]] ![![-31, -11, 5, -14, -20]]
  ![![207998685, 59618451, -27956937, 84006192, 121019366]] where
 M := ![![![207998685, 59618451, -27956937, 84006192, 121019366]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![207998685, 59618451, -27956937, 84006192, 121019366]] ![![-435, 51, 43, 130, -14]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5598, -1361, -4188, 7882, 11933]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![5598, -1361, -4188, 7882, 11933]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![16, 30, 9, 26, 1]] where
  M :=![![![5598, -1361, -4188, 7882, 11933], ![51563, -7460, -13074, 5632, 27257], ![93035, -8175, 2901, -59330, -36715], ![-48662, 8551, 19847, -25057, -50078], ![20248, -1810, 532, -12634, -7657]]]
  hmulB := by decide  
  f := ![![![2461528, 705545, -330852, 994158, 1432185]], ![![6284871, 1801426, -844744, 2538324, 3656709]], ![![16046775, 4599475, -2156837, 6480950, 9336465]], ![![954694, 273641, -128319, 385579, 555466]], ![![9342717, 2677893, -1255747, 3773322, 5435850]]]
  g := ![![![-4310, -8357, -2595, -7032, 11933], ![-8943, -19190, -6009, -16350, 27257], ![15825, 25425, 7752, 20820, -36715], ![17502, 35137, 10943, 29697, -50078], ![3320, 5300, 1615, 4336, -7657]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [41, 20, 18, 13, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 14, 32, 16], [7, 10, 38, 9], [17, 18, 16, 18], [0, 1]]
 g := ![![[3, 15, 31, 4], [21, 11, 5, 14], [2, 28, 11], [30, 1], []], ![[41, 40, 20, 8, 39, 4], [13, 3, 13, 20, 18, 23], [3, 14, 23], [27, 14, 26, 32, 17, 36], [27, 18, 41]], ![[37, 14, 26, 17, 32, 17], [8, 7, 2, 10, 7, 13], [11, 37, 1], [22, 20, 18, 16, 24, 36], [18, 18, 38]], ![[0, 22, 15, 23, 33, 8], [1, 40, 41, 33, 10, 3], [15, 26, 16], [5, 34, 23, 1, 34, 26], [28, 19, 23]]]
 h' := ![![[6, 14, 32, 16], [42, 10, 33, 41], [35, 23, 10, 33], [17, 4, 42, 22], [0, 0, 1], [0, 1]], ![[7, 10, 38, 9], [40, 40, 24, 22], [17, 1, 41, 26], [21, 10, 29, 18], [4, 8, 31, 23], [6, 14, 32, 16]], ![[17, 18, 16, 18], [16, 26, 21, 8], [0, 0, 3, 21], [8, 36, 18, 42], [42, 31, 24, 41], [7, 10, 38, 9]], ![[0, 1], [0, 10, 8, 15], [28, 19, 32, 6], [27, 36, 40, 4], [1, 4, 30, 22], [17, 18, 16, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [36, 41, 1], []]
 b := ![[], [], [35, 42, 38, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [41, 20, 18, 13, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-52381745, 92440794, -17911204, 55013348, -46718342]
  a := ![-21, -9, 26, -28, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![16165389, 34743978, 9361718, 29527680, -46718342]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2461528, 705545, -330852, 994158, 1432185]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![2461528, 705545, -330852, 994158, 1432185]] 
 ![![43, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![2461528, 705545, -330852, 994158, 1432185], ![6284871, 1801426, -844744, 2538324, 3656709], ![16046775, 4599475, -2156837, 6480950, 9336465], ![954694, 273641, -128319, 385579, 555466], ![4563234, 1307958, -613342, 1842994, 2655019]]]
  hmulB := by decide  
  f := ![![![5598, -1361, -4188, 7882, 11933]], ![![2501, -490, -1278, 1964, 3409]], ![![5939, -1108, -2757, 3936, 7194]], ![![40, -86, -415, 1067, 1333]], ![![1252, -232, -572, 806, 1487]]]
  g := ![![![-291622, 705545, -330852, 994158, 1432185], ![-744581, 1801426, -844744, 2538324, 3656709], ![-1901094, 4599475, -2156837, 6480950, 9336465], ![-113104, 273641, -128319, 385579, 555466], ![-540616, 1307958, -613342, 1842994, 2655019]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![5598, -1361, -4188, 7882, 11933]] ![![2461528, 705545, -330852, 994158, 1432185]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1336, -467, 226, -598, -917]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-1336, -467, 226, -598, -917]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![44, 21, 13, 1, 0], ![9, 23, 27, 0, 1]] where
  M :=![![![-1336, -467, 226, -598, -917], ![-3947, -804, 410, -1368, -2033], ![-8835, -3265, 1267, -4070, -4845], ![-294, -255, 205, -239, -786], ![-2730, -850, 250, -1146, -983]]]
  hmulB := by decide  
  f := ![![![722, -161, -466, 822, 1299]], ![![5541, -786, -1328, 404, 2679]], ![![8845, -695, 681, -6710, -4805]], ![![5480, -674, -796, -959, 972]], ![![7972, -818, -345, -3530, -1222]]]
  g := ![![![707, 706, 697, -598, -917], ![1586, 1589, 1555, -1368, -2033], ![4550, 4120, 3936, -4070, -4845], ![368, 486, 522, -239, -786], ![1203, 975, 887, -1146, -983]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [29, 3, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 14, 10], [22, 32, 37], [0, 1]]
 g := ![![[42, 9, 16], [29, 17, 3], [38, 26, 1], [15, 26, 1], []], ![[39, 23, 31, 20], [22, 44, 21, 13], [27, 15, 18, 41], [5, 34, 18, 41], [13, 6]], ![[24, 15, 31, 12], [38, 33, 18, 1], [29, 45, 23, 14], [43, 22, 23, 14], [33, 6]]]
 h' := ![![[4, 14, 10], [5, 2, 4], [26, 28, 35], [35, 0, 1], [0, 0, 1], [0, 1]], ![[22, 32, 37], [26, 0, 7], [5, 6, 37], [3, 40, 32], [15, 40, 32], [4, 14, 10]], ![[0, 1], [37, 45, 36], [20, 13, 22], [32, 7, 14], [44, 7, 14], [22, 32, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 30], []]
 b := ![[], [14, 3, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [29, 3, 21, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![963545, -718572, 261138, -260106, -393936]
  a := ![12, -4, -14, -2, 48]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![339439, 293706, 303804, -260106, -393936]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2596, 780, 2681, -5596, -7931]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-2596, 780, 2681, -5596, -7931]] 
 ![![47, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-2596, 780, 2681, -5596, -7931], ![-34985, 5213, 9637, -5840, -20975], ![-74605, 7360, 1758, 36900, 16205], ![29734, -5498, -13532, 18989, 35146], ![-16178, 1608, 444, 7838, 3311]]]
  hmulB := by decide  
  f := ![![![-307407914, -88112020, 41318451, -124155442, -178858387]], ![![-23240297, -6661343, 3123710, -9386256, -13521846]], ![![-343505667, -98458680, 46170320, -138734546, -199861051]], ![![-61402084, -17599618, 8253005, -24798981, -35725423]], ![![-57909262, -16598472, 7783537, -23388304, -33693202]]]
  g := ![![![-443, 780, 2681, -5596, -7931], ![-6045, 5213, 9637, -5840, -20975], ![-12944, 7360, 1758, 36900, 16205], ![5123, -5498, -13532, 18989, 35146], ![-2807, 1608, 444, 7838, 3311]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-102917, -29499, 13833, -41566, -59880]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-102917, -29499, 13833, -41566, -59880]] 
 ![![47, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-102917, -29499, 13833, -41566, -59880], ![-262772, -75318, 35319, -106128, -152888], ![-670920, -192305, 90178, -270970, -390360], ![-39916, -11441, 5365, -16121, -23224], ![-190790, -54686, 25644, -77056, -111007]]]
  hmulB := by decide  
  f := ![![![185, -77, -1, -68, 24]], ![![38, -14, 3, -18, -8]], ![![115, -56, -1, -64, 32]], ![![7, -8, 2, 1, 0]], ![![-15, 7, -3, 0, 9]]]
  g := ![![![-5822, -29499, 13833, -41566, -59880], ![-14865, -75318, 35319, -106128, -152888], ![-37954, -192305, 90178, -270970, -390360], ![-2258, -11441, 5365, -16121, -23224], ![-10793, -54686, 25644, -77056, -111007]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-1336, -467, 226, -598, -917]] ![![-2596, 780, 2681, -5596, -7931]]
  ![![-185, 77, 1, 68, -24]] where
 M := ![![![-185, 77, 1, 68, -24]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-185, 77, 1, 68, -24]] ![![-102917, -29499, 13833, -41566, -59880]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1704, 236, 361, 8, -677]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-1704, 236, 361, 8, -677]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![17, 2, 8, 36, 1]] where
  M :=![![![-1704, 236, 361, 8, -677], ![-2015, 109, -465, 2280, 2095], ![10845, -2060, -4636, 6380, 11955], ![5870, -650, -692, -1471, 470], ![2352, -484, -982, 1358, 2567]]]
  hmulB := by decide  
  f := ![![![-219754, -62988, 29537, -88754, -127859]], ![![-561085, -160823, 75415, -226610, -326455]], ![![-1432585, -410620, 192552, -578590, -833515]], ![![-85230, -24430, 11456, -34423, -49590]], ![![-373478, -107050, 50199, -150840, -217300]]]
  g := ![![![185, 30, 109, 460, -677], ![-710, -77, -325, -1380, 2095], ![-3630, -490, -1892, -8000, 11955], ![-40, -30, -84, -347, 470], ![-779, -106, -406, -1718, 2567]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [12, 1, 16, 36, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 27, 47, 16], [35, 51, 22, 23], [24, 27, 37, 14], [0, 1]]
 g := ![![[30, 2, 26, 17], [18, 12, 24], [41, 19, 48, 7], [8, 17, 1], []], ![[28, 42, 25, 32, 23, 1], [14, 28, 15], [6, 2, 23, 22, 8, 28], [28, 33, 37], [8, 12, 0, 4, 46, 15]], ![[36, 2, 12, 23, 5, 22], [46, 22, 1], [11, 30, 0, 50], [8, 7, 1], [28, 35, 37, 31, 20, 30]], ![[32, 23, 16, 50, 9, 5], [50, 26, 46], [39, 40, 33, 10, 37, 51], [31, 28, 44], [42, 24, 16, 50, 34, 41]]]
 h' := ![![[11, 27, 47, 16], [9, 32, 48, 21], [38, 43, 21, 36], [10, 0, 2, 22], [0, 0, 0, 1], [0, 1]], ![[35, 51, 22, 23], [0, 4, 48, 40], [50, 47, 32, 42], [26, 43, 8, 42], [16, 3, 9, 14], [11, 27, 47, 16]], ![[24, 27, 37, 14], [40, 47, 16, 17], [50, 20, 24, 52], [39, 29, 49], [33, 46, 48, 1], [35, 51, 22, 23]], ![[0, 1], [49, 23, 47, 28], [38, 49, 29, 29], [23, 34, 47, 42], [17, 4, 49, 37], [24, 27, 37, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [35, 24, 35], []]
 b := ![[], [], [38, 44, 36, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [12, 1, 16, 36, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16534189, 69954091, -18290192, 45104652, 65943223]
  a := ![24, 19, -20, 44, 83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20839634, -1168535, -10298792, -43940592, 65943223]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-219754, -62988, 29537, -88754, -127859]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-219754, -62988, 29537, -88754, -127859]] 
 ![![53, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![-219754, -62988, 29537, -88754, -127859], ![-561085, -160823, 75415, -226610, -326455], ![-1432585, -410620, 192552, -578590, -833515], ![-85230, -24430, 11456, -34423, -49590], ![-407386, -116768, 54756, -164534, -237027]]]
  hmulB := by decide  
  f := ![![![-1704, 236, 361, 8, -677]], ![![-1099, 149, 216, 48, -382]], ![![-567, 68, 76, 124, -81]], ![![-50, 10, 21, -27, -55]], ![![-888, 120, 179, 30, -322]]]
  g := ![![![100031, -62988, 29537, -88754, -127859], ![255403, -160823, 75415, -226610, -326455], ![652104, -410620, 192552, -578590, -833515], ![38797, -24430, 11456, -34423, -49590], ![185439, -116768, 54756, -164534, -237027]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-1704, 236, 361, 8, -677]] ![![-219754, -62988, 29537, -88754, -127859]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2970584, -851457, 399274, -1199756, -1728367]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-2970584, -851457, 399274, -1199756, -1728367]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![39, 21, 58, 8, 1]] where
  M :=![![![-2970584, -851457, 399274, -1199756, -1728367], ![-7584613, -2173970, 1019444, -3063262, -4412947], ![-19365365, -5550655, 2602869, -7821240, -11267255], ![-1152118, -330241, 154859, -465323, -670342], ![-5506954, -1578438, 740178, -2224130, -3204077]]]
  hmulB := by decide  
  f := ![![![110, -23, -66, 112, 181]], ![![767, -108, -178, 38, 353]], ![![1135, -85, 131, -960, -755]], ![![-802, 137, 293, -327, -718]], ![![1357, -119, 62, -904, -597]]]
  g := ![![![1092131, 600750, 1705840, 214020, -1728367], ![2788480, 1533863, 4355430, 546446, -4412947], ![7119620, 3916300, 11120401, 1395200, -11267255], ![423580, 232999, 661605, 83007, -670342], ![2024611, 1113681, 3162316, 396754, -3204077]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [20, 51, 5, 16, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 26, 23, 48], [20, 16, 17, 36], [46, 16, 19, 34], [0, 1]]
 g := ![![[10, 13, 11, 57], [54, 18, 3, 16], [28, 18, 27], [25, 15, 43, 1], []], ![[45, 27, 12, 16, 52, 22], [29, 11, 14, 28, 3, 45], [58, 49, 12], [42, 52, 46, 48, 14, 28], [51, 15, 3, 33, 27, 26]], ![[7, 33, 52, 46, 16, 57], [55, 25, 13, 13, 55, 17], [11, 43, 1], [25, 16, 26, 43, 41, 7], [40, 49, 21, 44, 47, 46]], ![[3, 55, 19, 37, 31, 2], [39, 12, 50, 3, 5, 43], [17, 56, 26], [55, 41, 56, 41, 10, 23], [42, 49, 27, 6, 6, 10]]]
 h' := ![![[36, 26, 23, 48], [41, 39, 12, 36], [47, 36, 25, 4], [31, 18, 20, 26], [0, 0, 0, 1], [0, 1]], ![[20, 16, 17, 36], [45, 36, 41, 36], [45, 35, 7, 22], [54, 57, 39, 22], [29, 11, 46, 25], [36, 26, 23, 48]], ![[46, 16, 19, 34], [33, 30, 57, 6], [6, 26, 37, 44], [52, 2, 0, 58], [2, 14, 14, 46], [20, 16, 17, 36]], ![[0, 1], [3, 13, 8, 40], [12, 21, 49, 48], [36, 41, 0, 12], [31, 34, 58, 46], [46, 16, 19, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [26, 40, 2], []]
 b := ![[], [], [36, 26, 40, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [20, 51, 5, 16, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![48180, -12829, -19893, 22028, 54113]
  a := ![0, -3, -1, -4, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-34953, -19478, -53533, -6964, 54113]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![110, -23, -66, 112, 181]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![110, -23, -66, 112, 181]] 
 ![![59, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![110, -23, -66, 112, 181], ![767, -108, -178, 38, 353], ![1135, -85, 131, -960, -755], ![-802, 137, 293, -327, -718], ![252, -22, 28, -206, -161]]]
  hmulB := by decide  
  f := ![![![-2970584, -851457, 399274, -1199756, -1728367]], ![![-2998439, -859441, 403018, -1211006, -1744574]], ![![-3097415, -887810, 416321, -1250980, -1802160]], ![![-623714, -178775, 83833, -251905, -362894]], ![![-1452758, -416403, 195264, -586738, -845254]]]
  g := ![![![-20, -23, -66, 112, 181], ![114, -108, -178, 38, 353], ![520, -85, 131, -960, -755], ![-24, 137, 293, -327, -718], ![115, -22, 28, -206, -161]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-2970584, -851457, 399274, -1199756, -1728367]] ![![110, -23, -66, 112, 181]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, -14, -6, -72, -26]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![167, -14, -6, -72, -26]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![10, 24, 19, 45, 1]] where
  M :=![![![167, -14, -6, -72, -26], ![-222, 65, 176, -328, -498], ![-2150, 330, 551, -220, -1130], ![-272, 6, -102, 423, 412], ![-458, 72, 118, -48, -241]]]
  hmulB := by decide  
  f := ![![![7, -2, 2, 0, -6]], ![![-18, 17, -8, 8, 18]], ![![70, -50, 11, -20, 10]], ![![8, 2, 6, 3, -28]], ![![22, -8, 5, -1, -11]]]
  g := ![![![7, 10, 8, 18, -26], ![78, 197, 158, 362, -498], ![150, 450, 361, 830, -1130], ![-72, -162, -130, -297, 412], ![32, 96, 77, 177, -241]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [38, 37, 3, 22, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 23, 26, 14], [46, 20, 18, 55], [23, 17, 17, 53], [0, 1]]
 g := ![![[4, 54, 28, 45], [44, 3, 57], [53, 52, 51, 16], [0, 54, 39, 1], []], ![[14, 17, 34, 15, 56, 47], [10, 9, 4], [48, 1, 12, 60, 41, 46], [37, 14, 37, 28, 52, 1], [35, 19, 50, 34, 60, 60]], ![[36, 49, 10, 18, 8, 44], [2, 3, 46], [16, 46, 57, 48, 16, 50], [29, 3, 28, 50, 30, 32], [43, 14, 51, 29, 47, 28]], ![[19, 48, 15, 51, 9, 18], [42, 4, 49], [17, 35, 5, 51, 42, 55], [0, 14, 48, 29, 52, 17], [37, 31, 18, 23, 10, 37]]]
 h' := ![![[31, 23, 26, 14], [37, 32, 12, 17], [60, 28, 5, 22], [0, 22, 58, 4], [0, 0, 0, 1], [0, 1]], ![[46, 20, 18, 55], [34, 53, 6, 11], [29, 50, 9, 2], [30, 35, 44, 16], [35, 59, 57, 29], [31, 23, 26, 14]], ![[23, 17, 17, 53], [47, 49, 40, 47], [60, 34, 22, 30], [54, 20, 39, 45], [54, 31, 44, 25], [46, 20, 18, 55]], ![[0, 1], [46, 49, 3, 47], [42, 10, 25, 7], [40, 45, 42, 57], [25, 32, 21, 6], [23, 17, 17, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 45, 53], []]
 b := ![[], [], [38, 33, 25, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [38, 37, 3, 22, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-340547393, 223265505, -136983197, 90424804, 357816599]
  a := ![23, 9, -23, 28, 89]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-64241203, -137120211, -113696698, -262480691, 357816599]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -2, 2, 0, -6]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![7, -2, 2, 0, -6]] 
 ![![61, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![7, -2, 2, 0, -6], ![-18, 17, -8, 8, 18], ![70, -50, 11, -20, 10], ![8, 2, 6, 3, -28], ![14, -16, -2, -8, 27]]]
  hmulB := by decide  
  f := ![![![167, -14, -6, -72, -26]], ![![21, -1, 2, -16, -12]], ![![77, -4, 5, -52, -36]], ![![116, -10, -6, -45, -12]], ![![102, -8, -2, -48, -21]]]
  g := ![![![3, -2, 2, 0, -6], ![-15, 17, -8, 8, 18], ![9, -50, 11, -20, 10], ![12, 2, 6, 3, -28], ![-8, -16, -2, -8, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![167, -14, -6, -72, -26]] ![![7, -2, 2, 0, -6]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB397I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB397I1 : PrimesBelowBoundCertificateInterval O 23 61 397 where
  m := 9
  g := ![4, 1, 2, 3, 2, 3, 2, 2, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB397I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2, I29N3]
    · exact ![I31N0]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
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
    · exact ![841, 29, 29, 29]
    · exact ![28629151]
    · exact ![1874161, 37]
    · exact ![68921, 41, 41]
    · exact ![3418801, 43]
    · exact ![103823, 47, 47]
    · exact ![7890481, 53]
    · exact ![12117361, 59]
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
      exact NI29N2
      exact NI29N3
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
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
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I29N1, I29N2, I29N3, I37N1, I41N1, I41N2, I43N1, I47N1, I47N2, I53N1, I59N1, I61N1]
  Il := ![[I29N1, I29N2, I29N3], [], [I37N1], [I41N1, I41N2], [I43N1], [I47N1, I47N2], [I53N1], [I59N1], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
