
import IdealArithmetic.Examples.NF5_3_112500000_1.RI5_3_112500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![316, 87, -136, -66, 63]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![316, 87, -136, -66, 63]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![11, 3, 27, 1, 0], ![17, 28, 16, 0, 1]] where
  M :=![![![316, 87, -136, -66, 63], ![1240, 953, 28, -432, -132], ![-1556, -204, 849, 252, -432], ![-825, -809, -162, 343, 185], ![613, -613, -962, 100, 594]]]
  hmulB := by decide  
  f := ![![![-618, -21, -34, -144, 81]], ![![1876, 1, 52, 408, -288]], ![![-3404, -180, -235, -828, 408]], ![![-3099, -175, -223, -759, 364]], ![![-549, -120, -110, -178, 7]]]
  g := ![![![-1, -51, 22, -66, 63], ![284, 205, 476, -432, -132], ![104, 384, 33, 252, -432], ![-267, -242, -427, 343, 185], ![-365, -605, -454, 100, 594]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [16, 12, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 5, 3], [11, 23, 26], [0, 1]]
 g := ![![[24, 7, 7], [12, 6], [15, 26, 16], [1]], ![[25, 27, 10, 17], [4, 22], [12, 27, 8, 12], [14, 17, 11, 27]], ![[14, 8, 11, 26], [1, 7], [1, 4, 12, 17], [4, 0, 20, 2]]]
 h' := ![![[22, 5, 3], [17, 9, 23], [21, 8, 21], [13, 17, 4], [0, 1]], ![[11, 23, 26], [22, 20, 5], [17, 26, 14], [13, 5, 27], [22, 5, 3]], ![[0, 1], [9, 0, 1], [5, 24, 23], [20, 7, 27], [11, 23, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 10], []]
 b := ![[], [22, 22, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [16, 12, 25, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13621510, -7009399, -6197954, -6614612, -2532216]
  a := ![-9, -7, -7, -10, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3523686, 2887465, 7341794, -6614612, -2532216]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-618, -21, -34, -144, 81]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-618, -21, -34, -144, 81]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![16, 7, 1, 0, 0], ![6, 8, 0, 1, 0], ![23, 28, 0, 0, 1]] where
  M :=![![![-618, -21, -34, -144, 81], ![1876, 1, 52, 408, -288], ![-3404, -180, -235, -828, 408], ![3207, 13, 96, 705, -487], ![-3479, -271, -308, -890, 362]]]
  hmulB := by decide  
  f := ![![![316, 87, -136, -66, 63]], ![![1240, 953, 28, -432, -132]], ![![420, 271, -39, -132, -12]], ![![379, 253, -26, -121, -17]], ![![1469, 968, -114, -466, -57]]]
  g := ![![![-37, -31, -34, -144, 81], ![180, 153, 52, 408, -288], ![-140, -115, -235, -828, 408], ![298, 253, 96, 705, -487], ![-53, -39, -308, -890, 362]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [5, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 28], [0, 1]]
 g := ![![[21, 6], [23], [], [11, 1]], ![[0, 23], [23], [], [22, 28]]]
 h' := ![![[11, 28], [1, 21], [0, 9], [3], [0, 1]], ![[0, 1], [0, 8], [12, 20], [3], [11, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [7, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [5, 18, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![748510, 428049, 407171, 434704, 202962]
  a := ![-53, -53, -57, -58, -104]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-449744, -399404, 407171, 434704, 202962]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![316, 87, -136, -66, 63]] ![![-618, -21, -34, -144, 81]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42, 24, 20, 20, 9]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![42, 24, 20, 20, 9]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![30, 2, 8, 1, 0], ![0, 12, 12, 0, 1]] where
  M :=![![![42, 24, 20, 20, 9], ![256, 123, 106, 116, 40], ![586, 313, 269, 282, 116], ![387, 182, 154, 171, 59], ![1121, 588, 496, 522, 210]]]
  hmulB := by decide  
  f := ![![![64, -4, 4, 10, -7]], ![![-160, 7, -14, -24, 20]], ![![226, 5, 13, 22, -24]], ![![103, -2, 6, 13, -11]], ![![29, 4, 0, 0, -2]]]
  g := ![![![-18, -4, -8, 20, 9], ![-104, -19, -42, 116, 40], ![-254, -53, -109, 282, 116], ![-153, -28, -62, 171, 59], ![-469, -96, -200, 522, 210]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [21, 19, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 16, 14], [6, 14, 17], [0, 1]]
 g := ![![[0, 4, 20], [30, 20, 8], [4, 19, 5], [1]], ![[13, 16, 20, 2], [19, 17, 1, 10], [29, 19, 18, 7], [11, 16, 18, 16]], ![[20, 17, 7, 13], [16, 29, 28, 29], [17, 10, 12, 26], [25, 24, 14, 15]]]
 h' := ![![[0, 16, 14], [21, 21, 12], [9, 28, 15], [10, 12, 6], [0, 1]], ![[6, 14, 17], [4, 9, 28], [11, 16, 13], [17, 13, 4], [0, 16, 14]], ![[0, 1], [16, 1, 22], [21, 18, 3], [1, 6, 21], [6, 14, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 30], []]
 b := ![[], [10, 20, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [21, 19, 25, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1287860, -661542, -572596, -606364, -229818]
  a := ![-4, -3, -4, -6, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![545260, 106742, 226972, -606364, -229818]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![64, -4, 4, 10, -7]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![64, -4, 4, 10, -7]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![17, 8, 1, 0, 0], ![1, 20, 0, 1, 0], ![2, 16, 0, 0, 1]] where
  M :=![![![64, -4, 4, 10, -7], ![-160, 7, -14, -24, 20], ![226, 5, 13, 22, -24], ![-215, 4, -10, -25, 21], ![107, -20, 12, 24, -14]]]
  hmulB := by decide  
  f := ![![![42, 24, 20, 20, 9]], ![![256, 123, 106, 116, 40]], ![![108, 55, 47, 50, 19]], ![![179, 86, 74, 81, 28]], ![![171, 84, 72, 78, 28]]]
  g := ![![![0, -4, 4, 10, -7], ![2, 9, -14, -24, 20], ![1, -5, 13, 22, -24], ![-2, 8, -10, -25, 21], ![-3, -12, 12, 24, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [30, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 30], [0, 1]]
 g := ![![[7, 2], [14, 9], [3, 20], [7, 1]], ![[21, 29], [15, 22], [19, 11], [14, 30]]]
 h' := ![![[7, 30], [14, 23], [3, 28], [7, 19], [0, 1]], ![[0, 1], [20, 8], [13, 3], [16, 12], [7, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [13, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [30, 24, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![203047, 125335, 116802, 124181, 69275]
  a := ![28, 32, 24, 19, 64]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-65978, -141971, 116802, 124181, 69275]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![42, 24, 20, 20, 9]] ![![64, -4, 4, 10, -7]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![88, -5, 4, 14, -9]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![88, -5, 4, 14, -9]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![11, 15, 1, 0, 0], ![28, 8, 0, 1, 0], ![14, 32, 0, 0, 1]] where
  M :=![![![88, -5, 4, 14, -9], ![-208, 17, -20, -40, 28], ![316, 12, 25, 36, -40], ![-321, -5, -14, -37, 33], ![165, -37, 10, 44, -18]]]
  hmulB := by decide  
  f := ![![![58, -9, -6, 8, -15]], ![![-372, -63, -60, -112, 16]], ![![-130, -32, -29, -44, -1]], ![![-53, -23, -20, -23, -7]], ![![-303, -65, -60, -98, 4]]]
  g := ![![![-6, 3, 4, 14, -9], ![20, -7, -20, -40, 28], ![-11, 17, 25, 36, -40], ![11, -15, -14, -37, 33], ![-25, 1, 10, 44, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [12, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 36], [0, 1]]
 g := ![![[1, 34], [12], [8, 9], [33], [1]], ![[0, 3], [12], [11, 28], [33], [1]]]
 h' := ![![[25, 36], [7, 16], [15, 30], [7, 3], [25, 25], [0, 1]], ![[0, 1], [0, 21], [25, 7], [8, 34], [21, 12], [25, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [23, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [12, 12, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36604, 6096, -1652, -17316, 6612]
  a := ![-12, 18, -14, -54, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10104, -1140, -1652, -17316, 6612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-187, 7, -12, -24, 20]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-187, 7, -12, -24, 20]] 
 ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![-187, 7, -12, -24, 20], ![456, -19, 30, 56, -48], ![-546, 25, -37, -62, 56], ![532, -25, 36, 59, -54], ![-308, 19, -22, -28, 29]]]
  hmulB := by decide  
  f := ![![![-75, -37, -18, -20, -12]], ![![-27, -14, -8, -8, -4]], ![![-47, -24, -17, -18, -8]], ![![-84, -41, -22, -25, -14]], ![![-112, -55, -32, -36, -19]]]
  g := ![![![2, 7, -12, -24, 20], ![-3, -19, 30, 56, -48], ![0, 25, -37, -62, 56], ![1, -25, 36, 59, -54], ![-5, 19, -22, -28, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-193, 2, -14, -30, 20]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-193, 2, -14, -30, 20]] 
 ![![37, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-193, 2, -14, -30, 20], ![452, -29, 16, 56, -60], ![-704, -24, -73, -128, 56], ![574, -40, 18, 69, -78], ![-570, -64, -90, -130, 21]]]
  hmulB := by decide  
  f := ![![![143, -10, 34, 58, -40]], ![![30, -9, 12, 20, -12]], ![![87, -2, 9, 26, -16]], ![![-7, 2, 4, -1, -2]], ![![26, 4, 6, 6, -7]]]
  g := ![![![3, 2, -14, -30, 20], ![10, -29, 16, 56, -60], ![33, -24, -73, -128, 56], ![15, -40, 18, 69, -78], ![58, -64, -90, -130, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2

def I37N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -2, 4, 2, -2]] i)))

def SI37N3: IdealEqSpanCertificate' Table ![![-9, -2, 4, 2, -2]] 
 ![![37, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-9, -2, 4, 2, -2], ![-40, -29, 0, 12, 4], ![48, 4, -25, -4, 12], ![20, 24, 4, -13, -4], ![-4, 22, 28, -2, -19]]]
  hmulB := by decide  
  f := ![![![483, 262, 220, 234, 94]], ![![347, 185, 156, 166, 66]], ![![444, 236, 199, 212, 84]], ![![524, 280, 236, 251, 100]], ![![340, 174, 148, 158, 61]]]
  g := ![![![-3, -2, 4, 2, -2], ![5, -29, 0, 12, 4], ![16, 4, -25, -4, 12], ![-4, 24, 4, -13, -4], ![-26, 22, 28, -2, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N3 : Nat.card (O ⧸ I37N3) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N3)

lemma isPrimeI37N3 : Ideal.IsPrime I37N3 := prime_ideal_of_norm_prime hp37.out _ NI37N3
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![88, -5, 4, 14, -9]] ![![-187, 7, -12, -24, 20]]
  ![![-10700, 290, -652, -1562, 1207]] where
 M := ![![![-10700, 290, -652, -1562, 1207]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-10700, 290, -652, -1562, 1207]] ![![-193, 2, -14, -30, 20]]
  ![![1070610, -28930, 65290, 156008, -120729]] where
 M := ![![![1070610, -28930, 65290, 156008, -120729]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N2 : IdealMulLeCertificate' Table 
  ![![1070610, -28930, 65290, 156008, -120729]] ![![-9, -2, 4, 2, -2]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-1741294, 47064, -106190, -253746, 196359]]]
 hmul := by decide  
 g := ![![![![-47062, 1272, -2870, -6858, 5307]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2, I37N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
    exact isPrimeI37N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1 ⊙ MulI37N2)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1059, 27, -64, -156, 120]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-1059, 27, -64, -156, 120]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![37, 27, 34, 1, 0], ![28, 22, 30, 0, 1]] where
  M :=![![![-1059, 27, -64, -156, 120], ![2752, -71, 166, 408, -312], ![-3578, 93, -217, -534, 408], ![3564, -89, 216, 531, -406], ![-2468, 59, -146, -368, 281]]]
  hmulB := by decide  
  f := ![![![1, 3, 2, 0, 0]], ![![4, -1, 10, 12, 0]], ![![10, 3, 9, 18, 12]], ![![13, 5, 16, 23, 10]], ![![12, 5, 14, 20, 9]]]
  g := ![![![33, 39, 40, -156, 120], ![-88, -103, -106, 408, -312], ![116, 135, 139, -534, 408], ![-115, -134, -138, 531, -406], ![80, 93, 96, -368, 281]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [14, 13, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 35, 36], [34, 5, 5], [0, 1]]
 g := ![![[14, 12, 5], [22, 32], [12, 2], [32, 2, 1], []], ![[24, 9, 16, 10], [27, 10], [11, 9], [26, 8, 28, 39], [28, 25]], ![[5, 20, 18, 10], [37, 39], [10, 32], [33, 37, 10, 16], [18, 25]]]
 h' := ![![[9, 35, 36], [4, 19, 13], [5, 22, 27], [3, 7, 24], [0, 0, 1], [0, 1]], ![[34, 5, 5], [27, 24, 11], [6, 19, 25], [23, 33, 3], [17, 39, 5], [9, 35, 36]], ![[0, 1], [20, 39, 17], [28, 0, 30], [2, 1, 14], [2, 2, 35], [34, 5, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 33], []]
 b := ![[], [5, 2, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [14, 13, 39, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![349085221, 179728340, 159281909, 168916191, 63503613]
  a := ![34, 13, 25, 47, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-187290610, -140928983, -182657975, 168916191, 63503613]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 6, 12, 62, -38]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![271, 6, 12, 62, -38]] 
 ![![41, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![271, 6, 12, 62, -38], ![-888, -21, -40, -204, 124], ![1448, 32, 63, 332, -204], ![-1516, -36, -68, -349, 212], ![1404, 30, 60, 322, -199]]]
  hmulB := by decide  
  f := ![![![-25, 6, 36, 6, -22]], ![![-16, -5, 8, 4, -4]], ![![-1, -2, 3, 2, -2]], ![![-2, 8, 12, -1, -8]], ![![-16, 14, 36, 2, -23]]]
  g := ![![![15, 6, 12, 62, -38], ![-48, -21, -40, -204, 124], ![81, 32, 63, 332, -204], ![-82, -36, -68, -349, 212], ![80, 30, 60, 322, -199]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-56, -1, -4, -14, 9]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-56, -1, -4, -14, 9]] 
 ![![41, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![-56, -1, -4, -14, 9], ![208, 15, 8, 40, -28], ![-328, -6, -5, -72, 40], ![321, -1, 14, 81, -45], ![-309, -17, -22, -68, 50]]]
  hmulB := by decide  
  f := ![![![-26410, 715, -1610, -3848, 2979]], ![![-21524, 583, -1312, -3136, 2428]], ![![-7304, 198, -445, -1064, 824]], ![![-13323, 361, -812, -1941, 1503]], ![![-17559, 476, -1070, -2558, 1981]]]
  g := ![![![3, -1, -4, -14, 9], ![-16, 15, 8, 40, -28], ![16, -6, -5, -72, 40], ![-14, -1, 14, 81, -45], ![21, -17, -22, -68, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-1059, 27, -64, -156, 120]] ![![271, 6, 12, 62, -38]]
  ![![1339, 247, -12, 670, -306]] where
 M := ![![![1339, 247, -12, 670, -306]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![1339, 247, -12, 670, -306]] ![![-56, -1, -4, -14, 9]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![289952, 6970, 12792, 67076, -40795]]]
 hmul := by decide  
 g := ![![![![7072, 170, 312, 1636, -995]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [2, 39, 35, 42, 21, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 28, 0, 36, 27], [22, 36, 30, 0, 31], [5, 36, 25, 31, 36], [27, 28, 31, 19, 35], [0, 1]]
 g := ![![[16, 26, 20, 10, 16], [41, 30, 27, 16, 9], [24, 34, 28, 11], [1], []], ![[9, 18, 39, 13, 10, 38, 16, 37], [32, 15, 27, 4, 28, 31, 18, 42], [12, 8, 38, 6], [21, 21, 29, 29, 37, 1, 14, 18], [3, 8, 8, 41]], ![[32, 37, 29, 9, 6, 37, 17, 16], [15, 6, 17, 2, 34, 24, 11, 10], [36, 30, 25, 1], [24, 23, 15, 21, 10, 3, 30, 21], [4, 19, 29, 15]], ![[5, 19, 11, 28, 23, 2, 3, 11], [13, 28, 34, 25, 30, 21, 8, 6], [1, 1, 33, 6], [23, 0, 41, 23, 16, 29, 22, 10], [36, 36, 42, 6]], ![[11, 10, 15, 24, 30, 10, 10, 38], [2, 31, 9, 31, 36, 2, 31, 36], [40, 26, 5, 38], [41, 11, 2, 37, 36, 14, 23, 1], [28, 8, 29, 21]]]
 h' := ![![[11, 28, 0, 36, 27], [4, 19, 26, 32, 39], [42, 12, 41, 16, 40], [41, 4, 8, 1, 22], [0, 0, 1], [0, 1]], ![[22, 36, 30, 0, 31], [17, 21, 35, 12, 9], [25, 18, 1, 41, 32], [7, 42, 27, 19, 36], [29, 10, 7, 35, 31], [11, 28, 0, 36, 27]], ![[5, 36, 25, 31, 36], [3, 15, 40, 11, 20], [25, 12, 4, 1, 32], [21, 29, 34, 23, 1], [3, 14, 0, 37, 40], [22, 36, 30, 0, 31]], ![[27, 28, 31, 19, 35], [4, 19, 0, 1, 25], [36, 39, 17, 25, 6], [34, 29, 38, 4, 36], [39, 2, 2, 10, 19], [5, 36, 25, 31, 36]], ![[0, 1], [41, 12, 28, 30, 36], [4, 5, 23, 3, 19], [16, 25, 22, 39, 34], [28, 17, 33, 4, 39], [27, 28, 31, 19, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 39, 36, 42], [], [], []]
 b := ![[], [18, 38, 3, 27, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [2, 39, 35, 42, 21, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8381717982, -4280289316, -3654248446, -3898140146, -1504467058]
  a := ![-4, 0, -4, -9, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-194923674, -99541612, -84982522, -90654422, -34987606]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 0, 2, -2, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-17, 0, 2, -2, 0]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![32, 0, 46, 1, 0], ![33, 17, 42, 0, 1]] where
  M :=![![![-17, 0, 2, -2, 0], ![4, -21, 4, 16, -4], ![-44, -10, -21, -12, 16], ![78, 18, 2, 1, -10], ![-42, 22, 10, -22, -7]]]
  hmulB := by decide  
  f := ![![![-35, 0, -2, -6, 4]], ![![92, -3, 4, 16, -12]], ![![-140, -2, -11, -28, 16]], ![![-158, -2, -12, -31, 18]], ![![-119, -3, -10, -24, 13]]]
  g := ![![![1, 0, 2, -2, 0], ![-8, 1, -12, 16, -4], ![-4, -6, -3, -12, 16], ![8, 4, 8, 1, -10], ![19, 3, 28, -22, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [38, 26, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 12, 18], [34, 34, 29], [0, 1]]
 g := ![![[17, 16, 3], [38, 43, 9], [9, 0, 28], [22, 46, 1], []], ![[19, 4, 34, 16], [4, 29, 31, 28], [14, 27, 16, 27], [25, 46, 13, 34], [14, 42]], ![[23, 8, 18, 19], [29, 43, 13, 5], [43, 19, 39, 23], [20, 44, 7, 40], [3, 42]]]
 h' := ![![[12, 12, 18], [13, 38, 12], [34, 7, 44], [10, 30, 13], [0, 0, 1], [0, 1]], ![[34, 34, 29], [43, 38, 11], [13, 24, 24], [26, 9, 42], [35, 20, 34], [12, 12, 18]], ![[0, 1], [38, 18, 24], [13, 16, 26], [6, 8, 39], [8, 27, 12], [34, 34, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17], []]
 b := ![[], [5, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [38, 26, 1, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![90898072, 48675405, 42645232, 45141054, 18817716]
  a := ![15, 17, 12, 6, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-42012772, -5770761, -60089092, 45141054, 18817716]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 0, 2, 6, -4]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![35, 0, 2, 6, -4]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![26, 4, 1, 0, 0], ![4, 21, 0, 1, 0], ![22, 10, 0, 0, 1]] where
  M :=![![![35, 0, 2, 6, -4], ![-92, 3, -4, -16, 12], ![140, 2, 11, 28, -16], ![-134, 2, -6, -23, 18], ![122, 6, 10, 26, -11]]]
  hmulB := by decide  
  f := ![![![17, 0, -2, 2, 0]], ![![-4, 21, -4, -16, 4]], ![![10, 2, -1, 0, 0]], ![![-2, 9, -2, -7, 2]], ![![8, 4, -2, -2, 1]]]
  g := ![![![1, -2, 2, 6, -4], ![-4, 5, -4, -16, 12], ![2, -10, 11, 28, -16], ![-6, 7, -6, -23, 18], ![0, -10, 10, 26, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [2, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 46], [0, 1]]
 g := ![![[19, 24], [4, 42], [17, 21], [35, 34], [1]], ![[0, 23], [6, 5], [18, 26], [12, 13], [1]]]
 h' := ![![[9, 46], [39, 27], [13, 29], [24, 16], [45, 9], [0, 1]], ![[0, 1], [0, 20], [39, 18], [27, 31], [32, 38], [9, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [13, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [2, 38, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9723, 9587, 6990, 6287, 7379]
  a := ![6, 12, 2, -5, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7649, -4770, 6990, 6287, 7379]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-17, 0, 2, -2, 0]] ![![35, 0, 2, 6, -4]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3258, 96, -202, -460, 363]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-3258, 96, -202, -460, 363]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![23, 41, 12, 31, 1]] where
  M :=![![![-3258, 96, -202, -460, 363], ![8308, -249, 514, 1160, -920], ![-10526, 337, -655, -1458, 1160], ![10401, -334, 652, 1437, -1147], ![-6865, 222, -434, -918, 750]]]
  hmulB := by decide  
  f := ![![![8, 4, 2, 2, 1]], ![![28, 17, 14, 12, 4]], ![![62, 31, 35, 38, 12]], ![![41, 20, 16, 19, 9]], ![![66, 35, 30, 31, 12]]]
  g := ![![![-219, -279, -86, -221, 363], ![556, 707, 218, 560, -920], ![-702, -891, -275, -706, 1160], ![694, 881, 272, 698, -1147], ![-455, -576, -178, -456, 750]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [4, 21, 25, 22, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 32, 22, 36], [49, 0, 51, 7], [17, 20, 33, 10], [0, 1]]
 g := ![![[22, 16, 44, 16], [33, 25, 44], [45, 46, 13, 46], [35, 31, 1], []], ![[28, 19, 16, 26, 7, 13], [40, 23, 38], [48, 3, 47, 27, 44, 10], [41, 40, 16], [42, 9, 31, 42, 13, 16]], ![[2, 50, 15, 49, 7, 9], [10, 10, 9], [52, 14, 4, 4], [28, 13, 52], [29, 17, 3, 7, 4, 25]], ![[24, 1, 37, 31, 12, 37], [23, 18, 42], [24, 29, 10, 43, 44, 7], [2, 1, 40], [15, 0, 17, 30, 37, 46]]]
 h' := ![![[18, 32, 22, 36], [44, 34, 23, 4], [32, 27, 36, 16], [19, 42, 7, 24], [0, 0, 0, 1], [0, 1]], ![[49, 0, 51, 7], [35, 49, 44, 29], [47, 11, 38, 12], [44, 4, 22, 11], [46, 29, 4, 49], [18, 32, 22, 36]], ![[17, 20, 33, 10], [22, 22, 24, 17], [50, 43, 36, 50], [11, 22, 24], [32, 12, 29, 30], [49, 0, 51, 7]], ![[0, 1], [42, 1, 15, 3], [9, 25, 49, 28], [44, 38, 0, 18], [30, 12, 20, 26], [17, 20, 33, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 35, 18], []]
 b := ![[], [], [21, 32, 8, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [4, 21, 25, 22, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12914726756, 6616088638, 5666464838, 6022923039, 2313425889]
  a := ![12, 6, 8, 15, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-760265447, -1664799487, -416880110, -1239495840, 2313425889]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, -4, -2, -2, -1]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-8, -4, -2, -2, -1]] 
 ![![53, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-8, -4, -2, -2, -1], ![-28, -17, -14, -12, -4], ![-62, -31, -35, -38, -12], ![-41, -20, -16, -19, -9], ![-151, -74, -54, -60, -26]]]
  hmulB := by decide  
  f := ![![![3258, -96, 202, 460, -363]], ![![2548, -75, 158, 360, -284]], ![![2596, -77, 161, 366, -289]], ![![357, -10, 22, 51, -40]], ![![191, -6, 12, 26, -21]]]
  g := ![![![5, -4, -2, -2, -1], ![26, -17, -14, -12, -4], ![57, -31, -35, -38, -12], ![31, -20, -16, -19, -9], ![109, -74, -54, -60, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-3258, 96, -202, -460, 363]] ![![-8, -4, -2, -2, -1]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [56, 28, 35, 46, 35, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 5, 32, 51], [47, 53, 24, 45, 41], [29, 54, 22, 29, 28], [19, 5, 40, 52, 49], [0, 1]]
 g := ![![[55, 34, 51, 21, 5], [11, 1, 47, 1, 49], [35, 20, 51, 53], [58, 24, 1], []], ![[53, 23, 55, 39, 27, 28, 35], [7, 7, 26, 10, 25, 2, 9], [13, 43, 49, 20], [25, 55, 3, 51, 4, 56, 19], [53, 0, 39, 51, 19]], ![[6, 40, 10, 48, 55, 35, 37, 16], [22, 40, 38, 50, 55, 9, 50, 27], [20, 34, 55, 19], [43, 36, 17, 56, 30, 24, 31, 46], [39, 2, 32, 7, 55, 23, 1, 9]], ![[25, 10, 26, 57, 51, 9, 9, 25], [44, 14, 40, 11, 37, 5, 53, 5], [2, 28, 36, 16], [56, 33, 14, 40, 54, 57, 1, 53], [44, 15, 30, 15, 45, 55, 41, 4]], ![[14, 44, 49, 45, 56, 54, 54, 26], [2, 0, 53, 35, 38, 12, 44, 22], [22, 43, 45, 22], [5, 9, 36, 6, 7, 24, 37, 35], [28, 26, 14, 14, 12, 11, 37, 3]]]
 h' := ![![[47, 5, 32, 51], [33, 6, 29, 27, 8], [55, 14, 18, 46, 52], [56, 41, 15, 4, 17], [0, 0, 0, 1], [0, 1]], ![[47, 53, 24, 45, 41], [18, 8, 16, 36, 11], [29, 9, 37, 28, 27], [7, 9, 29, 19, 43], [24, 27, 35, 3, 51], [47, 5, 32, 51]], ![[29, 54, 22, 29, 28], [2, 49, 11, 50, 24], [54, 23, 39, 51, 21], [17, 2, 17, 8, 45], [41, 39, 18, 8, 57], [47, 53, 24, 45, 41]], ![[19, 5, 40, 52, 49], [42, 31, 26, 17, 48], [11, 11, 5, 53, 53], [51, 49, 22, 45, 4], [36, 4, 56, 54, 57], [29, 54, 22, 29, 28]], ![[0, 1], [57, 24, 36, 47, 27], [22, 2, 19, 58, 24], [30, 17, 35, 42, 9], [40, 48, 9, 52, 12], [19, 5, 40, 52, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 29, 17], [], [], []]
 b := ![[], [5, 24, 32, 57, 39], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [56, 28, 35, 46, 35, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-654343430668323, -334176346399561, -284527098268705, -303484831809406, -117368871432642]
  a := ![-25, -6, -33, -52, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11090566621497, -5664005871179, -4822493190995, -5143810708634, -1989302905638]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-90, -60, -50, -48, -25]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-90, -60, -50, -48, -25]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![5, 58, 40, 1, 0], ![55, 35, 35, 0, 1]] where
  M :=![![![-90, -60, -50, -48, -25], ![-700, -313, -270, -304, -96], ![-1422, -799, -679, -698, -304], ![-1055, -462, -396, -451, -139], ![-2769, -1486, -1258, -1314, -542]]]
  hmulB := by decide  
  f := ![![![168, 0, 10, 22, -19]], ![![-436, 9, -18, -60, 44]], ![![510, -41, 35, 94, -60]], ![![-75, -18, 6, 5, 2]], ![![201, -18, 19, 40, -27]]]
  g := ![![![25, 59, 45, -48, -25], ![100, 339, 250, -304, -96], ![308, 825, 621, -698, -304], ![145, 501, 369, -451, -139], ![551, 1536, 1152, -1314, -542]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [4, 33, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 10, 35], [44, 50, 26], [0, 1]]
 g := ![![[36, 9, 13], [9, 49], [36, 48, 5], [44, 46, 57], [1]], ![[9, 7, 40, 10], [31, 5], [35, 30, 16, 26], [13, 58, 49, 40], [24, 41, 35, 53]], ![[2, 31, 26, 11], [1, 52], [20, 52, 55, 55], [41, 22, 41, 10], [55, 11, 11, 8]]]
 h' := ![![[39, 10, 35], [21, 60, 47], [39, 11, 54], [7, 27, 35], [57, 28, 22], [0, 1]], ![[44, 50, 26], [14, 10, 58], [57, 59, 35], [4, 37, 11], [53, 22, 6], [39, 10, 35]], ![[0, 1], [10, 52, 17], [21, 52, 33], [45, 58, 15], [52, 11, 33], [44, 50, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 60], []]
 b := ![[], [56, 38, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [4, 33, 39, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12614991, -6522136, -5583916, -5856436, -2216004]
  a := ![-10, -3, -10, -18, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2271269, 6732972, 5020224, -5856436, -2216004]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![168, 0, 10, 22, -19]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![168, 0, 10, 22, -19]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![30, 3, 1, 0, 0], ![1, 11, 0, 1, 0], ![37, 40, 0, 0, 1]] where
  M :=![![![168, 0, 10, 22, -19], ![-436, 9, -18, -60, 44], ![510, -41, 35, 94, -60], ![-527, 20, -40, -85, 65], ![431, 22, 14, 40, -42]]]
  hmulB := by decide  
  f := ![![![-90, -60, -50, -48, -25]], ![![-700, -313, -270, -304, -96]], ![![-102, -58, -49, -50, -22]], ![![-145, -65, -56, -63, -20]], ![![-559, -266, -228, -250, -87]]]
  g := ![![![9, 8, 10, 22, -19], ![-24, -17, -18, -60, 44], ![26, 20, 35, 94, -60], ![-27, -25, -40, -85, 65], ![25, 20, 14, 40, -42]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [21, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 60], [0, 1]]
 g := ![![[10, 60], [9], [3, 49], [54, 27], [34, 1]], ![[37, 1], [9], [22, 12], [57, 34], [7, 60]]]
 h' := ![![[34, 60], [59, 50], [59, 3], [25, 7], [18, 37], [0, 1]], ![[0, 1], [51, 11], [39, 58], [19, 54], [56, 24], [34, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [55, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [21, 27, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![70949, 35338, 40014, 44706, 15402]
  a := ![23, 5, 19, 42, 24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28591, -19550, 40014, 44706, 15402]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-90, -60, -50, -48, -25]] ![![168, 0, 10, 22, -19]]
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


lemma PB519I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB519I1 : PrimesBelowBoundCertificateInterval O 23 61 519 where
  m := 9
  g := ![2, 2, 4, 3, 1, 2, 2, 1, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB519I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2, I37N3]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
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
    · exact ![1369, 37, 37, 37]
    · exact ![68921, 41, 41]
    · exact ![147008443]
    · exact ![103823, 2209]
    · exact ![7890481, 53]
    · exact ![714924299]
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
      exact NI37N1
      exact NI37N2
      exact NI37N3
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I37N1, I37N2, I37N3, I41N1, I41N2, I53N1]
  Il := ![[], [], [I37N1, I37N2, I37N3], [I41N1, I41N2], [], [], [I53N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
