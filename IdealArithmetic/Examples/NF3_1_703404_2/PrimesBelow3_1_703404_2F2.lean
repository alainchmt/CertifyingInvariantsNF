
import IdealArithmetic.Examples.NF3_1_703404_2.RI3_1_703404_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [71, 18, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 4, 24], [64, 78, 59], [0, 1]]
 g := ![![[39, 65, 70], [21, 15, 23], [64, 78], [3, 25], [59, 34, 1], []], ![[45, 27, 51, 50], [43, 52, 0, 54], [66, 9], [81, 7], [57, 16, 43, 19], [22, 78]], ![[34, 78, 61, 9], [27, 44], [9, 26], [19, 38], [42, 4, 59, 31], [70, 78]]]
 h' := ![![[53, 4, 24], [3, 4, 53], [6, 62, 40], [63, 47, 59], [44, 10, 78], [0, 0, 1], [0, 1]], ![[64, 78, 59], [72, 63, 80], [52, 47, 43], [16, 43, 3], [66, 34, 16], [2, 51, 78], [53, 4, 24]], ![[0, 1], [2, 16, 33], [56, 57], [60, 76, 21], [74, 39, 72], [39, 32, 4], [64, 78, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 54], []]
 b := ![[], [23, 25, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [71, 18, 49, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-95035, -29216, -2075]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1145, -352, -25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![247, 87, 9]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![247, 87, 9]] 
 ![![89, 0, 0], ![0, 89, 0], ![67, 69, 1]] where
  M :=![![![247, 87, 9], ![2358, 841, 87], ![22794, 8100, 841]]]
  hmulB := by decide  
  f := ![![![29, -3, 0]], ![![0, 29, -3]], ![![13, 18, -2]]]
  g := ![![![-4, -6, 9], ![-39, -58, 87], ![-377, -561, 841]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [10, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 88], [0, 1]]
 g := ![![[49, 9], [71], [71], [37, 4], [21, 67], [1]], ![[0, 80], [71], [71], [35, 85], [32, 22], [1]]]
 h' := ![![[44, 88], [46, 3], [20, 31], [75, 31], [57, 87], [79, 44], [0, 1]], ![[0, 1], [0, 86], [49, 58], [15, 58], [58, 2], [57, 45], [44, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [28, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [10, 45, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3178, 1480, 727]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-583, -547, 727]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, -3, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![29, -3, 0]] 
 ![![89, 0, 0], ![20, 1, 0], ![45, 0, 1]] where
  M :=![![![29, -3, 0], ![0, 29, -3], ![-786, -198, 29]]]
  hmulB := by decide  
  f := ![![![247, 87, 9]], ![![82, 29, 3]], ![![381, 135, 14]]]
  g := ![![![1, -3, 0], ![-5, 29, -3], ![21, -198, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![247, 87, 9]] ![![29, -3, 0]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-1, 29, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-1, 29, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![96, 29, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-1, 29, 1], ![262, 65, 29], ![7598, 2176, 65]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-96, -29, 97]], ![![-1, 0, 1], ![-26, -8, 29], ![14, 3, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [26, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 96], [0, 1]]
 g := ![![[31, 95], [6], [31], [96], [1], [67, 1]], ![[91, 2], [6], [31], [96], [1], [37, 96]]]
 h' := ![![[67, 96], [2, 17], [35, 43], [29, 82], [87, 75], [4, 1], [0, 1]], ![[0, 1], [74, 80], [6, 54], [91, 15], [68, 22], [71, 96], [67, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [47, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [26, 30, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1678, 32, 165]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-146, -49, 165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-29, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-29, 1, 0]] 
 ![![97, 0, 0], ![68, 1, 0], ![32, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-29, 1, 0], ![0, -29, 1], ![262, 66, -29]]]
  hmulB := by decide  
  f := ![![![2698, -93, 0], ![9021, 0, 0]], ![![1886, -65, 0], ![6306, 0, 0]], ![![908, -31, 0], ![3036, 1, 0]]]
  g := ![![![1, 0, 0], ![-68, 97, 0], ![-32, 0, 97]], ![![-1, 1, 0], ![20, -29, 1], ![-34, 66, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-1, 29, 1]] ![![97, 0, 0], ![-29, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-2813, 97, 0]], ![![-97, 2813, 97], ![291, -776, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-29, 1, 0]]], ![![![-1, 29, 1]], ![![3, -8, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-1, 41, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-1, 41, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![100, 41, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-1, 41, 1], ![262, 65, 41], ![10742, 2968, 65]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-100, -41, 101]], ![![-1, 0, 1], ![-38, -16, 41], ![42, 3, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [48, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 100], [0, 1]]
 g := ![![[5, 30], [49], [46, 9], [16], [21], [63, 1]], ![[77, 71], [49], [7, 92], [16], [21], [25, 100]]]
 h' := ![![[63, 100], [66, 63], [14, 94], [70, 98], [38, 97], [6, 83], [0, 1]], ![[0, 1], [96, 38], [78, 7], [83, 3], [89, 4], [84, 18], [63, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [95, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [48, 38, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1485, 2002, 475]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-485, -173, 475]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-41, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-41, 1, 0]] 
 ![![101, 0, 0], ![60, 1, 0], ![36, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-41, 1, 0], ![0, -41, 1], ![262, 66, -41]]]
  hmulB := by decide  
  f := ![![![3486, -85, 0], ![8585, 0, 0]], ![![2092, -51, 0], ![5152, 0, 0]], ![![1288, -31, 0], ![3172, 1, 0]]]
  g := ![![![1, 0, 0], ![-60, 101, 0], ![-36, 0, 101]], ![![-1, 1, 0], ![24, -41, 1], ![-22, 66, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-1, 41, 1]] ![![101, 0, 0], ![-41, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-4141, 101, 0]], ![![-101, 4141, 101], ![303, -1616, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-41, 1, 0]]], ![![![-1, 41, 1]], ![![3, -16, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-37, -21, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-37, -21, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![66, 82, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-37, -21, 1], ![262, 29, -21], ![-5502, -1124, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -82, 103]], ![![-1, -1, 1], ![16, 17, -21], ![-72, -34, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [40, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 102], [0, 1]]
 g := ![![[34, 26], [66, 58], [23, 82], [81], [18], [82, 1]], ![[3, 77], [84, 45], [52, 21], [81], [18], [61, 102]]]
 h' := ![![[82, 102], [38, 51], [7, 77], [82, 59], [51, 94], [16, 92], [0, 1]], ![[0, 1], [100, 52], [38, 26], [79, 44], [34, 9], [41, 11], [82, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [78, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [40, 21, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![564, 373, 46]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24, -33, 46]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![21, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![21, 1, 0]] 
 ![![103, 0, 0], ![21, 1, 0], ![74, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![21, 1, 0], ![0, 21, 1], ![262, 66, 21]]]
  hmulB := by decide  
  f := ![![![883, 42, 0], ![-4326, 0, 0]], ![![147, 7, 0], ![-720, 0, 0]], ![![614, 29, 0], ![-3008, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 103, 0], ![-74, 0, 103]], ![![0, 1, 0], ![-5, 21, 1], ![-26, 66, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-37, -21, 1]] ![![103, 0, 0], ![21, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![2163, 103, 0]], ![![-3811, -2163, 103], ![-515, -412, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![21, 1, 0]]], ![![![-37, -21, 1]], ![![-5, -4, 0]]]]
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
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [39, 103, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 47, 105], [72, 59, 2], [0, 1]]
 g := ![![[56, 40, 42], [40, 18, 30], [92, 16], [71, 81, 37], [27, 35], [1]], ![[48, 6, 52, 49], [48, 24, 86, 90], [33, 16], [10, 70, 101, 35], [13, 23], [21, 93, 19, 99]], ![[103, 28, 45, 46], [50, 99, 93, 66], [36, 64], [20, 13, 79, 72], [50, 102], [63, 49, 76, 8]]]
 h' := ![![[63, 47, 105], [45, 18, 16], [5, 85, 43], [13, 9, 4], [40, 36, 12], [68, 4, 28], [0, 1]], ![[72, 59, 2], [78, 70, 52], [27, 37, 13], [64, 15, 4], [11, 40, 101], [25, 7, 39], [63, 47, 105]], ![[0, 1], [27, 19, 39], [39, 92, 51], [65, 83, 99], [95, 31, 101], [36, 96, 40], [72, 59, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 48], []]
 b := ![[], [46, 50, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [39, 103, 79, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3667960, 1251472, 126046]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34280, 11696, 1178]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![39, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![39, 1, 0]] 
 ![![109, 0, 0], ![39, 1, 0], ![5, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![39, 1, 0], ![0, 39, 1], ![262, 66, 39]]]
  hmulB := by decide  
  f := ![![![469, 12, 0], ![-1308, 0, 0]], ![![117, 3, 0], ![-326, 0, 0]], ![![-25, -1, 0], ![70, 1, 0]]]
  g := ![![![1, 0, 0], ![-39, 109, 0], ![-5, 0, 109]], ![![0, 1, 0], ![-14, 39, 1], ![-23, 66, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, -10, -1]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-29, -10, -1]] 
 ![![109, 0, 0], ![71, 1, 0], ![82, 0, 1]] where
  M :=![![![-29, -10, -1], ![-262, -95, -10], ![-2620, -922, -95]]]
  hmulB := by decide  
  f := ![![![195, 28, -5]], ![![115, 17, -3]], ![![214, 26, -5]]]
  g := ![![![7, -10, -1], ![67, -95, -10], ![648, -922, -95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-1, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-1, 1, 0]] 
 ![![109, 0, 0], ![108, 1, 0], ![108, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-1, 1, 0], ![0, -1, 1], ![262, 66, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![327, 0, 0]], ![![2, -1, 0], ![110, 0, 0]], ![![2, -1, 0], ![110, 1, 0]]]
  g := ![![![1, 0, 0], ![-108, 109, 0], ![-108, 0, 109]], ![![-1, 1, 0], ![0, -1, 1], ![-62, 66, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![39, 1, 0]] ![![-29, -10, -1]]
  ![![109, 0, 0], ![-65, 1, 1]] where
 M := ![![![-3161, -1090, -109]], ![![-1393, -485, -49]]]
 hmul := by decide  
 g := ![![![![36, -11, -2], ![109, 0, 0]]], ![![![23, -5, -1], ![60, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-65, 1, 1]] ![![109, 0, 0], ![-1, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-109, 109, 0]], ![![-7085, 109, 109], ![327, 0, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-1, 1, 0]]], ![![![-65, 1, 1]], ![![3, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-55, 24, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-55, 24, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![58, 24, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-55, 24, 1], ![262, 11, 24], ![6288, 1846, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -24, 113]], ![![-1, 0, 1], ![-10, -5, 24], ![50, 14, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [7, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 112], [0, 1]]
 g := ![![[44, 97], [41], [50], [102], [91, 14], [31, 1]], ![[0, 16], [41], [50], [102], [73, 99], [62, 112]]]
 h' := ![![[31, 112], [61, 60], [3, 43], [63, 84], [41, 92], [9, 50], [0, 1]], ![[0, 1], [0, 53], [93, 70], [68, 29], [68, 21], [90, 63], [31, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [79, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [7, 82, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1646, 106, -5]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, 2, -5]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-24, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-24, 1, 0]] 
 ![![113, 0, 0], ![89, 1, 0], ![102, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-24, 1, 0], ![0, -24, 1], ![262, 66, -24]]]
  hmulB := by decide  
  f := ![![![1033, -43, 0], ![4859, 0, 0]], ![![817, -34, 0], ![3843, 0, 0]], ![![966, -40, 0], ![4544, 1, 0]]]
  g := ![![![1, 0, 0], ![-89, 113, 0], ![-102, 0, 113]], ![![-1, 1, 0], ![18, -24, 1], ![-28, 66, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-55, 24, 1]] ![![113, 0, 0], ![-24, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-2712, 113, 0]], ![![-6215, 2712, 113], ![1582, -565, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-24, 1, 0]]], ![![![-55, 24, 1]], ![![14, -5, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![16, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![16, 1, 0]] 
 ![![127, 0, 0], ![16, 1, 0], ![125, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![16, 1, 0], ![0, 16, 1], ![262, 66, 16]]]
  hmulB := by decide  
  f := ![![![97, 6, 0], ![-762, 0, 0]], ![![-16, -1, 0], ![128, 0, 0]], ![![99, 6, 0], ![-778, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 127, 0], ![-125, 0, 127]], ![![0, 1, 0], ![-3, 16, 1], ![-22, 66, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-9, 1, 0]] 
 ![![127, 0, 0], ![118, 1, 0], ![46, 0, 1]] where
  M :=![![![-9, 1, 0], ![0, -9, 1], ![262, 66, -9]]]
  hmulB := by decide  
  f := ![![![15, 9, 1]], ![![16, 9, 1]], ![![24, 10, 1]]]
  g := ![![![-1, 1, 0], ![8, -9, 1], ![-56, 66, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-7, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-7, 1, 0]] 
 ![![127, 0, 0], ![120, 1, 0], ![78, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-7, 1, 0], ![0, -7, 1], ![262, 66, -7]]]
  hmulB := by decide  
  f := ![![![778, -111, 0], ![14097, 0, 0]], ![![736, -105, 0], ![13336, 0, 0]], ![![484, -69, 0], ![8770, 1, 0]]]
  g := ![![![1, 0, 0], ![-120, 127, 0], ![-78, 0, 127]], ![![-1, 1, 0], ![6, -7, 1], ![-56, 66, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![16, 1, 0]] ![![-9, 1, 0]]
  ![![127, 0, 0], ![-17, 7, 1]] where
 M := ![![![-1143, 127, 0]], ![![-144, 7, 1]]]
 hmul := by decide  
 g := ![![![![8, -6, -1], ![127, 0, 0]]], ![![![-1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-17, 7, 1]] ![![127, 0, 0], ![-7, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-889, 127, 0]], ![![-2159, 889, 127], ![381, 0, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-7, 1, 0]]], ![![![-17, 7, 1]], ![![3, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![0, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![0, 1, 0]] 
 ![![131, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![0, 1, 0], ![0, 0, 1], ![262, 66, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![0, 1, 0], ![0, 0, 1], ![2, 66, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-66, 0, 1]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-66, 0, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![65, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-66, 0, 1], ![262, 0, 0], ![0, 262, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, 0, 131]], ![![-1, 0, 1], ![2, 0, 0], ![0, 2, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [66, 129, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 130], [0, 1]]
 g := ![![[127, 4], [125, 107], [36], [112], [36], [4], [1]], ![[4, 127], [77, 24], [36], [112], [36], [4], [1]]]
 h' := ![![[2, 130], [3, 129], [28, 99], [96, 125], [26, 51], [31, 6], [65, 2], [0, 1]], ![[0, 1], [130, 2], [95, 32], [84, 6], [128, 80], [43, 125], [69, 129], [2, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [1, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [66, 129, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1114, 1441, 523]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-251, 11, 523]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![0, 1, 0]] ![![131, 0, 0], ![-66, 0, 1]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-8646, 0, 131]], ![![0, 131, 0], ![262, 0, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-66, 0, 1]]], ![![![0, 1, 0]], ![![2, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![21, 19, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![21, 19, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![21, 19, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![21, 19, 1], ![262, 87, 19], ![4978, 1516, 87]]]
  hmulB := by decide  
  f := ![![![-20, -19, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -19, 137]], ![![0, 0, 1], ![-1, -2, 19], ![23, -1, 87]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [78, 127, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 136], [0, 1]]
 g := ![![[35, 65], [39], [120], [18, 15], [7], [100], [1]], ![[0, 72], [39], [120], [31, 122], [7], [100], [1]]]
 h' := ![![[10, 136], [91, 32], [16, 83], [103, 95], [117, 17], [65, 125], [59, 10], [0, 1]], ![[0, 1], [0, 105], [24, 54], [94, 42], [13, 120], [82, 12], [22, 127], [10, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106]]
 b := ![[], [9, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [78, 127, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10144, -2902, 626]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-170, -108, 626]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-19, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-19, 1, 0]] 
 ![![137, 0, 0], ![118, 1, 0], ![50, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-19, 1, 0], ![0, -19, 1], ![262, 66, -19]]]
  hmulB := by decide  
  f := ![![![2072, -109, 0], ![14933, 0, 0]], ![![1806, -95, 0], ![13016, 0, 0]], ![![782, -41, 0], ![5636, 1, 0]]]
  g := ![![![1, 0, 0], ![-118, 137, 0], ![-50, 0, 137]], ![![-1, 1, 0], ![16, -19, 1], ![-48, 66, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![21, 19, 1]] ![![137, 0, 0], ![-19, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-2603, 137, 0]], ![![2877, 2603, 137], ![-137, -274, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-19, 1, 0]]], ![![![21, 19, 1]], ![![-1, -2, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB238I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB238I2 : PrimesBelowBoundCertificateInterval O 79 137 238 where
  m := 11
  g := ![1, 2, 2, 2, 2, 1, 3, 2, 3, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB238I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
    · exact ![131, 17161]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
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
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I89N1, I97N1, I101N1, I103N1, I109N0, I109N1, I109N2, I113N1, I127N0, I127N1, I127N2, I131N0, I137N1]
  Il := ![[], [I89N1], [I97N1], [I101N1], [I103N1], [], [I109N0, I109N1, I109N2], [I113N1], [I127N0, I127N1, I127N2], [I131N0], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
