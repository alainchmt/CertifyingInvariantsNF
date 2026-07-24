
import IdealArithmetic.Examples.NF3_3_936117_1.RI3_3_936117_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-36, -14, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-36, -14, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![47, 69, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-36, -14, 1], ![89, 30, -14], ![-1246, -835, 30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -69, 83]], ![![-1, -1, 1], ![9, 12, -14], ![-32, -35, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [9, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 82], [0, 1]]
 g := ![![[59, 37], [8, 9], [40], [36], [15, 10], [1]], ![[0, 46], [43, 74], [40], [36], [17, 73], [1]]]
 h' := ![![[50, 82], [11, 28], [37, 3], [56, 17], [31, 77], [74, 50], [0, 1]], ![[0, 1], [0, 55], [21, 80], [76, 66], [63, 6], [1, 33], [50, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [30, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [9, 33, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![187, 188, 34]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17, -26, 34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![14, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![14, 1, 0]] 
 ![![83, 0, 0], ![14, 1, 0], ![53, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![14, 1, 0], ![0, 14, 1], ![89, 66, 14]]]
  hmulB := by decide  
  f := ![![![57, 4, 0], ![-332, 0, 0]], ![![-14, -1, 0], ![84, 0, 0]], ![![31, 2, 0], ![-180, 1, 0]]]
  g := ![![![1, 0, 0], ![-14, 83, 0], ![-53, 0, 83]], ![![0, 1, 0], ![-3, 14, 1], ![-19, 66, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-36, -14, 1]] ![![83, 0, 0], ![14, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![1162, 83, 0]], ![![-2988, -1162, 83], ![-415, -166, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![14, 1, 0]]], ![![![-36, -14, 1]], ![![-5, -2, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![0, 1, 0]] 
 ![![89, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![0, 1, 0], ![0, 0, 1], ![89, 66, 0]]]
  hmulB := by decide  
  f := ![![![-66, 0, 1]], ![![1, 0, 0]], ![![0, 1, 0]]]
  g := ![![![0, 1, 0], ![0, 0, 1], ![1, 66, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-66, 0, 1]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-66, 0, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![23, 0, 1]] where
  M :=![![![-66, 0, 1], ![89, 0, 0], ![0, 89, 0]]]
  hmulB := by decide  
  f := ![![![0, 1, 0]], ![![0, 0, 1]], ![![1, 1, 0]]]
  g := ![![![-1, 0, 1], ![1, 0, 0], ![0, 1, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [8, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 88], [0, 1]]
 g := ![![[62, 78], [36], [84], [46, 78], [63, 20], [1]], ![[0, 11], [36], [84], [73, 11], [22, 69], [1]]]
 h' := ![![[38, 88], [15, 16], [6, 6], [77, 66], [30, 73], [81, 38], [0, 1]], ![[0, 1], [0, 73], [56, 83], [4, 23], [45, 16], [12, 51], [38, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [71, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [8, 51, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1110, -89, 745]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-205, -1, 745]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![0, 1, 0]] ![![-66, 0, 1]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-68, -17, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-68, -17, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![29, 80, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-68, -17, 1], ![89, -2, -17], ![-1513, -1033, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -80, 97]], ![![-1, -1, 1], ![6, 14, -17], ![-15, -9, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [30, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 96], [0, 1]]
 g := ![![[89, 62], [33], [47], [86], [73], [46, 1]], ![[31, 35], [33], [47], [86], [73], [92, 96]]]
 h' := ![![[46, 96], [53, 81], [48, 79], [87, 12], [40, 38], [75, 49], [0, 1]], ![[0, 1], [93, 16], [93, 18], [57, 85], [42, 59], [1, 48], [46, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [32, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [30, 51, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![684, -120, 144]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36, -120, 144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![17, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![17, 1, 0]] 
 ![![97, 0, 0], ![17, 1, 0], ![2, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![17, 1, 0], ![0, 17, 1], ![89, 66, 17]]]
  hmulB := by decide  
  f := ![![![579, 34, 0], ![-3298, 0, 0]], ![![85, 5, 0], ![-484, 0, 0]], ![![-14, -1, 0], ![80, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 97, 0], ![-2, 0, 97]], ![![0, 1, 0], ![-3, 17, 1], ![-11, 66, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-68, -17, 1]] ![![97, 0, 0], ![17, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![1649, 97, 0]], ![![-6596, -1649, 97], ![-1067, -291, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![17, 1, 0]]], ![![![-68, -17, 1]], ![![-11, -3, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [52, 63, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 38, 95], [22, 62, 6], [0, 1]]
 g := ![![[41, 7, 64], [94, 36], [15, 94, 23], [16, 76], [46, 20], [1]], ![[92, 23, 28, 22], [1, 21], [41, 80, 92, 43], [61, 4], [23, 76], [67, 83, 11, 87]], ![[77, 65, 80, 47], [7, 71], [25, 34, 81, 4], [30, 82], [20, 85], [80, 91, 83, 14]]]
 h' := ![![[90, 38, 95], [37, 12, 93], [28, 42, 95], [57, 76, 86], [9, 89, 51], [49, 38, 11], [0, 1]], ![[22, 62, 6], [35, 61, 38], [17, 12, 83], [96, 39, 28], [95, 80, 2], [33, 5, 50], [90, 38, 95]], ![[0, 1], [9, 28, 71], [26, 47, 24], [20, 87, 88], [41, 33, 48], [24, 58, 40], [22, 62, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 63], []]
 b := ![[], [26, 12, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [52, 63, 90, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-104636, -162408, -61206]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1036, -1608, -606]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-33, 41, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-33, 41, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![70, 41, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-33, 41, 1], ![89, 33, 41], ![3649, 2795, 33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-70, -41, 103]], ![![-1, 0, 1], ![-27, -16, 41], ![13, 14, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [40, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 102], [0, 1]]
 g := ![![[89, 76], [41, 23], [45, 30], [41], [63], [45, 1]], ![[7, 27], [46, 80], [56, 73], [41], [63], [90, 102]]]
 h' := ![![[45, 102], [8, 30], [54, 69], [58, 66], [87, 91], [54, 28], [0, 1]], ![[0, 1], [19, 73], [69, 34], [41, 37], [62, 12], [78, 75], [45, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [79, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [40, 58, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![218, 163, 9]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, -2, 9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-41, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-41, 1, 0]] 
 ![![103, 0, 0], ![62, 1, 0], ![70, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-41, 1, 0], ![0, -41, 1], ![89, 66, -41]]]
  hmulB := by decide  
  f := ![![![4183, -102, 0], ![10506, 0, 0]], ![![2502, -61, 0], ![6284, 0, 0]], ![![2846, -69, 0], ![7148, 1, 0]]]
  g := ![![![1, 0, 0], ![-62, 103, 0], ![-70, 0, 103]], ![![-1, 1, 0], ![24, -41, 1], ![-11, 66, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-33, 41, 1]] ![![103, 0, 0], ![-41, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-4223, 103, 0]], ![![-3399, 4223, 103], ![1442, -1648, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-41, 1, 0]]], ![![![-33, 41, 1]], ![![14, -16, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, -20, -3]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-22, -20, -3]] 
 ![![107, 0, 0], ![66, 1, 0], ![31, 0, 1]] where
  M :=![![![-22, -20, -3], ![-267, -220, -20], ![-1780, -1587, -220]]]
  hmulB := by decide  
  f := ![![![-16660, -361, 260]], ![![-10060, -218, 157]], ![![-5127, -111, 80]]]
  g := ![![![13, -20, -3], ![139, -220, -20], ![1026, -1587, -220]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-130, -3, 2]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-130, -3, 2]] 
 ![![107, 0, 0], ![71, 1, 0], ![95, 0, 1]] where
  M :=![![![-130, -3, 2], ![178, 2, -3], ![-267, -20, 2]]]
  hmulB := by decide  
  f := ![![![56, 34, -5]], ![![33, 20, -3]], ![![78, 47, -7]]]
  g := ![![![-1, -3, 2], ![3, 2, -3], ![9, -20, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![135, 2, -2]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![135, 2, -2]] 
 ![![107, 0, 0], ![77, 1, 0], ![63, 0, 1]] where
  M :=![![![135, 2, -2], ![-178, 3, 2], ![178, -46, 3]]]
  hmulB := by decide  
  f := ![![![101, 86, 10]], ![![81, 69, 8]], ![![131, 112, 13]]]
  g := ![![![1, 2, -2], ![-5, 3, 2], ![33, -46, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-22, -20, -3]] ![![-130, -3, 2]]
  ![![101, 86, 10]] where
 M := ![![![101, 86, 10]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![101, 86, 10]] ![![135, 2, -2]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [78, 31, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 23, 60], [107, 85, 49], [0, 1]]
 g := ![![[22, 43, 105], [6, 22], [17, 80, 12], [41, 98, 28], [50, 22], [1]], ![[45, 47, 72, 66], [11, 12], [24, 58, 67, 83], [74, 66, 2, 1], [75, 93], [44, 44, 91, 71]], ![[41, 26, 94, 94], [22, 7], [15, 96, 30, 9], [65, 7, 39, 80], [67, 3], [45, 107, 9, 38]]]
 h' := ![![[28, 23, 60], [74, 41, 43], [91, 52, 26], [72, 39, 11], [4, 44, 30], [31, 78, 26], [0, 1]], ![[107, 85, 49], [45, 58, 11], [85, 88, 98], [34, 9, 5], [27, 27, 67], [99, 32, 23], [28, 23, 60]], ![[0, 1], [103, 10, 55], [82, 78, 94], [30, 61, 93], [34, 38, 12], [79, 108, 60], [107, 85, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 94], []]
 b := ![[], [78, 31, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [78, 31, 83, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1244235, 1036263, 117829]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11415, 9507, 1081]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [38, 84, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 95, 16], [70, 17, 97], [0, 1]]
 g := ![![[50, 14, 41], [69, 11], [24, 14], [102, 25], [106, 54, 32], [1]], ![[68, 4, 6, 87], [62, 32], [34, 106], [9, 62], [62, 86, 44, 102], [104, 98, 24, 28]], ![[13, 45, 37, 97], [59, 82], [51, 32], [99, 69], [21, 5, 48, 31], [75, 0, 112, 85]]]
 h' := ![![[21, 95, 16], [9, 13, 70], [22, 103, 24], [97, 69, 63], [40, 93, 108], [75, 29, 91], [0, 1]], ![[70, 17, 97], [102, 19, 42], [57, 2, 22], [28, 14, 28], [101, 11, 47], [111, 112, 90], [21, 95, 16]], ![[0, 1], [54, 81, 1], [107, 8, 67], [24, 30, 22], [82, 9, 71], [20, 85, 45], [70, 17, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103, 52], []]
 b := ![[], [2, 93, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [38, 84, 22, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![37177, 21131, -3955]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![329, 187, -35]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀


def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-244, -209, -24]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-244, -209, -24]] 
 ![![127, 0, 0], ![28, 1, 0], ![105, 0, 1]] where
  M :=![![![-244, -209, -24], ![-2136, -1828, -209], ![-18601, -15930, -1828]]]
  hmulB := by decide  
  f := ![![![12214, 268, -191]], ![![2559, 56, -40]], ![![10286, 227, -161]]]
  g := ![![![64, -209, -24], ![559, -1828, -209], ![4877, -15930, -1828]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 2, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![15, 2, 0]] 
 ![![127, 0, 0], ![71, 1, 0], ![39, 0, 1]] where
  M :=![![![15, 2, 0], ![0, 15, 2], ![178, 132, 15]]]
  hmulB := by decide  
  f := ![![![-39, -30, 4]], ![![-19, -15, 2]], ![![-33, -22, 3]]]
  g := ![![![-1, 2, 0], ![-9, 15, 2], ![-77, 132, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-244, -209, -24]] ![![-244, -209, -24]]
  ![![952384, 815368, 93409]] where
 M := ![![![952384, 815368, 93409]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI127N1 : IdealMulLeCertificate' Table 
  ![![952384, 815368, 93409]] ![![15, 2, 0]]
  ![![127, 0, 0]] where
 M := ![![![30912562, 26465276, 3031871]]]
 hmul := by decide  
 g := ![![![![243406, 208388, 23873]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-96, 25, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-96, 25, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![35, 25, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-96, 25, 1], ![89, -30, 25], ![2225, 1739, -30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -25, 131]], ![![-1, 0, 1], ![-6, -5, 25], ![25, 19, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [41, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 130], [0, 1]]
 g := ![![[63, 16], [10, 16], [33], [109], [33], [59], [1]], ![[0, 115], [78, 115], [33], [109], [33], [59], [1]]]
 h' := ![![[37, 130], [114, 4], [91, 4], [93, 66], [34, 90], [48, 66], [90, 37], [0, 1]], ![[0, 1], [0, 127], [108, 127], [46, 65], [89, 41], [1, 65], [18, 94], [37, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [77, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [41, 94, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![397, 714, 453]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-118, -81, 453]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-25, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-25, 1, 0]] 
 ![![131, 0, 0], ![106, 1, 0], ![30, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-25, 1, 0], ![0, -25, 1], ![89, 66, -25]]]
  hmulB := by decide  
  f := ![![![726, -29, 0], ![3799, 0, 0]], ![![576, -23, 0], ![3014, 0, 0]], ![![180, -7, 0], ![942, 1, 0]]]
  g := ![![![1, 0, 0], ![-106, 131, 0], ![-30, 0, 131]], ![![-1, 1, 0], ![20, -25, 1], ![-47, 66, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-96, 25, 1]] ![![131, 0, 0], ![-25, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-3275, 131, 0]], ![![-12576, 3275, 131], ![2489, -655, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-25, 1, 0]]], ![![![-96, 25, 1]], ![![19, -5, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [44, 107, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 72, 87], [96, 64, 50], [0, 1]]
 g := ![![[77, 9, 2], [102, 37], [3, 18], [0, 19, 109], [12, 61], [133, 1], []], ![[16, 89, 67, 64], [133, 72], [39, 65], [19, 115, 73, 118], [112, 17], [66, 123], [62, 34]], ![[5, 13, 112, 65], [19, 17], [22, 7], [15, 52, 90, 133], [63, 18], [111, 115], [99, 34]]]
 h' := ![![[37, 72, 87], [58, 29, 31], [5, 120, 41], [0, 46, 44], [34, 91, 71], [39, 110, 46], [0, 0, 1], [0, 1]], ![[96, 64, 50], [102, 29, 123], [101, 70, 49], [131, 36, 105], [72, 95, 131], [94, 136, 47], [11, 75, 64], [37, 72, 87]], ![[0, 1], [62, 79, 120], [79, 84, 47], [15, 55, 125], [96, 88, 72], [26, 28, 44], [65, 62, 72], [96, 64, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134, 58], []]
 b := ![[], [11, 63, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [44, 107, 4, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-765830, -465526, 67678]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5590, -3398, 494]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB216I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB216I2 : PrimesBelowBoundCertificateInterval O 79 137 216 where
  m := 11
  g := ![2, 2, 2, 1, 2, 3, 1, 1, 3, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB216I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0]
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
    · exact ![6889, 83]
    · exact ![89, 7921]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![127, 127, 127]
    · exact ![17161, 131]
    · exact ![2571353]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
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
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I89N0, I97N1, I103N1, I107N0, I107N1, I107N2, I127N0, I127N1, I131N1]
  Il := ![[I83N1], [I89N0], [I97N1], [], [I103N1], [I107N0, I107N1, I107N2], [], [], [I127N0, I127N0, I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
