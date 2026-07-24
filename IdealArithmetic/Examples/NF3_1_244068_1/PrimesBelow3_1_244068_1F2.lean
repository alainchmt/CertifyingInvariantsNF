
import IdealArithmetic.Examples.NF3_1_244068_1.RI3_1_244068_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-23, 22, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-23, 22, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![60, 22, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-23, 22, 1], ![58, -23, 131], ![296, -478, -67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -22, 83]], ![![-1, 0, 1], ![-94, -35, 131], ![52, 12, -67]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [52, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 82], [0, 1]]
 g := ![![[23, 1], [62, 28], [12], [78], [5, 77], [1]], ![[72, 82], [23, 55], [12], [78], [43, 6], [1]]]
 h' := ![![[49, 82], [13, 82], [34, 32], [49, 57], [72, 24], [31, 49], [0, 1]], ![[0, 1], [47, 1], [25, 51], [20, 26], [3, 59], [25, 34], [49, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [18, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [52, 34, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-501, -358, -2046]
  a := ![-3, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1473, 538, -2046]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![35, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![35, 1, 0]] 
 ![![83, 0, 0], ![35, 1, 0], ![67, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![35, 1, 0], ![2, 36, 6], ![14, -22, 34]]]
  hmulB := by decide  
  f := ![![![-1245, -28718, -4788], ![-830, 66234, 0]], ![![-532, -12092, -2016], ![-331, 27888, 0]], ![![-1005, -23182, -3865], ![-670, 53466, 0]]]
  g := ![![![1, 0, 0], ![-35, 83, 0], ![-67, 0, 83]], ![![0, 1, 0], ![-20, 36, 6], ![-18, -22, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-23, 22, 1]] ![![83, 0, 0], ![35, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2905, 83, 0]], ![![-1909, 1826, 83], ![-747, 747, 166]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![35, 1, 0]]], ![![![-23, 22, 1]], ![![-9, 9, 2]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![38, -36, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![38, -36, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![38, 53, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![38, -36, 1], ![-58, -20, -217], ![-516, 798, 52]]]
  hmulB := by decide  
  f := ![![![-37, 36, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -53, 89]], ![![0, -1, 1], ![92, 129, -217], ![-28, -22, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [65, 45, 1] where
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
 g := ![![[76, 39], [8], [25], [29, 11], [76, 67], [1]], ![[12, 50], [8], [25], [68, 78], [87, 22], [1]]]
 h' := ![![[44, 88], [13, 67], [55, 50], [73, 5], [44, 10], [24, 44], [0, 1]], ![[0, 1], [24, 22], [30, 39], [26, 84], [39, 79], [2, 45], [44, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [3, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [65, 45, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-429, 294, -735]
  a := ![2, 0, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![309, 441, -735]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![39, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![39, 1, 0]] 
 ![![89, 0, 0], ![39, 1, 0], ![37, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![39, 1, 0], ![2, 40, 6], ![14, -22, 38]]]
  hmulB := by decide  
  f := ![![![1873, 49904, 7488], ![1424, -111072, 0]], ![![819, 21833, 3276], ![624, -48594, 0]], ![![755, 20746, 3113], ![646, -46176, 0]]]
  g := ![![![1, 0, 0], ![-39, 89, 0], ![-37, 0, 89]], ![![0, 1, 0], ![-20, 40, 6], ![-6, -22, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![38, -36, 1]] ![![89, 0, 0], ![39, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3471, 89, 0]], ![![3382, -3204, 89], ![1424, -1424, -178]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![39, 1, 0]]], ![![![38, -36, 1]], ![![16, -16, -2]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [86, 63, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 41, 27], [17, 55, 70], [0, 1]]
 g := ![![[56, 11, 72], [78, 18], [89, 48], [86, 3], [28, 79], [1]], ![[88, 38, 9, 2], [89, 9], [53, 62], [8, 48], [81, 11], [11, 47, 19, 89]], ![[23, 65, 44, 50], [19, 85], [3, 91], [39, 27], [52, 81], [82, 20, 25, 8]]]
 h' := ![![[34, 41, 27], [76, 42, 13], [73, 10, 55], [8, 21, 57], [41, 47, 87], [11, 34, 51], [0, 1]], ![[17, 55, 70], [63, 23, 6], [32, 94, 94], [82, 15, 16], [24, 18, 40], [43, 4, 37], [34, 41, 27]], ![[0, 1], [68, 32, 78], [76, 90, 45], [72, 61, 24], [15, 32, 67], [92, 59, 9], [17, 55, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 15], []]
 b := ![[], [2, 13, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [86, 63, 46, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5364756884, -607436310, -15569176090]
  a := ![-129, -64, -323]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-55306772, -6262230, -160506970]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [19, 93, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 83, 49], [39, 17, 52], [0, 1]]
 g := ![![[91, 38, 84], [57, 84], [62, 68, 24], [20, 76], [16, 22], [1]], ![[45, 14, 15, 65], [20, 92], [44, 20, 24, 56], [70, 71], [99, 31], [99, 3, 2, 85]], ![[50, 43, 14, 20], [56, 36], [17, 23, 51, 85], [67, 22], [19, 52], [62, 92, 67, 16]]]
 h' := ![![[89, 83, 49], [73, 56, 36], [34, 77, 65], [41, 84, 23], [57, 12, 50], [82, 8, 27], [0, 1]], ![[39, 17, 52], [28, 98, 23], [99, 33, 30], [48, 98, 63], [60, 52, 24], [27, 29, 43], [89, 83, 49]], ![[0, 1], [69, 48, 42], [74, 92, 6], [45, 20, 15], [56, 37, 27], [66, 64, 31], [39, 17, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 17], []]
 b := ![[], [36, 73, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [19, 93, 74, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-316837, 131098, -620140]
  a := ![-3, -1, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3137, 1298, -6140]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-10, -20, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-10, -20, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![93, 83, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-10, -20, 1], ![-26, -52, -121], ![-292, 446, -12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-93, -83, 103]], ![![-1, -1, 1], ![109, 97, -121], ![8, 14, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [20, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 102], [0, 1]]
 g := ![![[101, 38], [30, 7], [26, 16], [16], [92], [40, 1]], ![[76, 65], [1, 96], [48, 87], [16], [92], [80, 102]]]
 h' := ![![[40, 102], [18, 55], [98, 25], [52, 4], [75, 4], [24, 35], [0, 1]], ![[0, 1], [55, 48], [68, 78], [6, 99], [29, 99], [85, 68], [40, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [19, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [20, 63, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-620, -416, -2307]
  a := ![-3, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2077, 1855, -2307]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![18, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![18, 1, 0]] 
 ![![103, 0, 0], ![18, 1, 0], ![12, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![18, 1, 0], ![2, 19, 6], ![14, -22, 17]]]
  hmulB := by decide  
  f := ![![![9253, 92144, 29106], ![2575, -499653, 0]], ![![1604, 16088, 5082], ![516, -87241, 0]], ![![1074, 10735, 3391], ![323, -58212, 0]]]
  g := ![![![1, 0, 0], ![-18, 103, 0], ![-12, 0, 103]], ![![0, 1, 0], ![-4, 19, 6], ![2, -22, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-10, -20, 1]] ![![103, 0, 0], ![18, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![1854, 103, 0]], ![![-1030, -2060, 103], ![-206, -412, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![18, 1, 0]]], ![![![-10, -20, 1]], ![![-2, -4, -1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![253951321, -369700210, 22469917]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![253951321, -369700210, 22469917]] 
 ![![107, 0, 0], ![0, 107, 0], ![26, 35, 1]] where
  M :=![![![253951321, -369700210, 22469917], ![-424821582, -610087063, -2240671177], ![-5445441944, 8268224122, 129313357]]]
  hmulB := by decide  
  f := ![![![-172406346438904029, -2183116682219092, -7869955236880663]], ![![-114545606680767466, -1450447909748535, -5228744856433889]], ![![-78764349644363228, -997363317676253, -3595412342798072]]]
  g := ![![![-3086603, -10805115, 22469917], ![540491860, 727228076, -2240671177], ![-82313918, 34974361, 129313357]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [93, 91, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 106], [0, 1]]
 g := ![![[47, 36], [65, 4], [92], [20, 30], [33], [16, 1]], ![[88, 71], [22, 103], [92], [72, 77], [33], [32, 106]]]
 h' := ![![[16, 106], [54, 6], [80, 105], [66, 78], [27, 43], [10, 56], [0, 1]], ![[0, 1], [43, 101], [48, 2], [30, 29], [73, 64], [50, 51], [16, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [22, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [93, 91, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11907, -31770, -92622]
  a := ![23, 21, 68]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22395, 30000, -92622]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-839538945, 1725382318, 828061612]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-839538945, 1725382318, 828061612]] 
 ![![107, 0, 0], ![5, 1, 0], ![31, 0, 1]] where
  M :=![![![-839538945, 1725382318, 828061612], ![15043627204, -17331512091, 9524232296], ![14218613108, -32990041324, -20782276727]]]
  hmulB := by decide  
  f := ![![![674393097396923806061, 8539585993850658898, 30784501836513892820]], ![![35701193314799204183, 452070775296468387, 1629677787936070324]], ![![193049777581125051389, 2444516681904105486, 8812280634875683949]]]
  g := ![![![-328377201, 1725382318, 828061612], ![-1808878631, -17331512091, 9524232296], ![7695508395, -32990041324, -20782276727]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![253951321, -369700210, 22469917]] ![![-839538945, 1725382318, 828061612]]
  ![![107, 0, 0]] where
 M := ![![![-5455343104202337149, 6104343288169531080, -3777799372809914367]]]
 hmul := by decide  
 g := ![![![![-50984514992545207, 57049937272612440, -35306536194485181]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-28, -23, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-28, -23, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![81, 86, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-28, -23, 1], ![-32, -73, -139], ![-334, 512, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-81, -86, 109]], ![![-1, -1, 1], ![103, 109, -139], ![17, 26, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [56, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 108], [0, 1]]
 g := ![![[104, 4], [48], [87, 106], [1, 78], [75], [62, 1]], ![[25, 105], [48], [10, 3], [41, 31], [75], [15, 108]]]
 h' := ![![[62, 108], [36, 107], [33, 87], [53, 18], [89, 80], [16, 82], [0, 1]], ![[0, 1], [21, 2], [86, 22], [79, 91], [35, 29], [86, 27], [62, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [88, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [56, 47, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-92, 158, -168]
  a := ![-1, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![124, 134, -168]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![30, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![30, 1, 0]] 
 ![![109, 0, 0], ![30, 1, 0], ![27, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![30, 1, 0], ![2, 31, 6], ![14, -22, 29]]]
  hmulB := by decide  
  f := ![![![-6369, -110335, -21360], ![-2725, 388040, 0]], ![![-1778, -30343, -5874], ![-653, 106711, 0]], ![![-1587, -27331, -5291], ![-641, 96120, 0]]]
  g := ![![![1, 0, 0], ![-30, 109, 0], ![-27, 0, 109]], ![![0, 1, 0], ![-10, 31, 6], ![-1, -22, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-28, -23, 1]] ![![109, 0, 0], ![30, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![3270, 109, 0]], ![![-3052, -2507, 109], ![-872, -763, -109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![30, 1, 0]]], ![![![-28, -23, 1]], ![![-8, -7, -1]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 14, 12]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-5, 14, 12]] 
 ![![113, 0, 0], ![0, 113, 0], ![9, 20, 1]] where
  M :=![![![-5, 14, 12], ![196, -255, 72], ![52, -236, -283]]]
  hmulB := by decide  
  f := ![![![-789, -10, -36]], ![![-524, -7, -24]], ![![-153, -2, -7]]]
  g := ![![![-1, -2, 12], ![-4, -15, 72], ![23, 48, -283]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [25, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 112], [0, 1]]
 g := ![![[25, 104], [41], [99], [53], [106, 99], [53, 1]], ![[0, 9], [41], [99], [53], [42, 14], [106, 112]]]
 h' := ![![[53, 112], [101, 45], [83, 43], [33, 41], [62, 36], [31, 72], [0, 1]], ![[0, 1], [0, 68], [102, 70], [59, 72], [49, 77], [5, 41], [53, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [20, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [25, 60, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1072, -411, -3936]
  a := ![5, 3, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![304, 693, -3936]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-789, -10, -36]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-789, -10, -36]] 
 ![![113, 0, 0], ![107, 1, 0], ![33, 0, 1]] where
  M :=![![![-789, -10, -36], ![-524, -7, -24], ![292, 4, 13]]]
  hmulB := by decide  
  f := ![![![-5, 14, 12]], ![![-3, 11, 12]], ![![-1, 2, 1]]]
  g := ![![![13, -10, -36], ![9, -7, -24], ![-5, 4, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-5, 14, 12]] ![![-789, -10, -36]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [32, 45, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 40, 76], [85, 86, 51], [0, 1]]
 g := ![![[124, 41, 25], [101, 52, 21], [45, 60, 16], [110, 9, 60], [31, 77, 122], [1]], ![[47, 12, 71, 100], [20, 110, 58, 2], [51, 108, 62, 30], [118, 107, 122, 11], [101, 16, 120, 34], [14, 2, 108, 64]], ![[109, 16, 108, 96], [52, 3, 18, 77], [65, 90, 63, 63], [35, 93, 44, 20], [55, 60, 84, 89], [30, 72, 90, 63]]]
 h' := ![![[96, 40, 76], [70, 85, 5], [84, 18, 104], [36, 37, 123], [24, 86, 106], [95, 82, 54], [0, 1]], ![[85, 86, 51], [111, 102, 32], [18, 92, 25], [101, 29, 55], [38, 45, 31], [114, 72, 81], [96, 40, 76]], ![[0, 1], [80, 67, 90], [5, 17, 125], [63, 61, 76], [45, 123, 117], [9, 100, 119], [85, 86, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 58], []]
 b := ![[], [86, 123, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [32, 45, 73, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2728468, -434975, -8147050]
  a := ![-10, -5, -25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21484, -3425, -64150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63274887, -79176572, 28800622]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![63274887, -79176572, 28800622]] 
 ![![131, 0, 0], ![0, 131, 0], ![97, 9, 1]] where
  M :=![![![63274887, -79176572, 28800622], ![244855564, -649515369, -503860054], ![-1454079472, 1914688316, -491162225]]]
  hmulB := by decide  
  f := ![![![-9799636428264619, -124089108133892, -447330980681026]], ![![-6510811945802148, -82443961415939, -297203668122326]], ![![-7675811578622821, -97195913334897, -350383235758081]]]
  g := ![![![-20842637, -2583070, 28800622], ![374956342, 29658207, -503860054], ![352585163, 48359911, -491162225]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [83, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 130], [0, 1]]
 g := ![![[74, 52], [81, 53], [44], [80], [107], [94], [1]], ![[68, 79], [90, 78], [44], [80], [107], [94], [1]]]
 h' := ![![[15, 130], [89, 24], [8, 70], [56, 100], [43, 39], [4, 99], [48, 15], [0, 1]], ![[0, 1], [56, 107], [10, 61], [115, 31], [104, 92], [48, 32], [11, 116], [15, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [109]]
 b := ![[], [17, 120]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [83, 116, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![503, -2364, -2184]
  a := ![-2, -6, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1621, 132, -2184]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9799636428264619, 124089108133892, 447330980681026]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![9799636428264619, 124089108133892, 447330980681026]] 
 ![![131, 0, 0], ![78, 1, 0], ![65, 0, 1]] where
  M :=![![![9799636428264619, 124089108133892, 447330980681026], ![6510811945802148, 82443961415939, 297203668122326], ![-3630724254297824, -45974494859468, -165734254851845]]]
  hmulB := by decide  
  f := ![![![-63274887, 79176572, -28800622]], ![![-39544250, 52101435, -13302202]], ![![-20296093, 24670144, -10541055]]]
  g := ![![![-221036853056837, 124089108133892, 447330980681026], ![-146855385286964, 82443961415939, 297203668122326], ![81893228321455, -45974494859468, -165734254851845]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![63274887, -79176572, 28800622]] ![![9799636428264619, 124089108133892, 447330980681026]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7028085, 88994, 320816]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![7028085, 88994, 320816]] 
 ![![137, 0, 0], ![0, 137, 0], ![4, 88, 1]] where
  M :=![![![7028085, 88994, 320816], ![4669412, 59127, 213148], ![-2603876, -32972, -118861]]]
  hmulB := by decide  
  f := ![![![157, -214, 40]], ![![132, -937, -1324]], ![![64, -572, -853]]]
  g := ![![![41933, -205422, 320816], ![27860, -136481, 213148], ![-15536, 76108, -118861]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [35, 115, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 136], [0, 1]]
 g := ![![[62, 4], [120], [115], [105, 36], [109], [73], [1]], ![[13, 133], [120], [115], [75, 101], [109], [73], [1]]]
 h' := ![![[22, 136], [75, 135], [113, 95], [24, 72], [114, 6], [40, 66], [102, 22], [0, 1]], ![[0, 1], [31, 2], [11, 42], [101, 65], [109, 131], [122, 71], [38, 115], [22, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [106, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [35, 115, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26529, -8786, -90990]
  a := ![27, 13, 68]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2463, 58382, -90990]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-157, 214, -40]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-157, 214, -40]] 
 ![![137, 0, 0], ![21, 1, 0], ![106, 0, 1]] where
  M :=![![![-157, 214, -40], ![-132, 937, 1324], ![3476, -4948, 509]]]
  hmulB := by decide  
  f := ![![![-7028085, -88994, -320816]], ![![-1111381, -14073, -50732]], ![![-5418782, -68616, -247355]]]
  g := ![![![-3, 214, -40], ![-1169, 937, 1324], ![390, -4948, 509]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![7028085, 88994, 320816]] ![![-157, 214, -40]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB140I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB140I2 : PrimesBelowBoundCertificateInterval O 79 137 140 where
  m := 11
  g := ![2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB140I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![17161, 131]
    · exact ![18769, 137]
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I103N1, I107N1, I109N1, I113N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [], [], [I103N1], [I107N1], [I109N1], [I113N1], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
