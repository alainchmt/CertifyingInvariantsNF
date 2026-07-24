
import IdealArithmetic.Examples.NF3_1_463091_1.RI3_1_463091_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [7, 26, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 22, 36], [6, 14, 1], [0, 1]]
 g := ![![[2, 27, 16], [33, 4], [2, 24, 1], [29, 1], []], ![[9, 16, 3, 12], [18, 34], [31, 2, 4, 33], [11, 11], [22, 1]], ![[29, 11, 26, 1], [16, 11], [8, 20, 32, 1], [16, 3], [20, 1]]]
 h' := ![![[23, 22, 36], [2, 13, 33], [23, 30, 35], [19, 16, 1], [0, 0, 1], [0, 1]], ![[6, 14, 1], [22, 34, 5], [0, 16, 16], [22, 8, 35], [5, 26, 14], [23, 22, 36]], ![[0, 1], [15, 27, 36], [4, 28, 23], [11, 13, 1], [7, 11, 22], [6, 14, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 10], []]
 b := ![[], [3, 16, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [7, 26, 8, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16761, -407, -407]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-453, -11, -11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [18, 22, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 38, 31], [9, 2, 10], [0, 1]]
 g := ![![[13, 28, 18], [29, 2], [24, 16], [9, 21, 1], []], ![[32, 4, 30, 25], [35, 23], [34, 21], [39, 4, 22, 1], [28, 18]], ![[37, 10], [1, 40], [2, 23], [33, 28, 23, 8], [8, 18]]]
 h' := ![![[12, 38, 31], [7, 3, 10], [23, 37, 17], [2, 39, 37], [0, 0, 1], [0, 1]], ![[9, 2, 10], [10, 39, 31], [5, 28, 33], [24, 36, 12], [9, 13, 2], [12, 38, 31]], ![[0, 1], [19, 40], [23, 17, 32], [31, 7, 33], [19, 28, 38], [9, 2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 25], []]
 b := ![[], [21, 0, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [18, 22, 20, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![407294, 51373, -5863]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9934, 1253, -143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1717, -374, -70]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-1717, -374, -70]] 
 ![![43, 0, 0], ![0, 43, 0], ![19, 25, 1]] where
  M :=![![![-1717, -374, -70], ![-9170, -1997, -374], ![-48994, -10666, -1997]]]
  hmulB := by decide  
  f := ![![![25, 6, -2]], ![![-262, 17, 6]], ![![-123, 7, 3]]]
  g := ![![![-9, 32, -70], ![-48, 171, -374], ![-257, 913, -1997]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [1, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 42], [0, 1]]
 g := ![![[9, 1], [9, 1], [4], [20, 38], [1]], ![[0, 42], [0, 42], [4], [22, 5], [1]]]
 h' := ![![[34, 42], [34, 42], [9, 1], [23, 41], [42, 34], [0, 1]], ![[0, 1], [0, 1], [0, 42], [41, 2], [37, 9], [34, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [1, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [1, 9, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3259, 4, 124]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21, -72, 124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -6, 2]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-25, -6, 2]] 
 ![![43, 0, 0], ![18, 1, 0], ![20, 0, 1]] where
  M :=![![![-25, -6, 2], ![262, -17, -6], ![-786, 238, -17]]]
  hmulB := by decide  
  f := ![![![1717, 374, 70]], ![![932, 203, 38]], ![![1938, 422, 79]]]
  g := ![![![1, -6, 2], ![16, -17, -6], ![-110, 238, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-1717, -374, -70]] ![![-25, -6, 2]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![169782, 34815, -12470]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![169782, 34815, -12470]] 
 ![![47, 0, 0], ![8, 1, 0], ![30, 0, 1]] where
  M :=![![![169782, 34815, -12470], ![-1633570, 119902, 34815], ![4560765, -1494310, 119902]]]
  hmulB := by decide  
  f := ![![![-66400892254, -14459657570, -2707262165]], ![![-18848052801, -4104408542, -768462870]], ![![-82685998070, -18005951085, -3371229912]]]
  g := ![![![5646, 34815, -12470], ![-77388, 119902, 34815], ![274855, -1494310, 119902]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2812, 190, 63]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-2812, 190, 63]] 
 ![![47, 0, 0], ![31, 1, 0], ![26, 0, 1]] where
  M :=![![![-2812, 190, 63], ![8253, -2560, 190], ![24890, 9013, -2560]]]
  hmulB := by decide  
  f := ![![![4841130, 1054219, 197380]], ![![3743230, 815137, 152617]], ![![5616427, 1223050, 228990]]]
  g := ![![![-220, 190, 63], ![1759, -2560, 190], ![-3999, 9013, -2560]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![169782, 34815, -12470]] ![![169782, 34815, -12470]]
  ![![-84919551576, 28719394160, -2400275255]] where
 M := ![![![-84919551576, 28719394160, -2400275255]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-84919551576, 28719394160, -2400275255]] ![![-2812, 190, 63]]
  ![![47, 0, 0]] where
 M := ![![![416072087937242, -111290044722355, 6251457793912]]]
 hmul := by decide  
 g := ![![![![8852597615686, -2367873291965, 133009740296]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17783, 45146, -9076]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![17783, 45146, -9076]] 
 ![![53, 0, 0], ![0, 53, 0], ![6, 13, 1]] where
  M :=![![![17783, 45146, -9076], ![-1188956, -18521, 45146], ![5914126, -1008372, -18521]]]
  hmulB := by decide  
  f := ![![![-865414901, -188455346, -35284240]], ![![-4622235440, -1006551861, -188455346]], ![![-1697532084, -369659681, -69210883]]]
  g := ![![![1363, 3078, -9076], ![-27544, -11423, 45146], ![113684, -14483, -18521]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [28, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 52], [0, 1]]
 g := ![![[21, 36], [29], [35, 44], [9], [48, 1]], ![[0, 17], [29], [27, 9], [9], [43, 52]]]
 h' := ![![[48, 52], [23, 47], [27, 33], [3, 16], [34, 50], [0, 1]], ![[0, 1], [0, 6], [21, 20], [29, 37], [49, 3], [48, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [36, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [28, 5, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-752, 1162, 16]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16, 18, 16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![865414901, 188455346, 35284240]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![865414901, 188455346, 35284240]] 
 ![![53, 0, 0], ![40, 1, 0], ![43, 0, 1]] where
  M :=![![![865414901, 188455346, 35284240], ![4622235440, 1006551861, 188455346], ![24687650326, 5376056824, 1006551861]]]
  hmulB := by decide  
  f := ![![![-17783, -45146, 9076]], ![![9012, -33723, 5998]], ![![-126015, -17602, 7713]]]
  g := ![![![-154528703, 188455346, 35284240], ![-825347526, 1006551861, 188455346], ![-4408233069, 5376056824, 1006551861]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![17783, 45146, -9076]] ![![865414901, 188455346, 35284240]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![164, -4, -5]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![164, -4, -5]] 
 ![![59, 0, 0], ![5, 1, 0], ![34, 0, 1]] where
  M :=![![![164, -4, -5], ![-655, 144, -4], ![-524, -671, 144]]]
  hmulB := by decide  
  f := ![![![18052, 3931, 736]], ![![3164, 689, 129]], ![![19131, 4166, 780]]]
  g := ![![![6, -4, -5], ![-21, 144, -4], ![-35, -671, 144]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![74, 16, 3]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![74, 16, 3]] 
 ![![59, 0, 0], ![27, 1, 0], ![38, 0, 1]] where
  M :=![![![74, 16, 3], ![393, 86, 16], ![2096, 457, 86]]]
  hmulB := by decide  
  f := ![![![84, -5, -2]], ![![34, -1, -1]], ![![43, -8, 0]]]
  g := ![![![-8, 16, 3], ![-43, 86, 16], ![-229, 457, 86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![164, -4, -5]] ![![74, 16, 3]]
  ![![84, -5, -2]] where
 M := ![![![84, -5, -2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![84, -5, -2]] ![![74, 16, 3]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32, 6, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![32, 6, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![32, 6, 1]] where
  M :=![![![32, 6, 1], ![131, 36, 6], ![786, 155, 36]]]
  hmulB := by decide  
  f := ![![![6, -1, 0]], ![![0, 6, -1]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![-1, 0, 6], ![-6, -1, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [10, 27, 1] where
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
 g := ![![[21, 1], [60], [4, 45], [7, 47], [34, 1]], ![[55, 60], [60], [9, 16], [19, 14], [7, 60]]]
 h' := ![![[34, 60], [24, 1], [21, 11], [52, 17], [26, 48], [0, 1]], ![[0, 1], [58, 60], [29, 50], [20, 44], [11, 13], [34, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [29, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [10, 27, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![272, 112, -22]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, 4, -22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-6, 1, 0]] 
 ![![61, 0, 0], ![55, 1, 0], ![25, 0, 1]] where
  M :=![![![-6, 1, 0], ![0, -6, 1], ![131, 4, -6]]]
  hmulB := by decide  
  f := ![![![-32, -6, -1]], ![![-31, -6, -1]], ![![-26, -5, -1]]]
  g := ![![![-1, 1, 0], ![5, -6, 1], ![1, 4, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![32, 6, 1]] ![![-6, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3868583, 270880, -186328]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![3868583, 270880, -186328]] 
 ![![67, 0, 0], ![0, 67, 0], ![64, 1, 1]] where
  M :=![![![3868583, 270880, -186328], ![-24408968, 3123271, 270880], ![35485280, -23325448, 3123271]]]
  hmulB := by decide  
  f := ![![![-239898792443, -52241080992, -9781027064]], ![![-1281314545384, -279022900699, -52241080992]], ![![-350424162264, -76309417217, -14287309161]]]
  g := ![![![235725, 6824, -186328], ![-623064, 42573, 270880], ![-2453792, -394757, 3123271]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [44, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 66], [0, 1]]
 g := ![![[52, 39], [56, 14], [1], [62], [33], [1]], ![[64, 28], [50, 53], [1], [62], [33], [1]]]
 h' := ![![[57, 66], [15, 46], [63, 9], [43, 1], [15, 14], [23, 57], [0, 1]], ![[0, 1], [24, 21], [40, 58], [33, 66], [9, 53], [56, 10], [57, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [16, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [44, 10, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5033, 511, 377]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-285, 2, 377]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-239898792443, -52241080992, -9781027064]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-239898792443, -52241080992, -9781027064]] 
 ![![67, 0, 0], ![66, 1, 0], ![66, 0, 1]] where
  M :=![![![-239898792443, -52241080992, -9781027064], ![-1281314545384, -279022900699, -52241080992], ![-6843581609952, -1490278869352, -279022900699]]]
  hmulB := by decide  
  f := ![![![3868583, 270880, -186328]], ![![3446530, 313453, -179504]], ![![4340474, -81304, -136931]]]
  g := ![![![57515825959, -52241080992, -9781027064], ![307195645466, -279022900699, -52241080992], ![1640751271842, -1490278869352, -279022900699]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![3868583, 270880, -186328]] ![![-239898792443, -52241080992, -9781027064]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31424521, 6843098, 1281224]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![31424521, 6843098, 1281224]] 
 ![![71, 0, 0], ![0, 71, 0], ![34, 31, 1]] where
  M :=![![![31424521, 6843098, 1281224], ![167840344, 36549417, 6843098], ![896445838, 195212736, 36549417]]]
  hmulB := by decide  
  f := ![![![-3609, 1338, -124]], ![![-16244, -4105, 1338]], ![![-6352, -1305, 467]]]
  g := ![![![-170945, -463026, 1281224], ![-913028, -2473051, 6843098], ![-4876540, -13208721, 36549417]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [2, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 70], [0, 1]]
 g := ![![[68, 36], [53, 3], [58, 18], [15], [36], [1]], ![[0, 35], [0, 68], [24, 53], [15], [36], [1]]]
 h' := ![![[6, 70], [36, 65], [26, 43], [50, 35], [3, 50], [69, 6], [0, 1]], ![[0, 1], [0, 6], [0, 28], [47, 36], [19, 21], [34, 65], [6, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [56, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [2, 65, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-848, 296, -50]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, 26, -50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3609, -1338, 124]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![3609, -1338, 124]] 
 ![![71, 0, 0], ![40, 1, 0], ![33, 0, 1]] where
  M :=![![![3609, -1338, 124], ![16244, 4105, -1338], ![-175278, 10892, 4105]]]
  hmulB := by decide  
  f := ![![![-31424521, -6843098, -1281224]], ![![-20067904, -4370047, -818198]], ![![-27231761, -5930070, -1110279]]]
  g := ![![![747, -1338, 124], ![-1462, 4105, -1338], ![-10513, 10892, 4105]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![31424521, 6843098, 1281224]] ![![3609, -1338, 124]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![392483, 1230686, -244178]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![392483, 1230686, -244178]] 
 ![![73, 0, 0], ![0, 73, 0], ![5, 70, 1]] where
  M :=![![![392483, 1230686, -244178], ![-31987318, -584229, 1230686], ![161219866, -27064574, -584229]]]
  hmulB := by decide  
  f := ![![![-460949532085, -100377753442, -18793591258]], ![![-2461960454798, -536123897117, -100377753442]], ![![-2572485824619, -560192233342, -104884035539]]]
  g := ![![![22101, 251002, -244178], ![-522476, -1188113, 1230686], ![2248507, 189472, -584229]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [62, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 72], [0, 1]]
 g := ![![[20, 32], [27], [23], [31, 18], [1], [1]], ![[52, 41], [27], [23], [49, 55], [1], [1]]]
 h' := ![![[1, 72], [24, 18], [26, 63], [49, 60], [59, 23], [11, 1], [0, 1]], ![[0, 1], [42, 55], [16, 10], [36, 13], [9, 50], [12, 72], [1, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [13, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [62, 72, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![586, 612, 161]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, -146, 161]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-460949532085, -100377753442, -18793591258]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-460949532085, -100377753442, -18793591258]] 
 ![![73, 0, 0], ![3, 1, 0], ![64, 0, 1]] where
  M :=![![![-460949532085, -100377753442, -18793591258], ![-2461960454798, -536123897117, -100377753442], ![-13149485700902, -2863471468566, -536123897117]]]
  hmulB := by decide  
  f := ![![![392483, 1230686, -244178]], ![![-422053, 42573, 6824]], ![![2552586, 708210, -222077]]]
  g := ![![![14287309161, -100377753442, -18793591258], ![76309417217, -536123897117, -100377753442], ![407573398908, -2863471468566, -536123897117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![392483, 1230686, -244178]] ![![-460949532085, -100377753442, -18793591258]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-108827837737, -23698676544, -4437071214]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-108827837737, -23698676544, -4437071214]] 
 ![![79, 0, 0], ![0, 79, 0], ![18, 38, 1]] where
  M :=![![![-108827837737, -23698676544, -4437071214], ![-581256329034, -126576122593, -23698676544], ![-3104526627264, -676051035210, -126576122593]]]
  hmulB := by decide  
  f := ![![![-252271, 77388, -5646]], ![![-739626, -274855, 77388]], ![![-284922, -120020, 32459]]]
  g := ![![![-366589315, 1834304172, -4437071214], ![-1957976598, 9797134001, -23698676544], ![-10457676210, 52327109156, -126576122593]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [25, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 78], [0, 1]]
 g := ![![[30, 19], [6, 67], [55, 67], [36, 67], [20], [1]], ![[0, 60], [0, 12], [49, 12], [30, 12], [20], [1]]]
 h' := ![![[40, 78], [8, 63], [47, 64], [48, 64], [46, 64], [54, 40], [0, 1]], ![[0, 1], [0, 16], [0, 15], [1, 15], [78, 15], [74, 39], [40, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [39, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [25, 39, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5133, -66, 202]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-111, -98, 202]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-252271, 77388, -5646]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-252271, 77388, -5646]] 
 ![![79, 0, 0], ![41, 1, 0], ![57, 0, 1]] where
  M :=![![![-252271, 77388, -5646], ![-739626, -274855, 77388], ![10137828, -430074, -274855]]]
  hmulB := by decide  
  f := ![![![-108827837737, -23698676544, -4437071214]], ![![-63837945269, -13901542543, -2602767042]], ![![-117819156687, -25656653142, -4803660529]]]
  g := ![![![-39283, 77388, -5646], ![77447, -274855, 77388], ![549843, -430074, -274855]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-108827837737, -23698676544, -4437071214]] ![![-252271, 77388, -5646]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB193I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB193I1 : PrimesBelowBoundCertificateInterval O 31 79 193 where
  m := 11
  g := ![1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB193I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
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
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I43N1, I47N0, I47N1, I53N1, I59N0, I59N1, I61N1, I67N1, I71N1, I73N1, I79N1]
  Il := ![[], [], [I43N1], [I47N0, I47N0, I47N1], [I53N1], [I59N0, I59N1, I59N1], [I61N1], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
