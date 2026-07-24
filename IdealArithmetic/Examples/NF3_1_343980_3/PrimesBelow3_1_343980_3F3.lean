
import IdealArithmetic.Examples.NF3_1_343980_3.RI3_1_343980_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [27, 9, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 98, 120], [25, 40, 19], [0, 1]]
 g := ![![[107, 101, 57], [18, 45, 47], [32, 86], [35, 12, 38], [61, 96], [55, 1], []], ![[98, 19, 13, 54], [32, 128, 15, 34], [116, 11], [114, 79, 76, 121], [32, 118], [31, 71], [7, 83]], ![[39, 117, 130, 53], [73, 65, 83, 115], [122, 51], [131, 130, 51, 95], [127, 25], [101, 13], [108, 83]]]
 h' := ![![[30, 98, 120], [70, 19, 125], [59, 74, 73], [28, 38, 15], [11, 129, 90], [44, 34, 97], [0, 0, 1], [0, 1]], ![[25, 40, 19], [138, 31, 52], [111, 30, 124], [18, 96, 17], [39, 48, 37], [114, 63, 37], [16, 101, 40], [30, 98, 120]], ![[0, 1], [93, 89, 101], [76, 35, 81], [112, 5, 107], [125, 101, 12], [94, 42, 5], [72, 38, 98], [25, 40, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 1], []]
 b := ![[], [93, 46, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [27, 9, 84, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17375, 1251, 1251]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-125, 9, 9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [106, 99, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 67, 129], [30, 81, 20], [0, 1]]
 g := ![![[64, 63, 20], [86, 103], [65, 94, 121], [33, 114], [112, 10, 19], [100, 1], []], ![[3, 68, 130, 86], [29, 17], [61, 87, 51, 120], [62, 47], [118, 28, 35, 104], [117, 5], [70, 102]], ![[131, 49, 62, 1], [8, 119], [57, 145, 105, 67], [89, 119], [135, 70, 80, 124], [140, 19], [30, 102]]]
 h' := ![![[70, 67, 129], [77, 0, 13], [113, 144, 38], [147, 31, 138], [48, 64, 73], [128, 126, 67], [0, 0, 1], [0, 1]], ![[30, 81, 20], [97, 64, 10], [108, 24, 49], [88, 40, 128], [113, 143, 14], [134, 84, 76], [13, 131, 81], [70, 67, 129]], ![[0, 1], [88, 85, 126], [41, 130, 62], [82, 78, 32], [24, 91, 62], [148, 88, 6], [104, 18, 67], [30, 81, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 127], []]
 b := ![[], [48, 89, 133], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [106, 99, 49, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![204875, 299788, 58408]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1375, 2012, 392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-2, -77, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-2, -77, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![149, 74, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-2, -77, 1], ![154, 40, -77], ![-11858, -3080, 40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-149, -74, 151]], ![![-1, -1, 1], ![77, 38, -77], ![-118, -40, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [26, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 150], [0, 1]]
 g := ![![[114, 72], [42, 97], [46, 91], [81], [17, 90], [116], [1]], ![[69, 79], [38, 54], [8, 60], [81], [74, 61], [116], [1]]]
 h' := ![![[56, 150], [116, 125], [12, 90], [129, 53], [11, 9], [76, 111], [125, 56], [0, 1]], ![[0, 1], [19, 26], [69, 61], [77, 98], [62, 142], [101, 40], [90, 95], [56, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [55, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [26, 95, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2266, 37, 76]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-90, -37, 76]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-74, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-74, 1, 0]] 
 ![![151, 0, 0], ![77, 1, 0], ![111, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-74, 1, 0], ![0, -74, 1], ![154, 42, -74]]]
  hmulB := by decide  
  f := ![![![9473, -128, 0], ![19328, 0, 0]], ![![4811, -65, 0], ![9816, 0, 0]], ![![6993, -94, 0], ![14268, 1, 0]]]
  g := ![![![1, 0, 0], ![-77, 151, 0], ![-111, 0, 151]], ![![-1, 1, 0], ![37, -74, 1], ![34, 42, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-2, -77, 1]] ![![151, 0, 0], ![-74, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-11174, 151, 0]], ![![-302, -11627, 151], ![302, 5738, -151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-74, 1, 0]]], ![![![-2, -77, 1]], ![![2, 38, -1]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-88, -41, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-88, -41, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![69, 116, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-88, -41, 1], ![154, -46, -41], ![-6314, -1568, -46]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-69, -116, 157]], ![![-1, -1, 1], ![19, 30, -41], ![-20, 24, -46]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [14, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [124, 156], [0, 1]]
 g := ![![[36, 101], [46], [104, 1], [89, 25], [94, 4], [147], [1]], ![[0, 56], [46], [71, 156], [49, 132], [119, 153], [147], [1]]]
 h' := ![![[124, 156], [106, 27], [114, 108], [10, 156], [97, 152], [22, 155], [143, 124], [0, 1]], ![[0, 1], [0, 130], [4, 49], [43, 1], [105, 5], [88, 2], [133, 33], [124, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [119]]
 b := ![[], [79, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [14, 33, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-876, 1169, 274]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-126, -195, 274]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![41, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![41, 1, 0]] 
 ![![157, 0, 0], ![41, 1, 0], ![46, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![41, 1, 0], ![0, 41, 1], ![154, 42, 41]]]
  hmulB := by decide  
  f := ![![![862, 21, 0], ![-3297, 0, 0]], ![![164, 4, 0], ![-627, 0, 0]], ![![216, 5, 0], ![-826, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 157, 0], ![-46, 0, 157]], ![![0, 1, 0], ![-11, 41, 1], ![-22, 42, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-88, -41, 1]] ![![157, 0, 0], ![41, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![6437, 157, 0]], ![![-13816, -6437, 157], ![-3454, -1727, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![41, 1, 0]]], ![![![-88, -41, 1]], ![![-22, -11, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [124, 119, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 84, 48], [78, 78, 115], [0, 1]]
 g := ![![[46, 113, 85], [40, 64, 115], [21, 74], [157, 15], [150, 145], [91, 79, 1], []], ![[114, 66, 152, 8], [84, 132, 2, 79], [117, 156], [102, 60], [118, 83], [20, 96, 157, 99], [22, 22]], ![[25, 64, 143, 33], [5, 77, 67, 43], [110, 146], [57, 15], [31, 15], [18, 125, 7, 26], [118, 22]]]
 h' := ![![[1, 84, 48], [93, 72, 133], [39, 110, 142], [19, 160, 20], [47, 111, 129], [126, 76, 109], [0, 0, 1], [0, 1]], ![[78, 78, 115], [149, 18, 138], [40, 129, 56], [81, 19, 112], [129, 45, 68], [108, 94, 88], [44, 38, 78], [1, 84, 48]], ![[0, 1], [45, 73, 55], [25, 87, 128], [138, 147, 31], [69, 7, 129], [162, 156, 129], [91, 125, 84], [78, 78, 115]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107, 98], []]
 b := ![[], [99, 150, 127], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [124, 119, 84, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17278, 1141, 1141]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-106, 7, 7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀



lemma PB166I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 165 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 165 (by omega)

def PB166I3 : PrimesBelowBoundCertificateInterval O 137 165 166 where
  m := 5
  g := ![1, 1, 2, 2, 1]
  P := ![139, 149, 151, 157, 163]
  hP := PB166I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![4330747]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
  β := ![I151N1, I157N1]
  Il := ![[], [], [I151N1], [I157N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
