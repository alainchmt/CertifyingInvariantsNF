
import IdealArithmetic.Examples.NF3_1_293891_1.RI3_1_293891_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![60, 27, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![60, 27, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![60, 27, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![60, 27, 1], ![91, 34, 27], ![2457, -611, 34]]]
  hmulB := by decide  
  f := ![![![-59, -27, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -27, 139]], ![![0, 0, 1], ![-11, -5, 27], ![3, -11, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [94, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 138], [0, 1]]
 g := ![![[89, 42], [79, 125], [118], [38, 49], [131], [120], [1]], ![[109, 97], [26, 14], [118], [15, 90], [131], [120], [1]]]
 h' := ![![[113, 138], [80, 43], [124, 79], [42, 102], [85, 132], [58, 100], [45, 113], [0, 1]], ![[0, 1], [74, 96], [16, 60], [31, 37], [128, 7], [99, 39], [26, 26], [113, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [62, 101]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [94, 26, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![276, 13, -51]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24, 10, -51]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-27, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-27, 1, 0]] 
 ![![139, 0, 0], ![112, 1, 0], ![105, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-27, 1, 0], ![0, -27, 1], ![91, -26, -27]]]
  hmulB := by decide  
  f := ![![![3052, -113, 0], ![15707, 0, 0]], ![![2512, -93, 0], ![12928, 0, 0]], ![![2328, -86, 0], ![11981, 1, 0]]]
  g := ![![![1, 0, 0], ![-112, 139, 0], ![-105, 0, 139]], ![![-1, 1, 0], ![21, -27, 1], ![42, -26, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![60, 27, 1]] ![![139, 0, 0], ![-27, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-3753, 139, 0]], ![![8340, 3753, 139], ![-1529, -695, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-27, 1, 0]]], ![![![60, 27, 1]], ![![-11, -5, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [105, 95, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 81, 94], [82, 67, 55], [0, 1]]
 g := ![![[25, 124, 42], [98, 82], [99, 51, 145], [143, 112], [46, 5, 25], [139, 1], []], ![[123, 79, 76, 108], [35, 104], [129, 88, 43, 122], [102, 118], [147, 142, 2, 27], [3, 19], [27, 45]], ![[79, 12, 7, 139], [60, 20], [22, 42, 135, 79], [146, 9], [105, 132, 43, 91], [8, 5], [66, 45]]]
 h' := ![![[57, 81, 94], [24, 3, 41], [35, 7, 23], [4, 121, 61], [87, 71, 75], [7, 100, 5], [0, 0, 1], [0, 1]], ![[82, 67, 55], [34, 83, 49], [122, 132, 113], [120, 96, 114], [20, 18, 77], [29, 89, 50], [116, 7, 67], [57, 81, 94]], ![[0, 1], [19, 63, 59], [43, 10, 13], [42, 81, 123], [144, 60, 146], [25, 109, 94], [92, 142, 81], [82, 67, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 72], []]
 b := ![[], [127, 75, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [105, 95, 10, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![342998, -153023, 11026]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2302, -1027, 74]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30, -2, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![30, -2, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![30, 149, 1]] where
  M :=![![![30, -2, 1], ![91, 4, -2], ![-182, 143, 4]]]
  hmulB := by decide  
  f := ![![![2, 1, 0]], ![![0, 2, 1]], ![![1, 2, 1]]]
  g := ![![![0, -1, 1], ![1, 2, -2], ![-2, -3, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [46, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 150], [0, 1]]
 g := ![![[100, 49], [126, 58], [57, 85], [124], [147, 59], [68], [1]], ![[143, 102], [143, 93], [147, 66], [124], [94, 92], [68], [1]]]
 h' := ![![[81, 150], [93, 144], [96, 80], [66, 113], [33, 44], [45, 19], [105, 81], [0, 1]], ![[0, 1], [130, 7], [83, 71], [8, 38], [124, 107], [74, 132], [22, 70], [81, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125]]
 b := ![[], [149, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [46, 70, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-520, 85, 33]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -32, 33]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![2, 1, 0]] 
 ![![151, 0, 0], ![2, 1, 0], ![147, 0, 1]] where
  M :=![![![2, 1, 0], ![0, 2, 1], ![91, -26, 2]]]
  hmulB := by decide  
  f := ![![![30, -2, 1]], ![![1, 0, 0]], ![![28, -1, 1]]]
  g := ![![![0, 1, 0], ![-1, 2, 1], ![-1, -26, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![30, -2, 1]] ![![2, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![151, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB154I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 153 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 153 (by omega)

def PB154I3 : PrimesBelowBoundCertificateInterval O 137 153 154 where
  m := 3
  g := ![2, 1, 2]
  P := ![139, 149, 151]
  hP := PB154I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![22801, 151]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I139N1, I151N1]
  Il := ![[I139N1], [], [I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
