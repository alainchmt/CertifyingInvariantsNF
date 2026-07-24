
import IdealArithmetic.Examples.NF3_1_325983_1.RI3_1_325983_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-25, -62, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-25, -62, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![114, 77, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-25, -62, 1], ![105, -101, -310], ![-6531, 889, -39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-114, -77, 139]], ![![-1, -1, 1], ![255, 171, -310], ![-15, 28, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [68, 26, 1] where
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
 g := ![![[29, 81], [7, 91], [9], [2, 42], [1], [120], [1]], ![[8, 58], [4, 48], [9], [22, 97], [1], [120], [1]]]
 h' := ![![[113, 138], [80, 9], [92, 62], [3, 3], [39, 96], [78, 138], [71, 113], [0, 1]], ![[0, 1], [124, 130], [9, 77], [64, 136], [45, 43], [104, 1], [52, 26], [113, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [2, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [68, 26, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2147, 1149, -1348]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1121, 755, -1348]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![32, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![32, 1, 0]] 
 ![![139, 0, 0], ![32, 1, 0], ![39, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![32, 1, 0], ![0, 33, 5], ![105, -14, 32]]]
  hmulB := by decide  
  f := ![![![3201, 100, 0], ![-13900, 0, 0]], ![![736, 23, 0], ![-3196, 0, 0]], ![![853, 20, -1], ![-3704, 28, 0]]]
  g := ![![![1, 0, 0], ![-32, 139, 0], ![-39, 0, 139]], ![![0, 1, 0], ![-9, 33, 5], ![-5, -14, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-25, -62, 1]] ![![139, 0, 0], ![32, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![4448, 139, 0]], ![![-3475, -8618, 139], ![-695, -2085, -278]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![32, 1, 0]]], ![![![-25, -62, 1]], ![![-5, -15, -2]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [83, 2, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 61, 34], [62, 87, 115], [0, 1]]
 g := ![![[127, 136, 42], [10, 124], [69, 135, 64], [59, 80], [5, 4, 76], [100, 1], []], ![[55, 99, 10, 38], [116, 22], [8, 47, 129, 90], [104, 19], [113, 58, 121, 52], [25, 119], [101, 113]], ![[54, 59, 23, 98], [144, 80], [120, 77], [110, 7], [28, 18, 10, 71], [36, 145], [20, 113]]]
 h' := ![![[38, 61, 34], [117, 74, 41], [84, 131, 71], [1, 47, 141], [32, 104, 123], [44, 15, 15], [0, 0, 1], [0, 1]], ![[62, 87, 115], [40, 88, 123], [70, 43, 52], [83, 111, 8], [85, 69, 82], [84, 48, 27], [64, 121, 87], [38, 61, 34]], ![[0, 1], [81, 136, 134], [115, 124, 26], [45, 140], [58, 125, 93], [60, 86, 107], [98, 28, 61], [62, 87, 115]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 79], []]
 b := ![[], [54, 126, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [83, 2, 49, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![662007, -132759, 42018]
  a := ![-1, 1, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4443, -891, 282]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-32, -62, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-32, -62, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![119, 89, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-32, -62, 1], ![105, -108, -310], ![-6531, 889, -46]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-119, -89, 151]], ![![-1, -1, 1], ![245, 182, -310], ![-7, 33, -46]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [102, 146, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 150], [0, 1]]
 g := ![![[34, 127], [50, 8], [89, 37], [32], [45, 121], [25], [1]], ![[65, 24], [90, 143], [123, 114], [32], [46, 30], [25], [1]]]
 h' := ![![[5, 150], [34, 60], [133, 92], [34, 43], [91, 118], [2, 11], [49, 5], [0, 1]], ![[0, 1], [32, 91], [140, 59], [98, 108], [77, 33], [57, 140], [74, 146], [5, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [138]]
 b := ![[], [54, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [102, 146, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5167, 21, -32]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9, 19, -32]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![8, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![8, 1, 0]] 
 ![![151, 0, 0], ![8, 1, 0], ![46, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![8, 1, 0], ![0, 9, 5], ![105, -14, 8]]]
  hmulB := by decide  
  f := ![![![137, 17, 0], ![-2567, 0, 0]], ![![-8, -1, 0], ![152, 0, 0]], ![![34, -3, -4], ![-636, 121, 0]]]
  g := ![![![1, 0, 0], ![-8, 151, 0], ![-46, 0, 151]], ![![0, 1, 0], ![-2, 9, 5], ![-1, -14, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-32, -62, 1]] ![![151, 0, 0], ![8, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![1208, 151, 0]], ![![-4832, -9362, 151], ![-151, -604, -302]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![8, 1, 0]]], ![![![-32, -62, 1]], ![![-1, -4, -2]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [23, 132, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 110, 109], [131, 46, 48], [0, 1]]
 g := ![![[81, 43, 19], [70, 19], [68, 106, 140], [96, 1, 14], [44, 18, 145], [152, 1], []], ![[115, 44, 67, 48], [87, 13], [109, 63, 46, 140], [110, 13, 125, 11], [64, 42, 97, 115], [42, 75], [57, 106]], ![[121, 137, 53, 118], [62, 140], [97, 124, 129, 89], [130, 16, 28, 9], [26, 75, 98, 67], [40, 11], [118, 106]]]
 h' := ![![[21, 110, 109], [153, 94, 126], [6, 147, 31], [147, 55, 53], [87, 95, 64], [115, 9, 50], [0, 0, 1], [0, 1]], ![[131, 46, 48], [52, 102, 28], [144, 32, 22], [94, 29, 112], [96, 146, 111], [136, 5, 141], [72, 153, 46], [21, 110, 109]], ![[0, 1], [128, 118, 3], [45, 135, 104], [132, 73, 149], [7, 73, 139], [31, 143, 123], [3, 4, 110], [131, 46, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118, 105], []]
 b := ![[], [125, 57, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [23, 132, 5, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2246356, 644014, -314942]
  a := ![1, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14308, 4102, -2006]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀



lemma PB162I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 161 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 161 (by omega)

def PB162I3 : PrimesBelowBoundCertificateInterval O 137 161 162 where
  m := 4
  g := ![2, 1, 2, 1]
  P := ![139, 149, 151, 157]
  hP := PB162I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![3869893]
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
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
  β := ![I139N1, I151N1]
  Il := ![[I139N1], [], [I151N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
