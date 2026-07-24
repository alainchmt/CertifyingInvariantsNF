
import IdealArithmetic.Examples.NF3_1_331240_2.RI3_1_331240_2
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [1, 69, 111, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 78, 61], [121, 60, 78], [0, 1]]
 g := ![![[93, 20, 65], [128, 127, 66], [12, 11], [105, 86, 65], [44, 122], [28, 1], []], ![[96, 83, 47, 103], [17, 80, 136, 15], [12, 46], [39, 12, 77, 104], [101, 124], [108, 125], [2, 107]], ![[4, 57, 55, 45], [15, 129, 61, 6], [79, 1], [40, 51, 4, 71], [137, 41], [122, 107], [124, 107]]]
 h' := ![![[46, 78, 61], [11, 127, 75], [32, 31, 109], [34, 115, 122], [45, 6, 64], [111, 13, 20], [0, 0, 1], [0, 1]], ![[121, 60, 78], [105, 2, 15], [32, 69, 91], [105, 119, 18], [92, 86, 36], [38, 78, 47], [29, 120, 60], [46, 78, 61]], ![[0, 1], [76, 10, 49], [7, 39, 78], [124, 44, 138], [88, 47, 39], [124, 48, 72], [61, 19, 78], [121, 60, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 104], []]
 b := ![[], [93, 63, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [1, 69, 111, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8789109, 51291, -113980]
  a := ![0, 9, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-63231, 369, -820]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![57, 55, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![57, 55, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![57, 55, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![57, 55, 1], ![110, -218, 611], ![6160, 10, 393]]]
  hmulB := by decide  
  f := ![![![-56, -55, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -55, 149]], ![![0, 0, 1], ![-233, -227, 611], ![-109, -145, 393]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [12, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 148], [0, 1]]
 g := ![![[66, 95], [22], [134, 4], [113], [37, 113], [123], [1]], ![[71, 54], [22], [95, 145], [113], [90, 36], [123], [1]]]
 h' := ![![[102, 148], [101, 63], [31, 97], [143, 147], [3, 115], [9, 115], [137, 102], [0, 1]], ![[0, 1], [120, 86], [91, 52], [88, 2], [111, 34], [117, 34], [111, 47], [102, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [141]]
 b := ![[], [55, 145]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [12, 47, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1616, 1690, 1304]
  a := ![-1, -7, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-488, -470, 1304]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-15, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-15, 1, 0]] 
 ![![149, 0, 0], ![134, 1, 0], ![54, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-15, 1, 0], ![0, -20, 11], ![110, 0, -9]]]
  hmulB := by decide  
  f := ![![![481, -32, 0], ![4768, 0, 0]], ![![436, -29, 0], ![4322, 0, 0]], ![![186, 4, -9], ![1844, 122, 0]]]
  g := ![![![1, 0, 0], ![-134, 149, 0], ![-54, 0, 149]], ![![-1, 1, 0], ![14, -20, 11], ![4, 0, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![57, 55, 1]] ![![149, 0, 0], ![-15, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-2235, 149, 0]], ![![8493, 8195, 149], ![-745, -1043, 596]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-15, 1, 0]]], ![![![57, 55, 1]], ![![-5, -7, 4]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-17, -73, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-17, -73, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![134, 78, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-17, -73, 1], ![110, 348, -797], ![-7920, 10, -449]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-134, -78, 151]], ![![-1, -1, 1], ![708, 414, -797], ![346, 232, -449]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [87, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 150], [0, 1]]
 g := ![![[34, 125], [8, 4], [84, 121], [80], [8, 138], [69], [1]], ![[83, 26], [105, 147], [36, 30], [80], [108, 13], [69], [1]]]
 h' := ![![[62, 150], [59, 124], [91, 2], [145, 140], [59, 82], [56, 134], [64, 62], [0, 1]], ![[0, 1], [46, 27], [64, 149], [67, 11], [9, 69], [59, 17], [133, 89], [62, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118]]
 b := ![[], [134, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [87, 89, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1513, -4, 89]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-89, -46, 89]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![42, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![42, 1, 0]] 
 ![![151, 0, 0], ![42, 1, 0], ![147, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![42, 1, 0], ![0, 37, 11], ![110, 0, 48]]]
  hmulB := by decide  
  f := ![![![589, 14, 0], ![-2114, 0, 0]], ![![126, 3, 0], ![-452, 0, 0]], ![![609, 1, -4], ![-2186, 55, 0]]]
  g := ![![![1, 0, 0], ![-42, 151, 0], ![-147, 0, 151]], ![![0, 1, 0], ![-21, 37, 11], ![-46, 0, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-17, -73, 1]] ![![151, 0, 0], ![42, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![6342, 151, 0]], ![![-2567, -11023, 151], ![-604, -2718, -755]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![42, 1, 0]]], ![![![-17, -73, 1]], ![![-4, -18, -5]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![76, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![76, 1, 0]] 
 ![![157, 0, 0], ![76, 1, 0], ![9, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![76, 1, 0], ![0, 71, 11], ![110, 0, 82]]]
  hmulB := by decide  
  f := ![![![989, 13, 0], ![-2041, 0, 0]], ![![380, 5, 0], ![-784, 0, 0]], ![![17, -45, -7], ![-35, 100, 0]]]
  g := ![![![1, 0, 0], ![-76, 157, 0], ![-9, 0, 157]], ![![0, 1, 0], ![-35, 71, 11], ![-4, 0, 82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-46, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-46, 1, 0]] 
 ![![157, 0, 0], ![111, 1, 0], ![115, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-46, 1, 0], ![0, -51, 11], ![110, 0, -40]]]
  hmulB := by decide  
  f := ![![![5751, -125, 0], ![19625, 0, 0]], ![![4141, -90, 0], ![14131, 0, 0]], ![![4209, -59, -7], ![14363, 100, 0]]]
  g := ![![![1, 0, 0], ![-111, 157, 0], ![-115, 0, 157]], ![![-1, 1, 0], ![28, -51, 11], ![30, 0, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-31, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-31, 1, 0]] 
 ![![157, 0, 0], ![126, 1, 0], ![27, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-31, 1, 0], ![0, -36, 11], ![110, 0, -25]]]
  hmulB := by decide  
  f := ![![![2729, -88, 0], ![13816, 0, 0]], ![![2202, -71, 0], ![11148, 0, 0]], ![![525, 6, -7], ![2658, 100, 0]]]
  g := ![![![1, 0, 0], ![-126, 157, 0], ![-27, 0, 157]], ![![-1, 1, 0], ![27, -36, 11], ![5, 0, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![76, 1, 0]] ![![157, 0, 0], ![-46, 1, 0]]
  ![![157, 0, 0], ![39, -12, 1]] where
 M := ![![![24649, 0, 0], ![-7222, 157, 0]], ![![11932, 157, 0], ![-3496, 25, 11]]]
 hmul := by decide  
 g := ![![![![118, 12, -1], ![157, 0, 0]], ![![-46, 1, 0], ![0, 0, 0]]], ![![![37, 13, -1], ![157, 0, 0]], ![![-25, 1, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![39, -12, 1]] ![![157, 0, 0], ![-31, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-4867, 157, 0]], ![![6123, -1884, 157], ![-1099, 471, -157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-31, 1, 0]]], ![![![39, -12, 1]], ![![-7, 3, -1]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)


lemma PB163I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 162 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 162 (by omega)

def PB163I3 : PrimesBelowBoundCertificateInterval O 137 162 163 where
  m := 4
  g := ![1, 2, 2, 3]
  P := ![139, 149, 151, 157]
  hP := PB163I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1, I157N2]
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
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![157, 157, 157]
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
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
  β := ![I149N1, I151N1, I157N0, I157N1, I157N2]
  Il := ![[], [I149N1], [I151N1], [I157N0, I157N1, I157N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
