
import IdealArithmetic.Examples.NF3_1_132328_2.RI3_1_132328_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![12, 27, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![12, 27, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![12, 27, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![12, 27, 1], ![55, 20, 53], ![1430, -476, -33]]]
  hmulB := by decide  
  f := ![![![-11, -27, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -27, 83]], ![![0, 0, 1], ![-7, -17, 53], ![22, 5, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [16, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 82], [0, 1]]
 g := ![![[3, 26], [20, 36], [30], [27], [6, 63], [1]], ![[0, 57], [35, 47], [30], [27], [53, 20], [1]]]
 h' := ![![[35, 82], [12, 21], [48, 77], [69, 14], [70, 39], [67, 35], [0, 1]], ![[0, 1], [0, 62], [4, 6], [61, 69], [24, 44], [47, 48], [35, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [48, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [16, 48, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![181, 13, -310]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![47, 101, -310]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![30, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![30, 1, 0]] 
 ![![83, 0, 0], ![30, 1, 0], ![33, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![30, 1, 0], ![0, 31, 2], ![55, -19, 29]]]
  hmulB := by decide  
  f := ![![![421, 14, 0], ![-1162, 0, 0]], ![![150, 5, 0], ![-414, 0, 0]], ![![171, -10, -1], ![-472, 42, 0]]]
  g := ![![![1, 0, 0], ![-30, 83, 0], ![-33, 0, 83]], ![![0, 1, 0], ![-12, 31, 2], ![-4, -19, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![12, 27, 1]] ![![83, 0, 0], ![30, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2490, 83, 0]], ![![996, 2241, 83], ![415, 830, 83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![30, 1, 0]]], ![![![12, 27, 1]], ![![5, 10, 1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-142147, 88082, -41702]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-142147, 88082, -41702]] 
 ![![89, 0, 0], ![0, 89, 0], ![43, 86, 1]] where
  M :=![![![-142147, 88082, -41702], ![-2293610, 738273, 217866], ![7138120, -3216532, 520407]]]
  hmulB := by decide  
  f := ![![![-12190734807, -992104810, -561545322]], ![![-30884992710, -2513478499, -1422664298]], ![![-35999907209, -2929739812, -1658274075]]]
  g := ![![![18551, 41286, -41702], ![-131032, -202227, 217866], ![-171229, -539006, 520407]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [62, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 88], [0, 1]]
 g := ![![[40, 32], [88], [53], [39, 85], [62, 55], [1]], ![[68, 57], [88], [53], [80, 4], [10, 34], [1]]]
 h' := ![![[12, 88], [41, 11], [54, 34], [74, 26], [72, 21], [27, 12], [0, 1]], ![[0, 1], [84, 78], [17, 55], [30, 63], [57, 68], [82, 77], [12, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [17, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [62, 77, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-454, 516, 6]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, 0, 6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12190734807, -992104810, -561545322]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-12190734807, -992104810, -561545322]] 
 ![![89, 0, 0], ![7, 1, 0], ![61, 0, 1]] where
  M :=![![![-12190734807, -992104810, -561545322], ![-30884992710, -2513478499, -1422664298], ![-23680771840, -1927185524, -1090814201]]]
  hmulB := by decide  
  f := ![![![-142147, 88082, -41702]], ![![-36951, 15223, -832]], ![![-17223, 24230, -22735]]]
  g := ![![![325935545, -992104810, -561545322], ![825751449, -2513478499, -1422664298], ![633137001, -1927185524, -1090814201]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-142147, 88082, -41702]] ![![-12190734807, -992104810, -561545322]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-31, 9, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-31, 9, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![66, 9, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-31, 9, 1], ![55, -41, 17], ![440, -134, -58]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -9, 97]], ![![-1, 0, 1], ![-11, -2, 17], ![44, 4, -58]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [11, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 96], [0, 1]]
 g := ![![[40, 53], [16], [11], [31], [44], [45, 1]], ![[0, 44], [16], [11], [31], [44], [90, 96]]]
 h' := ![![[45, 96], [72, 76], [65, 4], [63, 60], [4, 15], [87, 74], [0, 1]], ![[0, 1], [0, 21], [51, 93], [47, 37], [0, 82], [22, 23], [45, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [91, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [11, 52, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![724, 37, 58]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, -5, 58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-17, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-17, 1, 0]] 
 ![![97, 0, 0], ![80, 1, 0], ![58, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-17, 1, 0], ![0, -16, 2], ![55, -19, -18]]]
  hmulB := by decide  
  f := ![![![987, -58, 0], ![5626, 0, 0]], ![![834, -49, 0], ![4754, 0, 0]], ![![614, -28, -1], ![3500, 49, 0]]]
  g := ![![![1, 0, 0], ![-80, 97, 0], ![-58, 0, 97]], ![![-1, 1, 0], ![12, -16, 2], ![27, -19, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-31, 9, 1]] ![![97, 0, 0], ![-17, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1649, 97, 0]], ![![-3007, 873, 97], ![582, -194, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-17, 1, 0]]], ![![![-31, 9, 1]], ![![6, -2, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8254578, 671773, 380233]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![8254578, 671773, 380233]] 
 ![![101, 0, 0], ![0, 101, 0], ![30, 94, 1]] where
  M :=![![![8254578, 671773, 380233], ![20912815, 1701924, 963313], ![16034700, 1304934, 738611]]]
  hmulB := by decide  
  f := ![![![-978, 419, -43]], ![![-2365, 258, 881]], ![![-2240, 270, 801]]]
  g := ![![![-31212, -347229, 380233], ![-79075, -879698, 963313], ![-60630, -674500, 738611]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [27, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 100], [0, 1]]
 g := ![![[58, 78], [9], [58, 17], [33], [78], [50, 1]], ![[19, 23], [9], [100, 84], [33], [78], [100, 100]]]
 h' := ![![[50, 100], [35, 49], [50, 98], [9, 57], [71, 72], [64, 49], [0, 1]], ![[0, 1], [61, 52], [1, 3], [31, 44], [35, 29], [90, 52], [50, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [30, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [27, 51, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-196, 443, -727]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![214, 681, -727]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-978, 419, -43]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-978, 419, -43]] 
 ![![101, 0, 0], ![15, 1, 0], ![82, 0, 1]] where
  M :=![![![-978, 419, -43], ![-2365, 258, 881], ![25410, -9552, -623]]]
  hmulB := by decide  
  f := ![![![8254578, 671773, 380233]], ![![1432985, 116619, 66008]], ![![6860496, 558320, 316017]]]
  g := ![![![-37, 419, -43], ![-777, 258, 881], ![2176, -9552, -623]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![8254578, 671773, 380233]] ![![-978, 419, -43]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB103I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 102 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 102 (by omega)

def PB103I2 : PrimesBelowBoundCertificateInterval O 79 102 103 where
  m := 4
  g := ![2, 2, 2, 2]
  P := ![83, 89, 97, 101]
  hP := PB103I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
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
      exact NI101N1
  β := ![I83N1, I89N1, I97N1, I101N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
