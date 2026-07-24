
import IdealArithmetic.Examples.NF3_1_524291_1.RI3_1_524291_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![25, 17, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![25, 17, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![25, 17, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![25, 17, 1], ![174, 8, 70], ![2485, 35, 60]]]
  hmulB := by decide  
  f := ![![![-24, -17, -1], ![197, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -17, 197]], ![![0, 0, 1], ![-8, -6, 70], ![5, -5, 60]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [14, 115, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 196], [0, 1]]
 g := ![![[163, 196], [135], [27, 138], [138], [59], [144], [82, 1]], ![[81, 1], [135], [114, 59], [138], [59], [144], [164, 196]]]
 h' := ![![[82, 196], [139, 183], [16, 23], [23, 170], [24, 170], [125, 16], [34, 12], [0, 1]], ![[0, 1], [173, 14], [129, 174], [173, 27], [174, 27], [58, 181], [33, 185], [82, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [184]]
 b := ![[], [168, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [14, 115, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1780, 1368, -638]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![90, 62, -638]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-70, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-70, 1, 0]] 
 ![![197, 0, 0], ![127, 1, 0], ![137, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-70, 1, 0], ![2, -71, 4], ![140, 0, -68]]]
  hmulB := by decide  
  f := ![![![18141, -773138, 43560], ![-10244, -2145330, 0]], ![![11731, -498387, 28080], ![-6500, -1382940, 0]], ![![12651, -537665, 30293], ![-7025, -1491930, 0]]]
  g := ![![![1, 0, 0], ![-127, 197, 0], ![-137, 0, 197]], ![![-1, 1, 0], ![43, -71, 4], ![48, 0, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![25, 17, 1]] ![![197, 0, 0], ![-70, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-13790, 197, 0]], ![![4925, 3349, 197], ![-1576, -1182, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-70, 1, 0]]], ![![![25, 17, 1]], ![![-8, -6, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-30, -31, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-30, -31, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![169, 168, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-30, -31, 1], ![78, 1, -122], ![-4235, 35, -91]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-169, -168, 199]], ![![-1, -1, 1], ![104, 103, -122], ![56, 77, -91]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [168, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 198], [0, 1]]
 g := ![![[54, 145], [91, 114], [121, 145], [26], [94], [121], [82, 1]], ![[4, 54], [86, 85], [71, 54], [26], [94], [121], [164, 198]]]
 h' := ![![[82, 198], [35, 155], [169, 78], [136, 155], [153, 15], [5, 166], [154, 188], [0, 1]], ![[0, 1], [9, 44], [197, 121], [110, 44], [189, 184], [85, 33], [48, 11], [82, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131]]
 b := ![[], [1, 165]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [168, 117, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-189, 1337, 862]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-733, -721, 862]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-77, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-77, 1, 0]] 
 ![![199, 0, 0], ![122, 1, 0], ![91, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-77, 1, 0], ![2, -78, 4], ![140, 0, -75]]]
  hmulB := by decide  
  f := ![![![-8507, 415868, -21328], ![5572, 1061068, 0]], ![![-5226, 254887, -13072], ![3384, 650332, 0]], ![![-3906, 190171, -9753], ![2507, 485212, 0]]]
  g := ![![![1, 0, 0], ![-122, 199, 0], ![-91, 0, 199]], ![![-1, 1, 0], ![46, -78, 4], ![35, 0, -75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-30, -31, 1]] ![![199, 0, 0], ![-77, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-15323, 199, 0]], ![![-5970, -6169, 199], ![2388, 2388, -199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-77, 1, 0]]], ![![![-30, -31, 1]], ![![12, 12, -1]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)


lemma PB205I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 204 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 204 (by omega)

def PB205I4 : PrimesBelowBoundCertificateInterval O 193 204 205 where
  m := 2
  g := ![2, 2]
  P := ![197, 199]
  hP := PB205I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![39601, 199]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
  β := ![I197N1, I199N1]
  Il := ![[I197N1], [I199N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
