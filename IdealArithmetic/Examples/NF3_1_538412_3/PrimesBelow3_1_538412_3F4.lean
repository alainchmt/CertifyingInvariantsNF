
import IdealArithmetic.Examples.NF3_1_538412_3.RI3_1_538412_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-325, -41, -32]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-325, -41, -32]] 
 ![![197, 0, 0], ![0, 197, 0], ![4, 69, 1]] where
  M :=![![![-325, -41, -32], ![-4654, -595, -474], ![-7892, -995, -791]]]
  hmulB := by decide  
  f := ![![![5, 3, -2]], ![![-302, -23, 26]], ![![-104, -8, 9]]]
  g := ![![![-1, 11, -32], ![-14, 163, -474], ![-24, 272, -791]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [135, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 196], [0, 1]]
 g := ![![[179, 54], [92], [53, 93], [191], [107], [161], [66, 1]], ![[0, 143], [92], [84, 104], [191], [107], [161], [132, 196]]]
 h' := ![![[66, 196], [20, 137], [134, 180], [136, 129], [36, 114], [187, 111], [152, 84], [0, 1]], ![[0, 1], [0, 60], [194, 17], [179, 68], [74, 83], [27, 86], [180, 113], [66, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [9, 143]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [135, 131, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1692, 425, -365]
  a := ![1, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, 130, -365]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 3, -2]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![5, 3, -2]] 
 ![![197, 0, 0], ![96, 1, 0], ![43, 0, 1]] where
  M :=![![![5, 3, -2], ![-302, -23, 26], ![330, -1, -13]]]
  hmulB := by decide  
  f := ![![![-325, -41, -32]], ![![-182, -23, -18]], ![![-111, -14, -11]]]
  g := ![![![-1, 3, -2], ![4, -23, 26], ![5, -1, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-325, -41, -32]] ![![5, 3, -2]]
  ![![197, 0, 0]] where
 M := ![![![197, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![64, -88, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![64, -88, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![64, 111, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![64, -88, 1], ![324, 251, -878], ![-12967, -951, -100]]]
  hmulB := by decide  
  f := ![![![-63, 88, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -111, 199]], ![![0, -1, 1], ![284, 491, -878], ![-33, 51, -100]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [194, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [112, 198], [0, 1]]
 g := ![![[102, 196], [114, 40], [131, 53], [66], [123], [144], [112, 1]], ![[164, 3], [17, 159], [97, 146], [66], [123], [144], [25, 198]]]
 h' := ![![[112, 198], [172, 14], [58, 55], [178, 124], [68, 128], [99, 116], [162, 12], [0, 1]], ![[0, 1], [148, 185], [49, 144], [136, 75], [76, 71], [156, 83], [113, 187], [112, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162]]
 b := ![[], [41, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [194, 87, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9656, 1337, 3456]
  a := ![-3, -5, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1160, -1921, 3456]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![82, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![82, 1, 0]] 
 ![![199, 0, 0], ![82, 1, 0], ![100, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![82, 1, 0], ![-2, 80, 10], ![148, 11, 84]]]
  hmulB := by decide  
  f := ![![![-3255, 140083, 17510], ![-597, -348449, 0]], ![![-1360, 57681, 7210], ![-198, -143479, 0]], ![![-1674, 70393, 8799], ![-207, -175100, 0]]]
  g := ![![![1, 0, 0], ![-82, 199, 0], ![-100, 0, 199]], ![![0, 1, 0], ![-38, 80, 10], ![-46, 11, 84]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![64, -88, 1]] ![![199, 0, 0], ![82, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![16318, 199, 0]], ![![12736, -17512, 199], ![5572, -6965, -796]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![82, 1, 0]]], ![![![64, -88, 1]], ![![28, -35, -4]]]]
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


lemma PB208I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 207 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 207 (by omega)

def PB208I4 : PrimesBelowBoundCertificateInterval O 193 207 208 where
  m := 2
  g := ![2, 2]
  P := ![197, 199]
  hP := PB208I4_primes
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
