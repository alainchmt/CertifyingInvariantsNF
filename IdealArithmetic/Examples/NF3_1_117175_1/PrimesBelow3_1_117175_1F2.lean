
import IdealArithmetic.Examples.NF3_1_117175_1.RI3_1_117175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [41, 17, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 37, 35], [38, 45, 48], [0, 1]]
 g := ![![[24, 6, 77], [78, 68, 1], [11, 17], [43, 16], [76, 50, 1], []], ![[44, 51, 10, 54], [71, 79, 77, 50], [28, 23], [33, 81], [49, 28, 69, 76], [13, 63]], ![[29, 63, 21, 27], [44, 12, 55, 30], [7, 10], [13, 25], [66, 81, 28, 59], [0, 63]]]
 h' := ![![[12, 37, 35], [39, 46, 34], [50, 9, 1], [13, 12, 10], [38, 61, 4], [0, 0, 1], [0, 1]], ![[38, 45, 48], [64, 53, 69], [18, 77, 28], [2, 42, 40], [44, 71, 74], [26, 76, 45], [12, 37, 35]], ![[0, 1], [4, 67, 63], [10, 80, 54], [52, 29, 33], [81, 34, 5], [33, 7, 37], [38, 45, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 63], []]
 b := ![[], [82, 39, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [41, 17, 33, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4316, 83, -1494]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![52, 1, -18]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4425016, 260478, 160043]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![4425016, 260478, 160043]] 
 ![![89, 0, 0], ![0, 89, 0], ![69, 20, 1]] where
  M :=![![![4425016, 260478, 160043], ![7201935, 423941, 260478], ![11721510, 689985, 423941]]]
  hmulB := by decide  
  f := ![![![659, -387, -11]], ![![-495, 934, -387]], ![![204, 13, -85]]]
  g := ![![![-74359, -33038, 160043], ![-121023, -53771, 260478], ![-196971, -87515, 423941]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [28, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 88], [0, 1]]
 g := ![![[85, 73], [10], [49], [28, 22], [21, 84], [1]], ![[73, 16], [10], [49], [0, 67], [84, 5], [1]]]
 h' := ![![[23, 88], [34, 42], [74, 30], [17, 7], [35, 72], [61, 23], [0, 1]], ![[0, 1], [21, 47], [52, 59], [0, 82], [0, 17], [56, 66], [23, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [85, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [28, 66, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-577, 577, -29]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, 13, -29]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-659, 387, 11]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-659, 387, 11]] 
 ![![89, 0, 0], ![69, 1, 0], ![45, 0, 1]] where
  M :=![![![-659, 387, 11], ![495, -934, 387], ![17415, -9180, -934]]]
  hmulB := by decide  
  f := ![![![-4425016, -260478, -160043]], ![![-3511551, -206707, -127005]], ![![-2369070, -139455, -85684]]]
  g := ![![![-313, 387, 11], ![534, -934, 387], ![7785, -9180, -934]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![4425016, 260478, 160043]] ![![-659, 387, 11]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB97I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 96 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 96 (by omega)

def PB97I2 : PrimesBelowBoundCertificateInterval O 79 96 97 where
  m := 2
  g := ![1, 2]
  P := ![83, 89]
  hP := PB97I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
  β := ![I89N1]
  Il := ![[], [I89N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
