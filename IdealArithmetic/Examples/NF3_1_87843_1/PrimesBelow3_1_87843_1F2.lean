
import IdealArithmetic.Examples.NF3_1_87843_1.RI3_1_87843_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, -256, 59]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![211, -256, 59]] 
 ![![83, 0, 0], ![0, 83, 0], ![50, 66, 1]] where
  M :=![![![211, -256, 59], ![1770, -1382, -197], ![-5910, 7089, -1579]]]
  hmulB := by decide  
  f := ![![![-43117, -169, -1590]], ![![-47700, -187, -1759]], ![![-64540, -253, -2380]]]
  g := ![![![-33, -50, 59], ![140, 140, -197], ![880, 1341, -1579]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [80, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 82], [0, 1]]
 g := ![![[42, 48], [40, 9], [75], [4], [2, 23], [1]], ![[31, 35], [12, 74], [75], [4], [78, 60], [1]]]
 h' := ![![[43, 82], [37, 31], [39, 3], [48, 65], [6, 81], [3, 43], [0, 1]], ![[0, 1], [42, 52], [2, 80], [21, 18], [3, 2], [26, 40], [43, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [70, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [80, 40, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![170, -91, -63]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40, 49, -63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43117, 169, 1590]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![43117, 169, 1590]] 
 ![![83, 0, 0], ![16, 1, 0], ![76, 0, 1]] where
  M :=![![![43117, 169, 1590], ![47700, 187, 1759], ![52770, 207, 1946]]]
  hmulB := by decide  
  f := ![![![-211, 256, -59]], ![![-62, 66, -9]], ![![-122, 149, -35]]]
  g := ![![![-969, 169, 1590], ![-1072, 187, 1759], ![-1186, 207, 1946]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![211, -256, 59]] ![![43117, 169, 1590]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB84I2_primes (p : ℕ) :
  p ∈ Set.range ![83] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 83 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 83 (by omega)

def PB84I2 : PrimesBelowBoundCertificateInterval O 79 83 84 where
  m := 1
  g := ![2]
  P := ![83]
  hP := PB84I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
  β := ![I83N1]
  Il := ![[I83N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
