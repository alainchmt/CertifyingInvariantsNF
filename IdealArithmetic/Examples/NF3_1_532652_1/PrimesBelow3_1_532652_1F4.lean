
import IdealArithmetic.Examples.NF3_1_532652_1.RI3_1_532652_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![26, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![26, 1, 0]] 
 ![![197, 0, 0], ![26, 1, 0], ![112, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![26, 1, 0], ![0, 26, 1], ![242, 64, 26]]]
  hmulB := by decide  
  f := ![![![3017, 116, 0], ![-22852, 0, 0]], ![![390, 15, 0], ![-2954, 0, 0]], ![![1720, 66, 0], ![-13028, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 197, 0], ![-112, 0, 197]], ![![0, 1, 0], ![-4, 26, 1], ![-22, 64, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![85, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![85, 1, 0]] 
 ![![197, 0, 0], ![85, 1, 0], ![64, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![85, 1, 0], ![0, 85, 1], ![242, 64, 85]]]
  hmulB := by decide  
  f := ![![![3486, 41, 0], ![-8077, 0, 0]], ![![1360, 16, 0], ![-3151, 0, 0]], ![![1142, 13, 0], ![-2646, 1, 0]]]
  g := ![![![1, 0, 0], ![-85, 197, 0], ![-64, 0, 197]], ![![0, 1, 0], ![-37, 85, 1], ![-54, 64, 85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-281, -104, -11]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![-281, -104, -11]] 
 ![![197, 0, 0], ![86, 1, 0], ![90, 0, 1]] where
  M :=![![![-281, -104, -11], ![-2662, -985, -104], ![-25168, -9318, -985]]]
  hmulB := by decide  
  f := ![![![-1153, -58, 19]], ![![-480, -25, 8]], ![![-598, -22, 9]]]
  g := ![![![49, -104, -11], ![464, -985, -104], ![4390, -9318, -985]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![26, 1, 0]] ![![197, 0, 0], ![85, 1, 0]]
  ![![1153, 58, -19]] where
 M := ![![![38809, 0, 0], ![16745, 197, 0]], ![![5122, 197, 0], ![2210, 111, 1]]]
 hmul := by decide  
 g := ![![![![55357, 20488, 2167]], ![![26547, 9825, 1039]]], ![![![9968, 3689, 390]], ![![4780, 1769, 187]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![1153, 58, -19]] ![![-281, -104, -11]]
  ![![197, 0, 0]] where
 M := ![![![-197, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-21, -21, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-21, -21, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![178, 178, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-21, -21, 1], ![242, 43, -21], ![-5082, -1102, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-178, -178, 199]], ![![-1, -1, 1], ![20, 19, -21], ![-64, -44, 43]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [178, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 198], [0, 1]]
 g := ![![[175, 180], [1, 92], [156, 103], [165], [32], [33], [93, 1]], ![[0, 19], [0, 107], [183, 96], [165], [32], [33], [186, 198]]]
 h' := ![![[93, 198], [21, 141], [92, 106], [143, 125], [85, 168], [72, 80], [162, 113], [0, 1]], ![[0, 1], [0, 58], [0, 93], [27, 74], [187, 31], [149, 119], [124, 86], [93, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104]]
 b := ![[], [169, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [178, 106, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![662, 264, -41]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40, 38, -41]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![21, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![21, 1, 0]] 
 ![![199, 0, 0], ![21, 1, 0], ![156, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![21, 1, 0], ![0, 21, 1], ![242, 64, 21]]]
  hmulB := by decide  
  f := ![![![358, 17, 0], ![-3383, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![276, 13, 0], ![-2608, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 199, 0], ![-156, 0, 199]], ![![0, 1, 0], ![-3, 21, 1], ![-22, 64, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-21, -21, 1]] ![![199, 0, 0], ![21, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![4179, 199, 0]], ![![-4179, -4179, 199], ![-199, -398, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![21, 1, 0]]], ![![![-21, -21, 1]], ![![-1, -2, 0]]]]
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


lemma PB207I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 206 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 206 (by omega)

def PB207I4 : PrimesBelowBoundCertificateInterval O 193 206 207 where
  m := 2
  g := ![3, 2]
  P := ![197, 199]
  hP := PB207I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
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
    · exact ![197, 197, 197]
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
      exact NI197N2
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
  β := ![I197N0, I197N1, I197N2, I199N1]
  Il := ![[I197N0, I197N1, I197N2], [I199N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
