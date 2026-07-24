
import IdealArithmetic.Examples.NF3_1_32780_1.RI3_1_32780_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-7, 12, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-7, 12, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![30, 12, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-7, 12, 1], ![10, -33, 62], ![436, -18, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -12, 37]], ![![-1, 0, 1], ![-50, -21, 62], ![-2, -6, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [31, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 36], [0, 1]]
 g := ![![[], [1], [], [], [1]], ![[], [1], [], [], [1]]]
 h' := ![![[0, 36], [6], [0, 1], [36], [6], [0, 1]], ![[0, 1], [6], [0, 36], [36], [6], [0, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [0, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [31, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![393, 172, -35]
  a := ![2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![39, 16, -35]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![12, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![12, 1, 0]] 
 ![![37, 0, 0], ![12, 1, 0], ![20, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![12, 1, 0], ![-2, 10, 5], ![34, -2, 14]]]
  hmulB := by decide  
  f := ![![![577, -3063, -1530], ![111, 11322, 0]], ![![186, -991, -495], ![38, 3663, 0]], ![![308, -1656, -827], ![72, 6120, 0]]]
  g := ![![![1, 0, 0], ![-12, 37, 0], ![-20, 0, 37]], ![![0, 1, 0], ![-6, 10, 5], ![-6, -2, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-7, 12, 1]] ![![37, 0, 0], ![12, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![444, 37, 0]], ![![-259, 444, 37], ![-74, 111, 74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![12, 1, 0]]], ![![![-7, 12, 1]], ![![-2, 3, 2]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![18, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![18, 1, 0]] 
 ![![41, 0, 0], ![18, 1, 0], ![24, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![18, 1, 0], ![-2, 16, 5], ![34, -2, 20]]]
  hmulB := by decide  
  f := ![![![1013, -8966, -2800], ![246, 22960, 0]], ![![436, -3923, -1225], ![124, 10045, 0]], ![![582, -5249, -1639], ![169, 13440, 0]]]
  g := ![![![1, 0, 0], ![-18, 41, 0], ![-24, 0, 41]], ![![0, 1, 0], ![-10, 16, 5], ![-10, -2, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 0, 3]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-23, 0, 3]] 
 ![![41, 0, 0], ![26, 1, 0], ![6, 0, 1]] where
  M :=![![![-23, 0, 3], ![102, -29, 6], ![84, 18, -23]]]
  hmulB := by decide  
  f := ![![![-559, -54, -87]], ![![-424, -41, -66]], ![![-186, -18, -29]]]
  g := ![![![-1, 0, 3], ![20, -29, 6], ![-6, 18, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-3, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-3, 1, 0]] 
 ![![41, 0, 0], ![38, 1, 0], ![13, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-3, 1, 0], ![-2, -5, 5], ![34, -2, -1]]]
  hmulB := by decide  
  f := ![![![271, 675, -675], ![0, 5535, 0]], ![![251, 625, -625], ![1, 5125, 0]], ![![86, 214, -214], ![1, 1755, 0]]]
  g := ![![![1, 0, 0], ![-38, 41, 0], ![-13, 0, 41]], ![![-1, 1, 0], ![3, -5, 5], ![3, -2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![18, 1, 0]] ![![-23, 0, 3]]
  ![![41, 0, 0], ![3, -8, 1]] where
 M := ![![![-943, 0, 123]], ![![-312, -29, 60]]]
 hmul := by decide  
 g := ![![![![-23, 0, 3], ![0, 0, 0]]], ![![![-9, 3, 1], ![19, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![3, -8, 1]] ![![41, 0, 0], ![-3, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-123, 41, 0]], ![![123, -328, 41], ![41, 41, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-3, 1, 0]]], ![![![3, -8, 1]], ![![1, 1, -1]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-4, 12, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-4, 12, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![39, 12, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-4, 12, 1], ![10, -30, 62], ![436, -18, 20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -12, 43]], ![![-1, 0, 1], ![-56, -18, 62], ![-8, -6, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [17, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 42], [0, 1]]
 g := ![![[26, 38], [19, 41], [6], [13, 15], [1]], ![[0, 5], [0, 2], [6], [5, 28], [1]]]
 h' := ![![[31, 42], [21, 34], [20, 16], [37, 7], [26, 31], [0, 1]], ![[0, 1], [0, 9], [0, 27], [39, 36], [41, 12], [31, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [27, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [17, 12, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1796, 1088, -67]
  a := ![-5, -7, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19, 44, -67]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-19, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-19, 1, 0]] 
 ![![43, 0, 0], ![24, 1, 0], ![23, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-19, 1, 0], ![-2, -21, 5], ![34, -2, -17]]]
  hmulB := by decide  
  f := ![![![485, 5483, -1305], ![-86, 11223, 0]], ![![272, 3046, -725], ![-42, 6235, 0]], ![![274, 2932, -698], ![-13, 6003, 0]]]
  g := ![![![1, 0, 0], ![-24, 43, 0], ![-23, 0, 43]], ![![-1, 1, 0], ![9, -21, 5], ![11, -2, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-4, 12, 1]] ![![43, 0, 0], ![-19, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-817, 43, 0]], ![![-172, 516, 43], ![86, -258, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-19, 1, 0]]], ![![![-4, 12, 1]], ![![2, -6, 1]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![4, 14, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![4, 14, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![4, 14, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![4, 14, 1], ![6, -26, 72], ![504, -22, 32]]]
  hmulB := by decide  
  f := ![![![-3, -14, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -14, 47]], ![![0, 0, 1], ![-6, -22, 72], ![8, -10, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [37, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 46], [0, 1]]
 g := ![![[22, 14], [33, 21], [23, 36], [38, 37], [1]], ![[0, 33], [0, 26], [0, 11], [0, 10], [1]]]
 h' := ![![[32, 46], [1, 22], [42, 31], [4, 41], [10, 32], [0, 1]], ![[0, 1], [0, 25], [0, 16], [0, 6], [0, 15], [32, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [23, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [37, 15, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![185525, 286521, -59310]
  a := ![66, 67, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8995, 23763, -59310]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![22, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![22, 1, 0]] 
 ![![47, 0, 0], ![22, 1, 0], ![15, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![22, 1, 0], ![-2, 20, 5], ![34, -2, 24]]]
  hmulB := by decide  
  f := ![![![821, -9305, -2325], ![235, 21855, 0]], ![![390, -4342, -1085], ![95, 10199, 0]], ![![255, -2970, -742], ![90, 6975, 0]]]
  g := ![![![1, 0, 0], ![-22, 47, 0], ![-15, 0, 47]], ![![0, 1, 0], ![-11, 20, 5], ![-6, -2, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![4, 14, 1]] ![![47, 0, 0], ![22, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![1034, 47, 0]], ![![188, 658, 47], ![94, 282, 94]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![22, 1, 0]]], ![![![4, 14, 1]], ![![2, 6, 2]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)


lemma PB52I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 51 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 51 (by omega)

def PB52I1 : PrimesBelowBoundCertificateInterval O 31 51 52 where
  m := 4
  g := ![2, 3, 2, 2]
  P := ![37, 41, 43, 47]
  hP := PB52I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1369, 37]
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
  β := ![I37N1, I41N0, I41N1, I41N2, I43N1, I47N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [I43N1], [I47N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
