
import IdealArithmetic.Examples.NF3_1_504175_1.RI3_1_504175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![106396594, 32175793, 2483602]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![106396594, 32175793, 2483602]] 
 ![![197, 0, 0], ![0, 197, 0], ![2, 179, 1]] where
  M :=![![![106396594, 32175793, 2483602], ![1378399110, 416846844, 32175793], ![17857565115, 5400373235, 416846844]]]
  hmulB := by decide  
  f := ![![![104873, 9874, -1387]], ![![-769785, -68502, 9874]], ![![-670567, -59785, 8610]]]
  g := ![![![514870, -2093345, 2483602], ![6670292, -27119899, 32175793], ![86415591, -351346253, 416846844]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [42, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 196], [0, 1]]
 g := ![![[130, 61], [136], [132, 62], [144], [142], [15], [56, 1]], ![[0, 136], [136], [58, 135], [144], [142], [15], [112, 196]]]
 h' := ![![[56, 196], [194, 88], [169, 50], [37, 72], [136, 185], [105, 39], [12, 139], [0, 1]], ![[0, 1], [0, 109], [14, 147], [129, 125], [55, 12], [122, 158], [113, 58], [56, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [171, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [42, 141, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1152, 664, -15]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, 17, -15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![104873, 9874, -1387]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![104873, 9874, -1387]] 
 ![![197, 0, 0], ![18, 1, 0], ![70, 0, 1]] where
  M :=![![![104873, 9874, -1387], ![-769785, -68502, 9874], ![5480070, 464465, -68502]]]
  hmulB := by decide  
  f := ![![![106396594, 32175793, 2483602]], ![![16718466, 5055894, 390257]], ![![128453435, 38846085, 2998472]]]
  g := ![![![123, 9874, -1387], ![-1157, -68502, 9874], ![9720, 464465, -68502]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![106396594, 32175793, 2483602]] ![![104873, 9874, -1387]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0]] 
 ![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [86, 164, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 59, 9], [115, 139, 190], [0, 1]]
 g := ![![[150, 76, 122], [158, 155, 102], [32, 24, 125], [195, 92], [5, 58], [112, 13], [1]], ![[85, 149, 62, 132], [132, 175, 94, 70], [175, 132, 110, 66], [187, 161], [134, 50], [107, 66], [20, 131, 108, 132]], ![[128, 17, 7, 147], [50, 194, 39, 30], [69, 134, 18, 109], [194, 98], [150, 65], [113, 86], [128, 39, 47, 67]]]
 h' := ![![[35, 59, 9], [143, 122, 108], [34, 191, 163], [90, 110, 18], [187, 174, 93], [152, 165, 43], [113, 35, 150], [0, 1]], ![[115, 139, 190], [95, 128, 190], [132, 160, 98], [169, 5, 109], [27, 10, 165], [3, 3, 99], [161, 95, 71], [35, 59, 9]], ![[0, 1], [192, 148, 100], [126, 47, 137], [95, 84, 72], [137, 15, 140], [163, 31, 57], [54, 69, 177], [115, 139, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170, 108], []]
 b := ![[], [185, 178, 187], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [86, 164, 49, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4259595, 3082112, 448546]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21405, 15488, 2254]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def PBC199 : ContainsPrimesAboveP 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![199, 0, 0]]) timesTableT_eq_Table B_one_repr 199 (by decide) 𝕀



lemma PB201I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 200 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 200 (by omega)

def PB201I4 : PrimesBelowBoundCertificateInterval O 193 200 201 where
  m := 2
  g := ![2, 1]
  P := ![197, 199]
  hP := PB201I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
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
    · exact ![7880599]
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
  β := ![I197N1]
  Il := ![[I197N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
