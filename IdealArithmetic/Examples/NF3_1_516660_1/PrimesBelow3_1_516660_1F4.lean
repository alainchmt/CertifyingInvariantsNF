
import IdealArithmetic.Examples.NF3_1_516660_1.RI3_1_516660_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4324, 909, -457]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![4324, 909, -457]] 
 ![![197, 0, 0], ![0, 197, 0], ![144, 70, 1]] where
  M :=![![![4324, 909, -457], ![-90486, -8477, 5454], ![195063, 12189, -9386]]]
  hmulB := by decide  
  f := ![![![66428, 15033, 5501]], ![![1089198, 246491, 90198]], ![![449769, 101785, 37246]]]
  g := ![![![356, 167, -457], ![-4446, -1981, 5454], ![7851, 3397, -9386]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [186, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [122, 196], [0, 1]]
 g := ![![[29, 161], [135], [185, 163], [138], [175], [19], [122, 1]], ![[168, 36], [135], [174, 34], [138], [175], [19], [47, 196]]]
 h' := ![![[122, 196], [194, 84], [65, 174], [47, 44], [156, 27], [2, 136], [160, 120], [0, 1]], ![[0, 1], [1, 113], [17, 23], [96, 153], [101, 170], [46, 61], [25, 77], [122, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [42, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [186, 75, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4905, 5167, 2829]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2043, -979, 2829]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-66428, -15033, -5501]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-66428, -15033, -5501]] 
 ![![197, 0, 0], ![171, 1, 0], ![23, 0, 1]] where
  M :=![![![-66428, -15033, -5501], ![-1089198, -246491, -90198], ![-2795001, -632523, -231458]]]
  hmulB := by decide  
  f := ![![![-4324, -909, 457]], ![![-3294, -746, 369]], ![![-1495, -168, 101]]]
  g := ![![![13354, -15033, -5501], ![218961, -246491, -90198], ![561878, -632523, -231458]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![4324, 909, -457]] ![![-66428, -15033, -5501]]
  ![![197, 0, 0]] where
 M := ![![![-197, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![52, 81, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![52, 81, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![52, 81, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![52, 81, 1], ![198, 163, 486], ![16005, 2463, 82]]]
  hmulB := by decide  
  f := ![![![-51, -81, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -81, 199]], ![![0, 0, 1], ![-126, -197, 486], ![59, -21, 82]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [17, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [133, 198], [0, 1]]
 g := ![![[39, 51], [118, 121], [193, 140], [91], [126], [128], [133, 1]], ![[56, 148], [92, 78], [107, 59], [91], [126], [128], [67, 198]]]
 h' := ![![[133, 198], [183, 161], [102, 188], [88, 109], [178, 115], [23, 153], [127, 160], [0, 1]], ![[0, 1], [104, 38], [32, 11], [58, 90], [150, 84], [74, 46], [114, 39], [133, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [14, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [17, 66, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1008, 2657, 2438]
  a := ![-1, 1, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-632, -979, 2438]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-88, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-88, 1, 0]] 
 ![![199, 0, 0], ![111, 1, 0], ![117, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-88, 1, 0], ![0, -87, 6], ![198, 30, -88]]]
  hmulB := by decide  
  f := ![![![16105, -183, 0], ![36417, 0, 0]], ![![8977, -102, 0], ![20299, 0, 0]], ![![9467, -35, -5], ![21407, 166, 0]]]
  g := ![![![1, 0, 0], ![-111, 199, 0], ![-117, 0, 199]], ![![-1, 1, 0], ![45, -87, 6], ![36, 30, -88]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![52, 81, 1]] ![![199, 0, 0], ![-88, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-17512, 199, 0]], ![![10348, 16119, 199], ![-4378, -6965, 398]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-88, 1, 0]]], ![![![52, 81, 1]], ![![-22, -35, 2]]]]
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


lemma PB204I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 203 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 203 (by omega)

def PB204I4 : PrimesBelowBoundCertificateInterval O 193 203 204 where
  m := 2
  g := ![2, 2]
  P := ![197, 199]
  hP := PB204I4_primes
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
