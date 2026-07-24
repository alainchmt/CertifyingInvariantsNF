
import IdealArithmetic.Examples.NF3_3_815925_1.RI3_3_815925_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0]] 
 ![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [28, 40, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 112, 71], [106, 84, 126], [0, 1]]
 g := ![![[76, 97, 188], [63, 158], [77, 18, 15], [174, 150], [67, 134], [73, 143], [1]], ![[117, 130, 39, 122], [144, 39], [177, 92, 79, 68], [145, 134], [36, 171], [93, 60], [120, 147, 173, 159]], ![[124, 17, 150, 3], [159, 107], [83, 174, 137, 27], [16, 47], [9, 55], [80, 53], [149, 193, 70, 38]]]
 h' := ![![[39, 112, 71], [130, 12, 42], [11, 155, 143], [169, 85, 58], [71, 100, 97], [119, 44, 118], [169, 157, 145], [0, 1]], ![[106, 84, 126], [193, 47, 46], [132, 3, 165], [26, 196, 72], [151, 151, 79], [78, 27, 34], [11, 184, 81], [39, 112, 71]], ![[0, 1], [119, 138, 109], [51, 39, 86], [137, 113, 67], [114, 143, 21], [184, 126, 45], [116, 53, 168], [106, 84, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137, 102], []]
 b := ![[], [33, 152, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [28, 40, 52, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-58115, -89241, -234430]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-295, -453, -1190]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀

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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [99, 167, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [125, 71, 156], [193, 127, 43], [0, 1]]
 g := ![![[51, 101, 92], [188, 118, 128], [189, 122, 193], [35, 102], [26, 46], [81, 32], [1]], ![[136, 66, 136, 134], [136, 29, 42, 27], [104, 92, 156, 82], [150, 155], [194, 36], [98, 36], [198, 197, 138, 93]], ![[173, 16, 138, 2], [100, 128, 85, 162], [133, 118, 191, 65], [176, 140], [82, 66], [178, 103], [174, 141, 86, 106]]]
 h' := ![![[125, 71, 156], [94, 130, 106], [194, 143, 39], [197, 71, 118], [94, 100, 36], [190, 53, 65], [100, 32, 119], [0, 1]], ![[193, 127, 43], [198, 120, 111], [196, 69, 197], [132, 130, 192], [183, 195, 73], [177, 24, 6], [39, 16, 6], [125, 71, 156]], ![[0, 1], [164, 148, 181], [58, 186, 162], [139, 197, 88], [38, 103, 90], [14, 122, 128], [70, 151, 74], [193, 127, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [184, 58], []]
 b := ![[], [109, 85, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [99, 167, 80, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![332529, -280590, 613517]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1671, -1410, 3083]
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
  g := ![1, 1]
  P := ![197, 199]
  hP := PB201I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
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
    · exact ![7645373]
    · exact ![7880599]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
  β := ![]
  Il := ![[], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
