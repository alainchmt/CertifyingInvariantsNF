
import IdealArithmetic.Examples.NF3_1_547575_2.RI3_1_547575_2
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [14, 112, 150, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 111, 188], [18, 85, 9], [0, 1]]
 g := ![![[12, 189, 7], [80, 33], [136, 85, 34], [42, 171], [40, 101], [114, 42], [1]], ![[50, 71, 147, 43], [78, 142], [8, 89, 168, 85], [142, 33], [177, 93], [104, 174], [112, 64, 196, 59]], ![[158, 107, 158, 6], [69, 112], [80, 105, 34, 55], [137, 168], [188, 36], [6, 62], [151, 47, 152, 138]]]
 h' := ![![[29, 111, 188], [84, 122, 106], [66, 132, 128], [177, 84, 25], [78, 190, 163], [176, 24, 62], [183, 85, 47], [0, 1]], ![[18, 85, 9], [141, 33, 32], [144, 168, 39], [6, 148, 187], [40, 103, 128], [96, 167, 129], [166, 72, 78], [29, 111, 188]], ![[0, 1], [62, 42, 59], [35, 94, 30], [140, 162, 182], [65, 101, 103], [147, 6, 6], [172, 40, 72], [18, 85, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81, 75], []]
 b := ![[], [90, 84, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [14, 112, 150, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![58706, -120170, -97909]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![298, -610, -497]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-22, -91, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-22, -91, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![177, 108, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-22, -91, 1], ![24, -154, -182], ![-2196, 3743, -63]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-177, -108, 199]], ![![-1, -1, 1], ![162, 98, -182], ![45, 53, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [17, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 198], [0, 1]]
 g := ![![[146, 16], [97, 5], [189, 80], [65], [1], [188], [105, 1]], ![[35, 183], [25, 194], [32, 119], [65], [1], [188], [11, 198]]]
 h' := ![![[105, 198], [142, 195], [170, 76], [140, 105], [161, 57], [24, 198], [6, 63], [0, 1]], ![[0, 1], [120, 4], [190, 123], [21, 94], [176, 142], [118, 1], [54, 136], [105, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [158, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [17, 94, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-76, -43, -286]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![254, 155, -286]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-17, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-17, 1, 0]] 
 ![![199, 0, 0], ![182, 1, 0], ![63, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-17, 1, 0], ![0, -16, 2], ![24, -41, -17]]]
  hmulB := by decide  
  f := ![![![1599, -94, 0], ![18706, 0, 0]], ![![1446, -85, 0], ![16916, 0, 0]], ![![511, -22, -1], ![5978, 100, 0]]]
  g := ![![![1, 0, 0], ![-182, 199, 0], ![-63, 0, 199]], ![![-1, 1, 0], ![14, -16, 2], ![43, -41, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-22, -91, 1]] ![![199, 0, 0], ![-17, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-3383, 199, 0]], ![![-4378, -18109, 199], ![398, 1393, -199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-17, 1, 0]]], ![![![-22, -91, 1]], ![![2, 7, -1]]]]
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


lemma PB210I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 209 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 209 (by omega)

def PB210I4 : PrimesBelowBoundCertificateInterval O 193 209 210 where
  m := 2
  g := ![1, 2]
  P := ![197, 199]
  hP := PB210I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
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
    · exact ![7645373]
    · exact ![39601, 199]
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
      exact NI199N1
  β := ![I199N1]
  Il := ![[], [I199N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
