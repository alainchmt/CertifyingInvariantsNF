
import IdealArithmetic.Examples.NF3_3_895700_1.RI3_3_895700_1
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [12, 181, 151, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 169, 18], [144, 27, 179], [0, 1]]
 g := ![![[41, 155, 104], [186, 81], [156, 94, 133], [153, 37], [131, 178], [111, 146], [1]], ![[194, 113, 163, 32], [193, 143], [190, 153, 3, 94], [79, 76], [165, 53], [171, 146], [14, 44, 125, 119]], ![[126, 99, 39, 74], [175, 175], [120, 137, 184, 126], [5, 36], [71, 156], [], [158, 168, 85, 78]]]
 h' := ![![[99, 169, 18], [83, 100, 33], [98, 131, 188], [158, 48, 85], [40, 143, 49], [191, 34, 93], [185, 16, 46], [0, 1]], ![[144, 27, 179], [77, 179, 130], [134, 158, 145], [187, 61, 7], [97, 97, 154], [86, 29, 168], [103, 69, 151], [99, 169, 18]], ![[0, 1], [122, 115, 34], [152, 105, 61], [131, 88, 105], [114, 154, 191], [93, 134, 133], [129, 112], [144, 27, 179]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [189, 38], []]
 b := ![[], [194, 37, 173], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [12, 181, 151, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-375679, 100273, -2364]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1907, 509, -12]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [56, 147, 131, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 106, 142], [176, 92, 57], [0, 1]]
 g := ![![[73, 189, 106], [54, 174, 196], [13, 77, 94], [185, 63], [138, 117], [119, 47], [1]], ![[118, 45, 138, 168], [166, 171, 46, 136], [119, 28, 46, 141], [158, 126], [19, 177], [112, 122], [88, 8, 167, 76]], ![[93, 94, 165, 145], [17, 138, 143, 175], [187, 87, 6, 7], [38, 57], [68, 196], [122, 131], [114, 197, 36, 123]]]
 h' := ![![[91, 106, 142], [160, 76, 107], [68, 86, 185], [90, 159, 166], [163, 52, 62], [54, 120, 52], [143, 52, 68], [0, 1]], ![[176, 92, 57], [86, 96, 139], [47, 161, 178], [142, 138, 40], [45, 139, 153], [121, 183, 133], [5, 139, 108], [91, 106, 142]], ![[0, 1], [67, 27, 152], [42, 151, 35], [96, 101, 192], [45, 8, 183], [79, 95, 14], [155, 8, 23], [176, 92, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126, 90], []]
 b := ![[], [34, 8, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [56, 147, 131, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13431903, -5604835, 1226835]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![67497, -28165, 6165]
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



lemma PB211I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 210 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 210 (by omega)

def PB211I4 : PrimesBelowBoundCertificateInterval O 193 210 211 where
  m := 2
  g := ![1, 1]
  P := ![197, 199]
  hP := PB211I4_primes
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
