
import IdealArithmetic.Examples.NF3_1_536787_1.RI3_1_536787_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-42, 67, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-42, 67, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![155, 67, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-42, 67, 1], ![141, -42, 67], ![9447, 141, -42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-155, -67, 197]], ![![-1, 0, 1], ![-52, -23, 67], ![81, 15, -42]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [5, 172, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 196], [0, 1]]
 g := ![![[192, 23], [156], [71, 25], [190], [28], [53], [25, 1]], ![[176, 174], [156], [105, 172], [190], [28], [53], [50, 196]]]
 h' := ![![[25, 196], [150, 90], [39, 133], [16, 192], [93, 92], [191, 182], [72, 29], [0, 1]], ![[0, 1], [36, 107], [15, 64], [88, 5], [29, 105], [13, 15], [9, 168], [25, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [44, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [5, 172, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![287, -31, -171]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![136, 58, -171]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-67, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-67, 1, 0]] 
 ![![197, 0, 0], ![130, 1, 0], ![42, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-67, 1, 0], ![0, -67, 1], ![141, 0, -67]]]
  hmulB := by decide  
  f := ![![![4959, -74, 0], ![14578, 0, 0]], ![![3284, -49, 0], ![9654, 0, 0]], ![![1162, -17, 0], ![3416, 1, 0]]]
  g := ![![![1, 0, 0], ![-130, 197, 0], ![-42, 0, 197]], ![![-1, 1, 0], ![44, -67, 1], ![15, 0, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-42, 67, 1]] ![![197, 0, 0], ![-67, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-13199, 197, 0]], ![![-8274, 13199, 197], ![2955, -4531, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-67, 1, 0]]], ![![![-42, 67, 1]], ![![15, -23, 0]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [1, 153, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 14, 61], [114, 184, 138], [0, 1]]
 g := ![![[117, 118, 61], [116, 148, 4], [107, 146, 31], [185, 18], [26, 63], [95, 9], [1]], ![[170, 65, 75, 49], [39, 152, 124, 72], [40, 88, 11, 66], [50, 13], [106, 90], [20, 46], [129, 100, 102, 121]], ![[70, 159, 89, 152], [171, 144, 183, 87], [71, 87, 40, 60], [51, 140], [23, 35], [158, 63], [43, 165, 78, 78]]]
 h' := ![![[82, 14, 61], [83, 120, 85], [92, 40, 2], [144, 170, 164], [54, 133, 60], [105, 90, 62], [198, 46, 196], [0, 1]], ![[114, 184, 138], [98, 130, 75], [109, 67, 22], [44, 162, 149], [33, 7, 49], [61, 106, 182], [9, 90, 65], [82, 14, 61]], ![[0, 1], [134, 148, 39], [157, 92, 175], [179, 66, 85], [164, 59, 90], [171, 3, 154], [145, 63, 137], [114, 184, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 116], []]
 b := ![[], [24, 163, 171], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [1, 153, 3, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![535509, 4776, -7164]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2691, 24, -36]
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



lemma PB208I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 207 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 207 (by omega)

def PB208I4 : PrimesBelowBoundCertificateInterval O 193 207 208 where
  m := 2
  g := ![2, 1]
  P := ![197, 199]
  hP := PB208I4_primes
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
