
import IdealArithmetic.Examples.NF3_3_902356_1.RI3_3_902356_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1581, 10551, 3677]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![1581, 10551, 3677]] 
 ![![197, 0, 0], ![106, 1, 0], ![96, 0, 1]] where
  M :=![![![1581, 10551, 3677], ![21102, 140827, 49078], ![51478, 343546, 119725]]]
  hmulB := by decide  
  f := ![![![38013, -167, -1099]], ![![20452, -93, -590]], ![![18446, -72, -537]]]
  g := ![![![-7461, 10551, 3677], ![-99584, 140827, 49078], ![-242934, 343546, 119725]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![829, -5529, 2241]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![829, -5529, 2241]] 
 ![![197, 0, 0], ![139, 1, 0], ![9, 0, 1]] where
  M :=![![![829, -5529, 2241], ![-11058, 73735, -29886], ![31374, -209202, 84793]]]
  hmulB := by decide  
  f := ![![![-883, 1185, 441]], ![![-611, 916, 339]], ![![-9, 249, 88]]]
  g := ![![![3803, -5529, 2241], ![-50717, 73735, -29886], ![143895, -209202, 84793]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -5, -2]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![-1, -5, -2]] 
 ![![197, 0, 0], ![149, 1, 0], ![22, 0, 1]] where
  M :=![![![-1, -5, -2], ![-10, -76, -23], ![-28, -161, -66]]]
  hmulB := by decide  
  f := ![![![-1313, 8, 37]], ![![-993, 6, 28]], ![![-144, 1, 4]]]
  g := ![![![4, -5, -2], ![60, -76, -23], ![129, -161, -66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![1581, 10551, 3677]] ![![829, -5529, 2241]]
  ![![-111, 882, -304]] where
 M := ![![![-111, 882, -304]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![-111, 882, -304]] ![![-1, -5, -2]]
  ![![197, 0, 0]] where
 M := ![![![-197, -17533, 0]]]
 hmul := by decide  
 g := ![![![![-1, -89, 0]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0]] 
 ![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [48, 58, 157, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 96, 129], [198, 102, 70], [0, 1]]
 g := ![![[53, 173, 81], [70, 133, 123], [160, 71, 86], [162, 13], [101, 90], [163, 172], [1]], ![[194, 121, 30, 141], [182, 68, 10, 101], [63, 37, 27, 19], [188, 169], [4, 47], [36, 196], [139, 139, 99, 76]], ![[125, 68, 140, 57], [90, 111, 163, 46], [143, 96, 170, 172], [11, 63], [98, 14], [103, 187], [153, 193, 126, 123]]]
 h' := ![![[43, 96, 129], [23, 97, 9], [81, 50, 83], [20, 85, 177], [45, 57, 49], [52, 196, 182], [151, 141, 42], [0, 1]], ![[198, 102, 70], [34, 96, 98], [173, 5, 190], [135, 42, 164], [123, 71, 13], [64, 6, 68], [1, 179, 185], [43, 96, 129]], ![[0, 1], [13, 6, 92], [170, 144, 125], [54, 72, 57], [130, 71, 137], [156, 196, 148], [18, 78, 171], [198, 102, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [171, 46], []]
 b := ![[], [184, 126, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [48, 58, 157, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8756, -43979, -20895]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-44, -221, -105]
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

instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [194, 174, 130, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 43, 209], [27, 167, 2], [0, 1]]
 g := ![![[28, 189, 169], [125, 30, 121], [80, 47], [29, 81], [82, 202, 81], [18, 20], [1]], ![[148, 92, 0, 134], [44, 147, 90, 1], [0, 184], [132, 203], [118, 150, 76, 126], [179, 69], [157, 88, 79, 203]], ![[128, 65, 199, 195], [160, 13, 207, 94], [89, 173], [34, 101], [148, 191, 128, 33], [71, 56], [3, 12, 120, 8]]]
 h' := ![![[54, 43, 209], [15, 130, 13], [103, 166, 200], [208, 1, 141], [128, 105, 202], [173, 154, 202], [17, 37, 81], [0, 1]], ![[27, 167, 2], [43, 65, 12], [51, 208, 152], [126, 42, 124], [186, 111, 186], [134, 108, 88], [195, 82, 160], [54, 43, 209]], ![[0, 1], [134, 16, 186], [118, 48, 70], [121, 168, 157], [133, 206, 34], [24, 160, 132], [111, 92, 181], [27, 167, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 168], []]
 b := ![[], [99, 175, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [194, 174, 130, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1424039, -1248065, 3615274]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6749, -5915, 17134]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀



lemma PB212I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 211 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 211 (by omega)

def PB212I4 : PrimesBelowBoundCertificateInterval O 193 211 212 where
  m := 3
  g := ![3, 1, 1]
  P := ![197, 199, 211]
  hP := PB212I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0]
    · exact ![I211N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![197, 197, 197]
    · exact ![7880599]
    · exact ![9393931]
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
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
  β := ![I197N0, I197N1, I197N2]
  Il := ![[I197N0, I197N1, I197N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
