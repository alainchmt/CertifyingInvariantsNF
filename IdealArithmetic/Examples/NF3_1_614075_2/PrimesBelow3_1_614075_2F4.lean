
import IdealArithmetic.Examples.NF3_1_614075_2.RI3_1_614075_2
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [99, 33, 125, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 186, 100], [176, 10, 97], [0, 1]]
 g := ![![[11, 158, 163], [107, 92], [4, 61, 101], [36, 7], [50, 160], [106, 62], [1]], ![[50, 100, 82, 15], [26, 88], [72, 41, 82, 135], [183, 23], [174, 83], [129, 164], [51, 135, 21, 28]], ![[100, 144, 12, 19], [192, 26], [81, 26, 25, 54], [18, 59], [128, 28], [71, 51], [165, 58, 120, 169]]]
 h' := ![![[93, 186, 100], [49, 52, 44], [195, 127, 17], [83, 136, 135], [135, 87, 106], [95, 50, 102], [98, 164, 72], [0, 1]], ![[176, 10, 97], [29, 112, 124], [47, 103, 65], [178, 137, 175], [163, 64, 107], [168, 176, 110], [79, 157, 178], [93, 186, 100]], ![[0, 1], [91, 33, 29], [160, 164, 115], [178, 121, 84], [37, 46, 181], [62, 168, 182], [14, 73, 144], [176, 10, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 110], []]
 b := ![[], [95, 121, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [99, 33, 125, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-74269, -41961, -4531]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-377, -213, -23]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![104, -48, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![104, -48, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![104, 151, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![104, -48, 1], ![-112, 67, -47], ![5264, 1627, 20]]]
  hmulB := by decide  
  f := ![![![-103, 48, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-104, -151, 199]], ![![0, -1, 1], ![24, 36, -47], ![16, -7, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [126, 178, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 198], [0, 1]]
 g := ![![[33, 169], [168, 56], [121, 51], [46], [128], [123], [21, 1]], ![[0, 30], [150, 143], [197, 148], [46], [128], [123], [42, 198]]]
 h' := ![![[21, 198], [125, 13], [77, 102], [87, 38], [149, 65], [122, 39], [140, 116], [0, 1]], ![[0, 1], [0, 186], [30, 97], [89, 161], [121, 134], [145, 160], [188, 83], [21, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [158]]
 b := ![[], [66, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [126, 178, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![285, -1249, 196]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-101, -155, 196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![47, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![47, 1, 0]] 
 ![![199, 0, 0], ![47, 1, 0], ![179, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![47, 1, 0], ![0, 47, 1], ![-112, -37, 48]]]
  hmulB := by decide  
  f := ![![![2821, 60, 0], ![-11940, 0, 0]], ![![611, 13, 0], ![-2586, 0, 0]], ![![2503, 53, 0], ![-10594, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 199, 0], ![-179, 0, 199]], ![![0, 1, 0], ![-12, 47, 1], ![-35, -37, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![104, -48, 1]] ![![199, 0, 0], ![47, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![9353, 199, 0]], ![![20696, -9552, 199], ![4776, -2189, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![47, 1, 0]]], ![![![104, -48, 1]], ![![24, -11, 0]]]]
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
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![107, 65, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![107, 65, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![107, 65, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![107, 65, 1], ![-112, 70, 66], ![-7392, -2554, 136]]]
  hmulB := by decide  
  f := ![![![-106, -65, -1], ![211, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-107, -65, 211]], ![![0, 0, 1], ![-34, -20, 66], ![-104, -54, 136]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [98, 195, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 210], [0, 1]]
 g := ![![[185, 59], [157, 136], [185], [204], [12, 105], [66], [16, 1]], ![[74, 152], [12, 75], [185], [204], [4, 106], [66], [32, 210]]]
 h' := ![![[16, 210], [17, 108], [95, 66], [135, 94], [90, 41], [125, 152], [120, 158], [0, 1]], ![[0, 1], [57, 103], [96, 145], [162, 117], [113, 170], [25, 59], [116, 53], [16, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [180]]
 b := ![[], [124, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [98, 195, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8174, -8, -104]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14, 32, -104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-66, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-66, 1, 0]] 
 ![![211, 0, 0], ![145, 1, 0], ![75, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-66, 1, 0], ![0, -66, 1], ![-112, -37, -65]]]
  hmulB := by decide  
  f := ![![![1717, -26, 0], ![5486, 0, 0]], ![![1123, -17, 0], ![3588, 0, 0]], ![![681, -10, 0], ![2176, 1, 0]]]
  g := ![![![1, 0, 0], ![-145, 211, 0], ![-75, 0, 211]], ![![-1, 1, 0], ![45, -66, 1], ![48, -37, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![107, 65, 1]] ![![211, 0, 0], ![-66, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-13926, 211, 0]], ![![22577, 13715, 211], ![-7174, -4220, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-66, 1, 0]]], ![![![107, 65, 1]], ![![-34, -20, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)


lemma PB222I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 221 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 221 (by omega)

def PB222I4 : PrimesBelowBoundCertificateInterval O 193 221 222 where
  m := 3
  g := ![1, 2, 2]
  P := ![197, 199, 211]
  hP := PB222I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
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
    · exact ![7645373]
    · exact ![39601, 199]
    · exact ![44521, 211]
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
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
  β := ![I199N1, I211N1]
  Il := ![[], [I199N1], [I211N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
