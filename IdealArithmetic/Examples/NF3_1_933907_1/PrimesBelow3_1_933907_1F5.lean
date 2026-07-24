
import IdealArithmetic.Examples.NF3_1_933907_1.RI3_1_933907_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![11, 1, 0]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![11, 1, 0]] 
 ![![263, 0, 0], ![11, 1, 0], ![197, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![11, 1, 0], ![0, 12, 2], ![-754, 117, 11]]]
  hmulB := by decide  
  f := ![![![243, 22, 0], ![-5786, 0, 0]], ![![-11, -1, 0], ![264, 0, 0]], ![![177, 10, -1], ![-4214, 132, 0]]]
  g := ![![![1, 0, 0], ![-11, 263, 0], ![-197, 0, 263]], ![![0, 1, 0], ![-2, 12, 2], ![-16, 117, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N0 : Nat.card (O ⧸ I263N0) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N0)

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := prime_ideal_of_norm_prime hp263.out _ NI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![117, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![117, 1, 0]] 
 ![![263, 0, 0], ![117, 1, 0], ![198, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![117, 1, 0], ![0, 118, 2], ![-754, 117, 117]]]
  hmulB := by decide  
  f := ![![![352, 3, 0], ![-789, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![144, -58, -1], ![-322, 132, 0]]]
  g := ![![![1, 0, 0], ![-117, 263, 0], ![-198, 0, 263]], ![![0, 1, 0], ![-54, 118, 2], ![-143, 117, 117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-129, 1, 0]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-129, 1, 0]] 
 ![![263, 0, 0], ![134, 1, 0], ![160, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-129, 1, 0], ![0, -128, 2], ![-754, 117, -129]]]
  hmulB := by decide  
  f := ![![![30187, -234, 0], ![61542, 0, 0]], ![![15610, -121, 0], ![31824, 0, 0]], ![![18350, -78, -1], ![37410, 132, 0]]]
  g := ![![![1, 0, 0], ![-134, 263, 0], ![-160, 0, 263]], ![![-1, 1, 0], ![64, -128, 2], ![16, 117, -129]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![11, 1, 0]] ![![263, 0, 0], ![117, 1, 0]]
  ![![263, 0, 0], ![-14, -67, 1]] where
 M := ![![![69169, 0, 0], ![30771, 263, 0]], ![![2893, 263, 0], ![1287, 129, 2]]]
 hmul := by decide  
 g := ![![![![263, 0, 0], ![0, 0, 0]], ![![117, 1, 0], ![0, 0, 0]]], ![![![11, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![-14, -67, 1]] ![![263, 0, 0], ![-129, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![-33927, 263, 0]], ![![-3682, -17621, 263], ![1052, 8679, -263]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![-129, 1, 0]]], ![![![-14, -67, 1]], ![![4, 33, -1]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1, I263N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
    exact isPrimeI263N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0 ⊙ MulI263N1)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0]] 
 ![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [117, 260, 166, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 96, 103], [233, 172, 166], [0, 1]]
 g := ![![[31, 221, 205], [113, 204], [170, 116, 24], [262, 216, 23], [183, 97], [167, 258], [103, 1], []], ![[179, 239, 58, 96], [146, 253], [178, 49, 7, 152], [177, 195, 99, 212], [195, 54], [219, 148], [23, 263], [188, 118]], ![[233, 72, 203, 125], [259, 96], [20, 63, 39, 138], [104, 51, 213, 92], [3, 34], [252, 57], [146, 70], [125, 118]]]
 h' := ![![[139, 96, 103], [216, 182, 151], [16, 207, 136], [12, 179, 37], [175, 85, 125], [55, 155, 161], [54, 3, 127], [0, 0, 1], [0, 1]], ![[233, 172, 166], [72, 241, 64], [163, 38, 59], [162, 130, 53], [146, 172, 127], [74, 12, 79], [224, 197, 95], [15, 48, 172], [139, 96, 103]], ![[0, 1], [99, 115, 54], [143, 24, 74], [197, 229, 179], [135, 12, 17], [237, 102, 29], [249, 69, 47], [121, 221, 96], [233, 172, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 22], []]
 b := ![[], [176, 65, 227], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [117, 260, 166, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5028686, 1333702, -172160]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18694, 4958, -640]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def PBC269 : ContainsPrimesAboveP 269 ![I269N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![269, 0, 0]]) timesTableT_eq_Table B_one_repr 269 (by decide) 𝕀

instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![-177, 45, 1]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0], ![-177, 45, 1]] 
 ![![271, 0, 0], ![0, 271, 0], ![94, 45, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![-177, 45, 1], ![-754, -15, 90], ![-33553, 4888, -60]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-94, -45, 271]], ![![-1, 0, 1], ![-34, -15, 90], ![-103, 28, -60]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [231, 270, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 270], [0, 1]]
 g := ![![[61, 72], [26, 250], [215, 138], [214, 41], [259], [57], [1], [1]], ![[133, 199], [5, 21], [82, 133], [255, 230], [259], [57], [1], [1]]]
 h' := ![![[1, 270], [227, 34], [199, 122], [159, 42], [76, 224], [37, 157], [14, 81], [40, 1], [0, 1]], ![[0, 1], [261, 237], [50, 149], [201, 229], [29, 47], [194, 114], [95, 190], [41, 270], [1, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [138]]
 b := ![[], [101, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [231, 270, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38, -4827, 2946]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1022, -507, 2946]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![-90, 1, 0]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![271, 0, 0], ![-90, 1, 0]] 
 ![![271, 0, 0], ![181, 1, 0], ![60, 0, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![-90, 1, 0], ![0, -89, 2], ![-754, 117, -90]]]
  hmulB := by decide  
  f := ![![![91, 17888, -402], ![271, 54471, 0]], ![![91, 11925, -268], ![272, 36314, 0]], ![![60, 3960, -89], ![180, 12060, 0]]]
  g := ![![![1, 0, 0], ![-181, 271, 0], ![-60, 0, 271]], ![![-1, 1, 0], ![59, -89, 2], ![-61, 117, -90]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![271, 0, 0], ![-177, 45, 1]] ![![271, 0, 0], ![-90, 1, 0]]
  ![![271, 0, 0]] where
 M := ![![![73441, 0, 0], ![-24390, 271, 0]], ![![-47967, 12195, 271], ![15176, -4065, 0]]]
 hmul := by decide  
 g := ![![![![271, 0, 0]], ![![-90, 1, 0]]], ![![![-177, 45, 1]], ![![56, -15, 0]]]]
 hle2 := by decide  


def PBC271 : ContainsPrimesAboveP 271 ![I271N0, I271N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 271 (by decide) (𝕀 ⊙ MulI271N0)


lemma PB274I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269, 271] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 273 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 273 (by omega)

def PB274I5 : PrimesBelowBoundCertificateInterval O 257 273 274 where
  m := 3
  g := ![3, 1, 2]
  P := ![263, 269, 271]
  hP := PB274I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1, I263N2]
    · exact ![I269N0]
    · exact ![I271N0, I271N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC263
    · exact PBC269
    · exact PBC271
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![263, 263, 263]
    · exact ![19465109]
    · exact ![73441, 271]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
      exact NI263N2
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
  β := ![I263N0, I263N1, I263N2, I271N1]
  Il := ![[I263N0, I263N1, I263N2], [], [I271N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
