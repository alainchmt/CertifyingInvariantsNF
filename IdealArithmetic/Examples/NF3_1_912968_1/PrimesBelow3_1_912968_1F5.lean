
import IdealArithmetic.Examples.NF3_1_912968_1.RI3_1_912968_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![51, -108, 1]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![51, -108, 1]] 
 ![![263, 0, 0], ![0, 263, 0], ![51, 155, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![51, -108, 1], ![81, 76, -215], ![-20305, -2593, -32]]]
  hmulB := by decide  
  f := ![![![-50, 108, -1], ![263, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -155, 263]], ![![0, -1, 1], ![42, 127, -215], ![-71, 9, -32]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [32, 119, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 262], [0, 1]]
 g := ![![[127, 74], [234, 78], [19, 140], [207], [95], [72], [222], [1]], ![[0, 189], [157, 185], [191, 123], [207], [95], [72], [222], [1]]]
 h' := ![![[144, 262], [139, 52], [181, 128], [174, 156], [111, 101], [235, 219], [232, 134], [231, 144], [0, 1]], ![[0, 1], [0, 211], [203, 135], [20, 107], [190, 162], [211, 44], [66, 129], [190, 119], [144, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [207]]
 b := ![[], [175, 235]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [32, 119, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1099, 411, -128]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, 77, -128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-48, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-48, 1, 0]] 
 ![![263, 0, 0], ![215, 1, 0], ![32, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-48, 1, 0], ![1, -48, 2], ![189, 25, -47]]]
  hmulB := by decide  
  f := ![![![-7661, 393109, -16380], ![2893, 2153970, 0]], ![![-6262, 321351, -13390], ![2368, 1760785, 0]], ![![-896, 47830, -1993], ![550, 262080, 0]]]
  g := ![![![1, 0, 0], ![-215, 263, 0], ![-32, 0, 263]], ![![-1, 1, 0], ![39, -48, 2], ![-14, 25, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![51, -108, 1]] ![![263, 0, 0], ![-48, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![-12624, 263, 0]], ![![13413, -28404, 263], ![-2367, 5260, -263]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![-48, 1, 0]]], ![![![51, -108, 1]], ![![-9, 20, -1]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![-57, 54, 1]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0], ![-57, 54, 1]] 
 ![![269, 0, 0], ![0, 269, 0], ![212, 54, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![-57, 54, 1], ![243, -32, 109], ![10313, 1457, 22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-212, -54, 269]], ![![-1, 0, 1], ![-85, -22, 109], ![21, 1, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 2 2 8 [10, 178, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 268], [0, 1]]
 g := ![![[233, 5], [214], [115, 43], [151, 64], [176], [56], [211], [1]], ![[150, 264], [214], [262, 226], [57, 205], [176], [56], [211], [1]]]
 h' := ![![[91, 268], [108, 126], [195, 138], [104, 124], [136, 261], [236, 39], [142, 165], [259, 91], [0, 1]], ![[0, 1], [7, 143], [110, 131], [90, 145], [215, 8], [19, 230], [93, 104], [201, 178], [91, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [172, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 2
  hpos := by decide
  P := [10, 178, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-731, 1811, 1523]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1203, -299, 1523]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![-109, 1, 0]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![269, 0, 0], ![-109, 1, 0]] 
 ![![269, 0, 0], ![160, 1, 0], ![247, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![-109, 1, 0], ![1, -109, 2], ![189, 25, -108]]]
  hmulB := by decide  
  f := ![![![-20982, 3201907, -58752], ![20713, 7902144, 0]], ![![-12457, 1904402, -34944], ![12375, 4699968, 0]], ![![-19266, 2940041, -53947], ![19019, 7255872, 0]]]
  g := ![![![1, 0, 0], ![-160, 269, 0], ![-247, 0, 269]], ![![-1, 1, 0], ![63, -109, 2], ![85, 25, -108]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![269, 0, 0], ![-57, 54, 1]] ![![269, 0, 0], ![-109, 1, 0]]
  ![![269, 0, 0]] where
 M := ![![![72361, 0, 0], ![-29321, 269, 0]], ![![-15333, 14526, 269], ![6456, -5918, 0]]]
 hmul := by decide  
 g := ![![![![269, 0, 0]], ![![-109, 1, 0]]], ![![![-57, 54, 1]], ![![24, -22, 0]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0)


lemma PB271I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 270 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 270 (by omega)

def PB271I5 : PrimesBelowBoundCertificateInterval O 257 270 271 where
  m := 2
  g := ![2, 2]
  P := ![263, 269]
  hP := PB271I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC263
    · exact PBC269
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![69169, 263]
    · exact ![72361, 269]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
  β := ![I263N1, I269N1]
  Il := ![[I263N1], [I269N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
