
import IdealArithmetic.Examples.NF3_1_916300_1.RI3_1_916300_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-98, 86, 1]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-98, 86, 1]] 
 ![![263, 0, 0], ![0, 263, 0], ![165, 86, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-98, 86, 1], ![153, -145, 87], ![13311, -3936, -58]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-165, -86, 263]], ![![-1, 0, 1], ![-54, -29, 87], ![87, 4, -58]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [50, 142, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [121, 262], [0, 1]]
 g := ![![[87, 121], [168, 16], [85, 221], [218], [13], [81], [176], [1]], ![[0, 142], [0, 247], [0, 42], [218], [13], [81], [176], [1]]]
 h' := ![![[121, 262], [16, 252], [221, 259], [32, 241], [82, 179], [39, 117], [12, 254], [213, 121], [0, 1]], ![[0, 1], [0, 11], [0, 4], [0, 22], [175, 84], [257, 146], [238, 9], [126, 142], [121, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [247, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [50, 142, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![509, -130, -185]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![118, 60, -185]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-87, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-87, 1, 0]] 
 ![![263, 0, 0], ![176, 1, 0], ![58, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-87, 1, 0], ![0, -87, 1], ![153, -47, -86]]]
  hmulB := by decide  
  f := ![![![14791, -170, 0], ![44710, 0, 0]], ![![10006, -115, 0], ![30246, 0, 0]], ![![3248, -37, 0], ![9818, 1, 0]]]
  g := ![![![1, 0, 0], ![-176, 263, 0], ![-58, 0, 263]], ![![-1, 1, 0], ![58, -87, 1], ![51, -47, -86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![-98, 86, 1]] ![![263, 0, 0], ![-87, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![-22881, 263, 0]], ![![-25774, 22618, 263], ![8679, -7627, 0]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![-87, 1, 0]]], ![![![-98, 86, 1]], ![![33, -29, 0]]]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![77, -6, 1]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0], ![77, -6, 1]] 
 ![![269, 0, 0], ![0, 269, 0], ![77, 263, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![77, -6, 1], ![153, 30, -5], ![-765, 388, 25]]]
  hmulB := by decide  
  f := ![![![-76, 6, -1], ![269, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-77, -263, 269]], ![![0, -1, 1], ![2, 5, -5], ![-10, -23, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 2 2 8 [154, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [170, 268], [0, 1]]
 g := ![![[212, 138], [204], [10, 245], [212, 84], [87], [54], [117], [1]], ![[0, 131], [204], [234, 24], [235, 185], [87], [54], [117], [1]]]
 h' := ![![[170, 268], [153, 26], [74, 133], [170, 194], [61, 114], [3, 244], [49, 79], [115, 170], [0, 1]], ![[0, 1], [0, 243], [88, 136], [63, 75], [73, 155], [57, 25], [29, 190], [232, 99], [170, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [262]]
 b := ![[], [163, 131]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 2
  hpos := by decide
  P := [154, 99, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-403, 1324, -131]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![36, 133, -131]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![5, 1, 0]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![269, 0, 0], ![5, 1, 0]] 
 ![![269, 0, 0], ![5, 1, 0], ![244, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![5, 1, 0], ![0, 5, 1], ![153, -47, 6]]]
  hmulB := by decide  
  f := ![![![261, 52, 0], ![-13988, 0, 0]], ![![-5, -1, 0], ![270, 0, 0]], ![![236, 47, 0], ![-12648, 1, 0]]]
  g := ![![![1, 0, 0], ![-5, 269, 0], ![-244, 0, 269]], ![![0, 1, 0], ![-1, 5, 1], ![-4, -47, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![269, 0, 0], ![77, -6, 1]] ![![269, 0, 0], ![5, 1, 0]]
  ![![269, 0, 0]] where
 M := ![![![72361, 0, 0], ![1345, 269, 0]], ![![20713, -1614, 269], ![538, 0, 0]]]
 hmul := by decide  
 g := ![![![![269, 0, 0]], ![![5, 1, 0]]], ![![![77, -6, 1]], ![![2, 0, 0]]]]
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
