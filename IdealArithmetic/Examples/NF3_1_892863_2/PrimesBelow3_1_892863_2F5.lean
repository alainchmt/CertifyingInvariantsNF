
import IdealArithmetic.Examples.NF3_1_892863_2.RI3_1_892863_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0]] 
 ![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [236, 80, 211, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 105, 175], [257, 157, 88], [0, 1]]
 g := ![![[158, 145, 66], [134, 226, 68], [156, 237, 258], [52, 156], [5, 43], [183, 36], [52, 1], []], ![[118, 104, 68, 195], [133, 73, 88, 230], [183, 212, 168, 257], [244, 144], [35, 103], [223, 124], [4, 190], [228, 117]], ![[136, 186, 6, 233], [39, 131, 190, 206], [199, 195, 226, 244], [21, 72], [259, 102], [222, 192], [62, 242], [52, 117]]]
 h' := ![![[58, 105, 175], [199, 132, 132], [4, 124, 133], [141, 239, 28], [234, 92, 122], [238, 208, 147], [89, 75, 257], [0, 0, 1], [0, 1]], ![[257, 157, 88], [254, 180, 166], [173, 121, 238], [205, 149, 196], [79, 5, 12], [221, 150, 41], [182, 33, 85], [52, 255, 157], [58, 105, 175]], ![[0, 1], [127, 214, 228], [105, 18, 155], [103, 138, 39], [204, 166, 129], [7, 168, 75], [204, 155, 184], [125, 8, 105], [257, 157, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 67], []]
 b := ![[], [217, 94, 201], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [236, 80, 211, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-983620, 547566, -356102]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3740, 2082, -1354]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def PBC263 : ContainsPrimesAboveP 263 ![I263N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![263, 0, 0]]) timesTableT_eq_Table B_one_repr 263 (by decide) 𝕀



lemma PB268I5_primes (p : ℕ) :
  p ∈ Set.range ![263] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 267 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 267 (by omega)

def PB268I5 : PrimesBelowBoundCertificateInterval O 257 267 268 where
  m := 1
  g := ![1]
  P := ![263]
  hP := PB268I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC263
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![18191447]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
  β := ![]
  Il := ![[]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
