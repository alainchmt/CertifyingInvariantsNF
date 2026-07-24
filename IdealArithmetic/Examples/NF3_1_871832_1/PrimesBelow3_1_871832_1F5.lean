
import IdealArithmetic.Examples.NF3_1_871832_1.RI3_1_871832_1
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


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [117, 158, 251, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 54, 16], [8, 208, 247], [0, 1]]
 g := ![![[227, 15, 46], [136, 125, 234], [87, 164, 93], [231, 98], [39, 44], [67, 196], [12, 1], []], ![[134, 188, 238, 153], [110, 166, 199, 204], [63, 238, 170, 157], [44, 172], [161, 33], [114, 156], [82, 132], [66, 256]], ![[64, 156, 34, 42], [246, 35, 244, 134], [104, 57, 68, 201], [248, 144], [5, 37], [216, 92], [145, 23], [98, 256]]]
 h' := ![![[4, 54, 16], [131, 216, 154], [78, 33, 51], [155, 107, 57], [57, 101, 244], [82, 254, 71], [174, 91, 249], [0, 0, 1], [0, 1]], ![[8, 208, 247], [138, 196, 246], [126, 54, 90], [25, 10, 155], [121, 188, 31], [223, 187, 159], [66, 51, 122], [184, 28, 208], [4, 54, 16]], ![[0, 1], [161, 114, 126], [70, 176, 122], [181, 146, 51], [2, 237, 251], [245, 85, 33], [100, 121, 155], [170, 235, 54], [8, 208, 247]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [168, 112], []]
 b := ![[], [149, 146, 256], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [117, 158, 251, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11478635, -2125040, -346108]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43645, -8080, -1316]
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



lemma PB265I5_primes (p : ℕ) :
  p ∈ Set.range ![263] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 264 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 264 (by omega)

def PB265I5 : PrimesBelowBoundCertificateInterval O 257 264 265 where
  m := 1
  g := ![1]
  P := ![263]
  hP := PB265I5_primes
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
