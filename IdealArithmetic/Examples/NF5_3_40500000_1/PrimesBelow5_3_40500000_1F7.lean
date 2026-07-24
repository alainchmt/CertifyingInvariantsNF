
import IdealArithmetic.Examples.NF5_3_40500000_1.RI5_3_40500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![557, 100, -208, -32, 292]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![557, 100, -208, -32, 292]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![0, 0, 311, 0, 0], ![0, 0, 0, 311, 0], ![118, 273, 191, 149, 1]] where
  M :=![![![557, 100, -208, -32, 292], ![-1012, 289, -4, -192, 508], ![148, -2620, 2153, 1336, -5660], ![5304, 5524, -5668, -2427, 12000], ![672, -364, 160, 216, -727]]]
  hmulB := by decide  
  f := ![![![3, 4, 0, 0, 4]], ![![-20, 7, -4, 0, 28]], ![![-140, 4, -49, -8, 196]], ![![-424, -44, -132, -21, 480]], ![![-306, -11, -97, -15, 377]]]
  g := ![![![-109, -256, -180, -140, 292], ![-196, -445, -312, -244, 508], ![2148, 4960, 3483, 2716, -5660], ![-4536, -10516, -7388, -5757, 12000], ![278, 637, 447, 349, -727]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 4 2 8 [78, 7, 248, 298, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [182, 219, 159, 129], [247, 36, 74, 115], [206, 55, 78, 67], [0, 1]]
 g := ![![[205, 134, 19, 96], [253, 141, 231, 146], [63, 222, 208, 112], [28, 91, 265], [262, 27, 3, 104], [8, 223, 103, 169], [1], []], ![[174, 145, 82, 91, 252, 68], [112, 19, 217, 237, 116, 171], [37, 245, 247, 38, 17, 247], [45, 234, 6], [11, 59, 192, 270, 223, 95], [98, 151, 142, 10, 260, 264], [87, 246, 292], [180, 158, 158]], ![[270, 184, 264, 10, 111, 167], [243, 69, 190, 72, 174, 131], [42, 194, 291, 148, 144, 207], [120, 274, 265], [2, 235, 283, 204, 48, 68], [254, 309, 202, 39, 179, 211], [197, 228, 280], [85, 168, 163]], ![[293, 26, 258, 136, 195, 209], [197, 310, 89, 307, 287, 128], [276, 198, 94, 230, 43, 188], [62, 258, 32], [302, 9, 216, 168, 139, 45], [77, 50, 255, 85, 287, 32], [197, 129, 201], [270, 78, 135]]]
 h' := ![![[182, 219, 159, 129], [170, 94, 223, 242], [62, 19, 81, 222], [7, 148, 10, 62], [90, 107, 280, 24], [309, 141, 87, 112], [233, 304, 63, 13], [0, 0, 1], [0, 1]], ![[247, 36, 74, 115], [135, 267, 297, 164], [70, 132, 169, 118], [228, 58, 16, 225], [216, 303, 9, 216], [8, 165, 207, 63], [74, 212, 56, 37], [113, 200, 184, 276], [182, 219, 159, 129]], ![[206, 55, 78, 67], [88, 215, 84, 88], [248, 254, 154, 139], [302, 10, 306, 303], [232, 68, 70, 24], [290, 50, 295, 95], [123, 298, 208, 177], [265, 42, 83, 223], [247, 36, 74, 115]], ![[0, 1], [149, 46, 18, 128], [112, 217, 218, 143], [204, 95, 290, 32], [8, 144, 263, 47], [285, 266, 33, 41], [231, 119, 295, 84], [228, 69, 43, 123], [206, 55, 78, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [114, 3, 236], []]
 b := ![[], [], [309, 258, 125, 217], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 4
  hpos := by decide
  P := [78, 7, 248, 298, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-203650712760, -42271504416, -72520857652, -13491952642, 221831078376]
  a := ![77, -62, 79, 36, -264]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-84822244248, -194862237624, -136470279188, -106322580806, 221831078376]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 9354951841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -4, 0, 0, -4]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![-3, -4, 0, 0, -4]] 
 ![![311, 0, 0, 0, 0], ![305, 1, 0, 0, 0], ![275, 0, 1, 0, 0], ![206, 0, 0, 1, 0], ![240, 0, 0, 0, 1]] where
  M :=![![![-3, -4, 0, 0, -4], ![20, -7, 4, 0, -28], ![140, -4, 49, 8, -196], ![424, 44, 132, 21, -480], ![144, 12, 48, 8, -175]]]
  hmulB := by decide  
  f := ![![![-557, -100, 208, 32, -292]], ![![-543, -99, 204, 32, -288]], ![![-493, -80, 177, 24, -240]], ![![-386, -84, 156, 29, -232]], ![![-432, -76, 160, 24, -223]]]
  g := ![![![7, -4, 0, 0, -4], ![25, -7, 4, 0, -28], ![107, -4, 49, 8, -196], ![198, 44, 132, 21, -480], ![76, 12, 48, 8, -175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N1 : Nat.card (O ⧸ I311N1) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N1)

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := prime_ideal_of_norm_prime hp311.out _ NI311N1
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![557, 100, -208, -32, 292]] ![![-3, -4, 0, 0, -4]]
  ![![311, 0, 0, 0, 0]] where
 M := ![![![-311, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC311 : ContainsPrimesAboveP 311 ![I311N0, I311N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI311N0
    exact isPrimeI311N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 311 (by decide) (𝕀 ⊙ MulI311N0)


lemma PB312I7_primes (p : ℕ) :
  p ∈ Set.range ![311] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 311 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 311 (by omega)

def PB312I7 : PrimesBelowBoundCertificateInterval O 307 311 312 where
  m := 1
  g := ![2]
  P := ![311]
  hP := PB312I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC311
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![9354951841, 311]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI311N0
      exact NI311N1
  β := ![I311N1]
  Il := ![[I311N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
