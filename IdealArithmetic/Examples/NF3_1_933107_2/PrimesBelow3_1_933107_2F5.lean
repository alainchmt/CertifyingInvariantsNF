
import IdealArithmetic.Examples.NF3_1_933107_2.RI3_1_933107_2
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


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [187, 18, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 104, 125], [132, 158, 138], [0, 1]]
 g := ![![[108, 19, 235], [26, 123, 48], [182, 183, 248], [24, 234], [229, 208], [257, 258], [187, 1], []], ![[261, 117, 74, 167], [56, 247, 199, 236], [33, 247, 182, 134], [164, 124], [22, 74], [176, 72], [71, 242], [171, 108]], ![[108, 196, 162, 13], [144, 174, 157, 162], [253, 55, 97, 121], [260, 104], [153, 36], [16, 207], [177, 33], [158, 108]]]
 h' := ![![[55, 104, 125], [135, 78, 32], [156, 162, 92], [239, 23, 145], [16, 42, 212], [170, 204, 58], [10, 129, 235], [0, 0, 1], [0, 1]], ![[132, 158, 138], [39, 254, 78], [204, 108, 70], [155, 170, 11], [29, 109, 85], [120, 234, 211], [94, 238, 129], [241, 1, 158], [55, 104, 125]], ![[0, 1], [195, 194, 153], [133, 256, 101], [58, 70, 107], [209, 112, 229], [195, 88, 257], [89, 159, 162], [239, 262, 104], [132, 158, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 239], []]
 b := ![[], [232, 222, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [187, 18, 76, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54967, 2367, 2367]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-209, 9, 9]
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


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [43, 116, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 73, 12], [188, 195, 257], [0, 1]]
 g := ![![[262, 24, 196], [218, 125], [137, 77, 268], [143, 47, 73], [16, 78], [250, 204], [220, 1], []], ![[240, 184, 45, 113], [260, 5], [225, 245, 55, 129], [268, 49, 168, 82], [254, 55], [257, 225], [63, 96], [76, 144]], ![[6, 249, 177, 229], [100, 180], [75, 216, 23, 262], [4, 237, 93, 112], [61, 213], [214, 115], [44, 218], [100, 144]]]
 h' := ![![[32, 73, 12], [232, 2, 255], [27, 264, 92], [38, 72, 187], [89, 199, 197], [152, 70, 62], [224, 261, 133], [0, 0, 1], [0, 1]], ![[188, 195, 257], [239, 128, 253], [11, 176, 126], [202, 78, 207], [169, 139, 184], [185, 194, 18], [106, 125, 15], [177, 155, 195], [32, 73, 12]], ![[0, 1], [158, 139, 30], [238, 98, 51], [63, 119, 144], [63, 200, 157], [164, 5, 189], [36, 152, 121], [109, 114, 73], [188, 195, 257]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [180, 47], []]
 b := ![[], [86, 108, 153], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [43, 116, 49, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1312989, -532889, 52724]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4881, -1981, 196]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0]] 
 ![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 3 2 8 [57, 147, 266, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 29, 58], [0, 241, 213], [0, 1]]
 g := ![![[95, 29, 126], [83, 158, 69], [54, 153, 50], [169, 250, 31], [240, 245], [191, 250], [5, 1], []], ![[55, 184, 206, 260], [59, 75, 97, 65], [196, 98, 24, 115], [39, 124, 185, 48], [220, 162], [], [224, 87], [130, 112]], ![[0, 173, 244, 126], [148, 179, 14, 89], [60, 252, 133, 8], [93, 137, 118, 2], [194, 121], [145, 250], [198, 28], [246, 112]]]
 h' := ![![[5, 29, 58], [147, 126, 160], [174, 96, 119], [123, 239, 209], [120, 168, 64], [149, 174, 40], [257, 21, 149], [0, 0, 1], [0, 1]], ![[0, 241, 213], [195, 242, 69], [150, 226, 101], [114, 218, 4], [131, 201, 236], [196, 128, 220], [257, 189], [203, 270, 241], [5, 29, 58]], ![[0, 1], [236, 174, 42], [103, 220, 51], [119, 85, 58], [264, 173, 242], [239, 240, 11], [118, 61, 122], [70, 1, 29], [0, 241, 213]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [268, 81], []]
 b := ![[], [197, 67, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 3
  hpos := by decide
  P := [57, 147, 266, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![778583, -22764, 22764]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2873, -84, 84]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 19902511 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def PBC271 : ContainsPrimesAboveP 271 ![I271N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![271, 0, 0]]) timesTableT_eq_Table B_one_repr 271 (by decide) 𝕀



lemma PB274I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269, 271] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 273 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 273 (by omega)

def PB274I5 : PrimesBelowBoundCertificateInterval O 257 273 274 where
  m := 3
  g := ![1, 1, 1]
  P := ![263, 269, 271]
  hP := PB274I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0]
    · exact ![I269N0]
    · exact ![I271N0]
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
    · exact ![18191447]
    · exact ![19465109]
    · exact ![19902511]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
  β := ![]
  Il := ![[], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
