
import IdealArithmetic.Examples.NF5_1_25312500_2.RI5_1_25312500_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7787, 4214, -204, 174, -1044]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![-7787, 4214, -204, 174, -1044]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![0, 0, 311, 0, 0], ![90, 58, 307, 1, 0], ![158, 123, 46, 0, 1]] where
  M :=![![![-7787, 4214, -204, 174, -1044], ![10410, -5631, 280, -234, 1392], ![-12142, 6574, -343, 280, -1626], ![11126, -6014, 312, -267, 1498], ![-3932, 2116, -92, 108, -547]]]
  hmulB := by decide  
  f := ![![![-13, 2, 36, 34, 16]], ![![-90, -49, 96, 106, 52]], ![![-114, -94, 63, 96, 54]], ![![-134, -102, 91, 125, 68]], ![![-60, -33, 66, 74, 37]]]
  g := ![![![455, 394, -18, 174, -1044], ![-606, -525, 26, -234, 1392], ![706, 612, -37, 280, -1626], ![-648, -562, 43, -267, 1498], ![234, 203, -26, 108, -547]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 3 2 8 [155, 203, 147, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 256, 3], [164, 54, 308], [0, 1]]
 g := ![![[0, 154, 256], [191, 278, 196], [12, 129, 168], [1, 94], [197, 271, 96], [243, 67, 10], [164, 1], []], ![[17, 128, 196, 157], [204, 232, 68, 91], [195, 167, 16, 128], [264, 81], [255, 132, 14, 260], [163, 287, 70, 50], [245, 117], [213, 9]], ![[249, 272, 111, 261], [52, 264, 294, 246], [149, 281, 298, 167], [263, 158], [157, 225, 107, 310], [170, 47, 120, 263], [72, 226], [219, 9]]]
 h' := ![![[0, 256, 3], [251, 277, 295], [6, 217, 14], [295, 52, 146], [254, 20, 120], [277, 191, 242], [82, 141, 258], [0, 0, 1], [0, 1]], ![[164, 54, 308], [102, 92, 278], [253, 117, 163], [294, 69, 265], [283, 106, 9], [237, 293, 268], [191, 156, 49], [262, 150, 54], [0, 256, 3]], ![[0, 1], [164, 253, 49], [41, 288, 134], [60, 190, 211], [153, 185, 182], [167, 138, 112], [278, 14, 4], [104, 161, 256], [164, 54, 308]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [309, 112], []]
 b := ![[], [225, 174, 170], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 3
  hpos := by decide
  P := [155, 203, 147, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9528943, 6244449, 5746760, -5575932, 1828938]
  a := ![-16, 11, 7, -17, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![653803, 336621, 5252176, -5575932, 1828938]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 30080231 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, -32, 1, -1, 8]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![59, -32, 1, -1, 8]] 
 ![![311, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![302, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![59, -32, 1, -1, 8], ![-80, 43, -1, 1, -10], ![90, -50, 4, -1, 11], ![-78, 42, -7, 4, -10], ![18, -10, 8, -6, 5]]]
  hmulB := by decide  
  f := ![![![619, 510, -187, -321, -201]], ![![176, 145, -53, -91, -57]], ![![604, 498, -182, -313, -196]], ![![235, 194, -70, -121, -76]], ![![39, 32, -11, -19, -12]]]
  g := ![![![8, -32, 1, -1, 8], ![-11, 43, -1, 1, -10], ![10, -50, 4, -1, 11], ![-6, 42, -7, 4, -10], ![-3, -10, 8, -6, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N1 : Nat.card (O ⧸ I311N1) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N1)

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := prime_ideal_of_norm_prime hp311.out _ NI311N1

def I311N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 6, -1, 1, -2]] i)))

def SI311N2: IdealEqSpanCertificate' Table ![![-11, 6, -1, 1, -2]] 
 ![![311, 0, 0, 0, 0], ![233, 1, 0, 0, 0], ![107, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![257, 0, 0, 0, 1]] where
  M :=![![![-11, 6, -1, 1, -2], ![20, -9, -3, -1, 4], ![-32, 16, 10, -3, -5], ![28, -16, -5, 6, 0], ![2, 6, -12, -6, 9]]]
  hmulB := by decide  
  f := ![![![-267, -156, 243, 285, 145]], ![![-203, -119, 184, 216, 110]], ![![-95, -56, 85, 100, 51]], ![![-131, -78, 116, 137, 70]], ![![-227, -134, 203, 239, 122]]]
  g := ![![![-3, 6, -1, 1, -2], ![5, -9, -3, -1, 4], ![-10, 16, 10, -3, -5], ![11, -16, -5, 6, 0], ![-5, 6, -12, -6, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N2 : Nat.card (O ⧸ I311N2) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N2)

lemma isPrimeI311N2 : Ideal.IsPrime I311N2 := prime_ideal_of_norm_prime hp311.out _ NI311N2
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![-7787, 4214, -204, 174, -1044]] ![![59, -32, 1, -1, 8]]
  ![![-847277, 458334, -22387, 19165, -113640]] where
 M := ![![![-847277, 458334, -22387, 19165, -113640]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI311N1 : IdealMulLeCertificate' Table 
  ![![-847277, 458334, -22387, 19165, -113640]] ![![-11, 6, -1, 1, -2]]
  ![![311, 0, 0, 0, 0]] where
 M := ![![![19512451, -10555340, 516260, -441620, 2617065]]]
 hmul := by decide  
 g := ![![![![62741, -33940, 1660, -1420, 8415]]]]
 hle2 := by decide  


def PBC311 : ContainsPrimesAboveP 311 ![I311N0, I311N1, I311N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI311N0
    exact isPrimeI311N1
    exact isPrimeI311N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 311 (by decide) (𝕀 ⊙ MulI311N0 ⊙ MulI311N1)
instance hp313 : Fact (Nat.Prime 313) := {out := by norm_num}

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2889, -824, -2701, 221, 1083]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![2889, -824, -2701, 221, 1083]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![0, 0, 313, 0, 0], ![0, 0, 0, 313, 0], ![157, 116, 166, 95, 1]] where
  M :=![![![2889, -824, -2701, 221, 1083], ![-13310, 6711, 9717, -5181, -641], ![12128, -9564, -5570, 9717, -4540], ![22738, -6346, -21515, 1446, 8855], ![-73778, 34026, 56798, -24216, -8271]]]
  hmulB := by decide  
  f := ![![![-14001, 7582, -371, 315, -1880]], ![![18744, -10123, 495, -427, 2510]], ![![-21888, 11848, -578, 495, -2937]], ![![20072, -10844, 533, -454, 2690]], ![![-5615, 3056, -148, 125, -757]]]
  g := ![![![-534, -404, -583, -328, 1083], ![279, 259, 371, 178, -641], ![2316, 1652, 2390, 1409, -4540], ![-4369, -3302, -4765, -2683, 8855], ![3913, 3174, 4568, 2433, -8271]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 4 2 8 [222, 229, 265, 28, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [178, 203, 223, 34], [296, 280, 83, 219], [124, 142, 7, 60], [0, 1]]
 g := ![![[284, 164, 22, 39], [106, 126, 75], [272, 118, 215], [247, 216, 225, 163], [204, 154, 203, 64], [125, 244, 87, 158], [1], []], ![[240, 196, 20, 1, 77, 178], [1, 248, 161], [157, 18, 198], [263, 26, 287, 291, 304, 211], [275, 227, 119, 133, 10, 111], [154, 208, 208, 231, 129, 273], [256, 236, 309], [86, 11, 217]], ![[25, 8, 213, 110, 83, 211], [262, 162, 241], [24, 3, 166], [70, 170, 137, 146, 83, 146], [128, 22, 215, 309, 32, 257], [183, 155, 24, 223], [262, 5, 48], [32, 221, 72]], ![[170, 43, 88, 76, 155, 159], [48, 112, 108], [227, 283, 213], [294, 207, 125, 290, 114, 65], [54, 160, 151, 146, 269, 133], [111, 48, 213, 236, 252, 43], [2, 155, 66], [245, 200, 157]]]
 h' := ![![[178, 203, 223, 34], [156, 78, 99, 189], [63, 301, 149, 102], [254, 46, 149, 29], [97, 31, 102, 114], [107, 295, 247, 305], [91, 84, 48, 285], [0, 0, 1], [0, 1]], ![[296, 280, 83, 219], [42, 72, 284, 24], [175, 168, 281, 180], [35, 41, 273, 220], [112, 177, 169, 197], [279, 228, 54, 284], [310, 75, 163, 223], [72, 52, 164, 50], [178, 203, 223, 34]], ![[124, 142, 7, 60], [158, 243, 115, 304], [143, 274, 130, 159], [33, 107, 266, 127], [134, 219, 169, 190], [34, 94, 221, 153], [87, 33, 30], [71, 133, 192, 19], [296, 280, 83, 219]], ![[0, 1], [114, 233, 128, 109], [21, 196, 66, 185], [282, 119, 251, 250], [33, 199, 186, 125], [239, 9, 104, 197], [296, 121, 72, 118], [111, 128, 269, 244], [124, 142, 7, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [153, 251, 280], []]
 b := ![[], [], [212, 275, 131, 296], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 4
  hpos := by decide
  P := [222, 229, 265, 28, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15771505988367, -3725979184669, -16182816825364, -414170041240, 7809401222075]
  a := ![-121, 61, 62, -122, -243]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3866787494816, -2906123070113, -4193429455878, -2371588773605, 7809401222075]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 9597924961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14001, -7582, 371, -315, 1880]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![14001, -7582, 371, -315, 1880]] 
 ![![313, 0, 0, 0, 0], ![124, 1, 0, 0, 0], ![75, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![77, 0, 0, 0, 1]] where
  M :=![![![14001, -7582, 371, -315, 1880], ![-18744, 10123, -495, 427, -2510], ![21888, -11848, 578, -495, 2937], ![-20072, 10844, -533, 454, -2690], ![7074, -3834, 184, -162, 949]]]
  hmulB := by decide  
  f := ![![![-2889, 824, 2701, -221, -1083]], ![![-1102, 305, 1039, -71, -427]], ![![-731, 228, 665, -84, -245]], ![![-1411, 402, 1320, -107, -530]], ![![-475, 94, 483, 23, -240]]]
  g := ![![![2643, -7582, 371, -315, 1880], ![-3532, 10123, -495, 427, -2510], ![4132, -11848, 578, -495, 2937], ![-3781, 10844, -533, 454, -2690], ![1339, -3834, 184, -162, 949]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N1 : Nat.card (O ⧸ I313N1) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N1)

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := prime_ideal_of_norm_prime hp313.out _ NI313N1
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![2889, -824, -2701, 221, 1083]] ![![14001, -7582, 371, -315, 1880]]
  ![![313, 0, 0, 0, 0]] where
 M := ![![![-313, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC313 : ContainsPrimesAboveP 313 ![I313N0, I313N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
    exact isPrimeI313N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 313 (by decide) (𝕀 ⊙ MulI313N0)


lemma PB314I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 313 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 313 (by omega)

def PB314I7 : PrimesBelowBoundCertificateInterval O 307 313 314 where
  m := 2
  g := ![3, 2]
  P := ![311, 313]
  hP := PB314I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1, I311N2]
    · exact ![I313N0, I313N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC311
    · exact PBC313
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![30080231, 311, 311]
    · exact ![9597924961, 313]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI311N0
      exact NI311N1
      exact NI311N2
    · dsimp ; intro j
      fin_cases j
      exact NI313N0
      exact NI313N1
  β := ![I311N1, I311N2, I313N1]
  Il := ![[I311N1, I311N2], [I313N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
