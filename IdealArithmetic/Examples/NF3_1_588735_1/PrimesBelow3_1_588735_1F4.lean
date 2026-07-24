
import IdealArithmetic.Examples.NF3_1_588735_1.RI3_1_588735_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2647, 14, 87]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![2647, 14, 87]] 
 ![![197, 0, 0], ![0, 197, 0], ![121, 93, 1]] where
  M :=![![![2647, 14, 87], ![4813, 23, 157], ![1640, 15, 51]]]
  hmulB := by decide  
  f := ![![![-6, 3, 1]], ![![61, -39, 16]], ![![26, -17, 8]]]
  g := ![![![-40, -41, 87], ![-72, -74, 157], ![-23, -24, 51]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [80, 163, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 196], [0, 1]]
 g := ![![[103, 83], [55], [84, 63], [193], [101], [7], [34, 1]], ![[167, 114], [55], [59, 134], [193], [101], [7], [68, 196]]]
 h' := ![![[34, 196], [24, 87], [175, 45], [72, 76], [151, 169], [96, 62], [38, 91], [0, 1]], ![[0, 1], [27, 110], [129, 152], [95, 121], [184, 28], [37, 135], [177, 106], [34, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [91, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [80, 163, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8, 125, -1545]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![949, 730, -1545]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, -3, -1]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![6, -3, -1]] 
 ![![197, 0, 0], ![125, 1, 0], ![13, 0, 1]] where
  M :=![![![6, -3, -1], ![-61, 39, -16], ![-175, 85, 33]]]
  hmulB := by decide  
  f := ![![![-2647, -14, -87]], ![![-1704, -9, -56]], ![![-183, -1, -6]]]
  g := ![![![2, -3, -1], ![-24, 39, -16], ![-57, 85, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![2647, 14, 87]] ![![6, -3, -1]]
  ![![197, 0, 0]] where
 M := ![![![-197, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [36, 105, 168, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 0, 24], [125, 198, 175], [0, 1]]
 g := ![![[80, 153, 47], [164, 129, 157], [180, 118, 92], [165, 28], [151, 175], [197, 165], [1]], ![[139, 146, 85, 197], [38, 54, 23, 142], [167, 110, 104, 12], [87, 117], [177, 86], [84, 102], [152, 159, 97, 93]], ![[94, 101, 134, 14], [178, 69, 105, 46], [168, 37, 107, 104], [30, 132], [128, 98], [60, 111], [45, 167, 165, 106]]]
 h' := ![![[105, 0, 24], [66, 33, 131], [87, 75, 117], [61, 4, 106], [164, 173, 25], [174, 39, 162], [163, 94, 31], [0, 1]], ![[125, 198, 175], [25, 36, 64], [0, 20, 91], [105, 178, 189], [75, 57, 147], [26, 43, 177], [142, 7, 36], [105, 0, 24]], ![[0, 1], [11, 130, 4], [20, 104, 190], [147, 17, 103], [113, 168, 27], [12, 117, 59], [111, 98, 132], [125, 198, 175]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [177, 73], []]
 b := ![[], [108, 197, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [36, 105, 168, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3078331, -2026815, 973110]
  a := ![5, -5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15469, -10185, 4890]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![92, 40, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![92, 40, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![92, 40, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![92, 40, 1], ![135, 22, 201], ![2210, -1195, 102]]]
  hmulB := by decide  
  f := ![![![-91, -40, -1], ![211, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-92, -40, 211]], ![![0, 0, 1], ![-87, -38, 201], ![-34, -25, 102]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [71, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [123, 210], [0, 1]]
 g := ![![[132, 107], [82, 9], [24], [107], [173, 137], [21], [123, 1]], ![[0, 104], [134, 202], [24], [107], [144, 74], [21], [35, 210]]]
 h' := ![![[123, 210], [86, 188], [206, 208], [125, 119], [166, 23], [169, 83], [129, 77], [0, 1]], ![[0, 1], [0, 23], [48, 3], [203, 92], [41, 188], [39, 128], [105, 134], [123, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [180]]
 b := ![[], [162, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [71, 88, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![146257, 104313, -525330]
  a := ![-66, 2, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![229747, 100083, -525330]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![10, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![10, 1, 0]] 
 ![![211, 0, 0], ![10, 1, 0], ![109, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![10, 1, 0], ![2, 9, 5], ![55, -30, 11]]]
  hmulB := by decide  
  f := ![![![45451, 205185, 114000], ![3165, -4810800, 0]], ![![2150, 9719, 5400], ![212, -227880, 0]], ![![23479, 105996, 58891], ![1644, -2485200, 0]]]
  g := ![![![1, 0, 0], ![-10, 211, 0], ![-109, 0, 211]], ![![0, 1, 0], ![-3, 9, 5], ![-4, -30, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![92, 40, 1]] ![![211, 0, 0], ![10, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![2110, 211, 0]], ![![19412, 8440, 211], ![1055, 422, 211]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![10, 1, 0]]], ![![![92, 40, 1]], ![![5, 2, 1]]]]
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


lemma PB218I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 217 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 217 (by omega)

def PB218I4 : PrimesBelowBoundCertificateInterval O 193 217 218 where
  m := 3
  g := ![2, 1, 2]
  P := ![197, 199, 211]
  hP := PB218I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
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
    · exact ![38809, 197]
    · exact ![7880599]
    · exact ![44521, 211]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
  β := ![I197N1, I211N1]
  Il := ![[I197N1], [], [I211N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
