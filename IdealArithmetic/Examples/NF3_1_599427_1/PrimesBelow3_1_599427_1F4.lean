
import IdealArithmetic.Examples.NF3_1_599427_1.RI3_1_599427_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, 195, -36]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-22, 195, -36]] 
 ![![197, 0, 0], ![0, 197, 0], ![121, 11, 1]] where
  M :=![![![-22, 195, -36], ![-5364, -22, 195], ![29055, -5364, -22]]]
  hmulB := by decide  
  f := ![![![-5312, -1002, -189]], ![![-28161, -5312, -1002]], ![![-5593, -1055, -199]]]
  g := ![![![22, 3, -36], ![-147, -11, 195], ![161, -26, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [35, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [132, 196], [0, 1]]
 g := ![![[30, 61], [178], [147, 61], [146], [181], [51], [132, 1]], ![[5, 136], [178], [122, 136], [146], [181], [51], [67, 196]]]
 h' := ![![[132, 196], [12, 109], [174, 93], [102, 109], [22, 151], [29, 56], [108, 53], [0, 1]], ![[0, 1], [19, 88], [39, 104], [109, 88], [57, 46], [132, 141], [12, 144], [132, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [149, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [35, 65, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![333, 84, -64]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![41, 4, -64]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5312, 1002, 189]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![5312, 1002, 189]] 
 ![![197, 0, 0], ![186, 1, 0], ![76, 0, 1]] where
  M :=![![![5312, 1002, 189], ![28161, 5312, 1002], ![149298, 28161, 5312]]]
  hmulB := by decide  
  f := ![![![22, -195, 36]], ![![48, -184, 33]], ![![-139, -48, 14]]]
  g := ![![![-992, 1002, 189], ![-5259, 5312, 1002], ![-27880, 28161, 5312]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-22, 195, -36]] ![![5312, 1002, 189]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [55, 98, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [116, 87, 92], [80, 111, 107], [0, 1]]
 g := ![![[139, 60, 165], [120, 173, 8], [45, 34, 90], [164, 111], [80, 36], [163, 9], [1]], ![[197, 97, 101, 16], [30, 52], [15, 195, 64, 126], [128, 18], [73, 14], [95, 16], [6, 110, 2, 1]], ![[42, 88, 74, 107], [196, 88, 112, 60], [156, 126, 0, 168], [62, 49], [69, 65], [185, 1], [44, 146, 78, 198]]]
 h' := ![![[116, 87, 92], [166, 25, 31], [112, 194, 40], [92, 73, 182], [82, 75, 132], [30, 82, 6], [144, 101, 196], [0, 1]], ![[80, 111, 107], [34, 47, 169], [17, 138], [170, 33, 53], [134, 38, 60], [13, 46, 51], [8, 192, 4], [116, 87, 92]], ![[0, 1], [197, 127, 198], [105, 66, 159], [188, 93, 163], [195, 86, 7], [72, 71, 142], [140, 105, 198], [80, 111, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [158, 81], []]
 b := ![[], [191, 172, 170], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [55, 98, 3, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![598194, 5174, -7761]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3006, 26, -39]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [102, 75, 192, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 107, 86], [198, 103, 125], [0, 1]]
 g := ![![[190, 35, 134], [188, 70, 46], [115, 178], [149, 79], [21, 51, 36], [0, 150], [1]], ![[62, 103, 88, 41], [41, 44, 186, 91], [18, 126], [63, 121], [124, 82, 120, 149], [59, 46], [195, 99, 194, 102]], ![[64, 135, 210, 37], [80, 171, 37, 101], [170, 137], [81, 5], [70, 208, 177, 208], [126, 161], [100, 135, 195, 109]]]
 h' := ![![[32, 107, 86], [25, 133, 150], [189, 82, 62], [174, 193, 38], [179, 191, 76], [65, 0, 205], [109, 136, 19], [0, 1]], ![[198, 103, 125], [46, 163, 91], [106, 84, 145], [185, 58, 45], [80, 140, 200], [150, 31, 15], [7, 141, 149], [32, 107, 86]], ![[0, 1], [210, 126, 181], [142, 45, 4], [32, 171, 128], [109, 91, 146], [191, 180, 202], [52, 145, 43], [198, 103, 125]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 146], []]
 b := ![[], [71, 62, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [102, 75, 192, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![497538, -12660, 12660]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2358, -60, 60]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀



lemma PB220I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 219 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 219 (by omega)

def PB220I4 : PrimesBelowBoundCertificateInterval O 193 219 220 where
  m := 3
  g := ![2, 1, 1]
  P := ![197, 199, 211]
  hP := PB220I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0]
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
    · exact ![9393931]
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
  β := ![I197N1]
  Il := ![[I197N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
