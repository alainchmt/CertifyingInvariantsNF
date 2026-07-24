
import IdealArithmetic.Examples.NF3_1_557179_1.RI3_1_557179_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0]] 
 ![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [190, 107, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 122, 141], [116, 74, 56], [0, 1]]
 g := ![![[119, 122, 9], [24, 191], [137, 111, 34], [174, 39], [87, 55], [54, 114], [1]], ![[12, 15, 12, 194], [100, 156], [142, 154, 38, 179], [165, 42], [104, 83], [58, 47], [56, 10, 106, 108]], ![[37, 92, 31, 86], [151, 164], [185, 109, 83, 118], [62, 28], [91, 88], [60, 97], [113, 174, 139, 89]]]
 h' := ![![[45, 122, 141], [56, 57, 194], [171, 51, 114], [145, 190, 172], [122, 80, 165], [33, 23, 152], [7, 90, 161], [0, 1]], ![[116, 74, 56], [125, 131, 132], [193, 137, 64], [109, 140, 118], [147, 87, 47], [73, 143, 110], [109, 24, 176], [45, 122, 141]], ![[0, 1], [8, 9, 68], [112, 9, 19], [175, 64, 104], [23, 30, 182], [119, 31, 132], [68, 83, 57], [116, 74, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 63], []]
 b := ![[], [83, 98, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [190, 107, 36, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11323954, 20488, 174148]
  a := ![0, -2, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-57482, 104, 884]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀

instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-6, 69, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-6, 69, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![193, 69, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-6, 69, 1], ![-144, 64, 621], ![-9920, 53, -5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-193, -69, 199]], ![![-1, 0, 1], ![-603, -215, 621], ![-45, 2, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [182, 147, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 198], [0, 1]]
 g := ![![[85, 117], [157, 43], [120, 62], [9], [92], [46], [52, 1]], ![[0, 82], [5, 156], [160, 137], [9], [92], [46], [104, 198]]]
 h' := ![![[52, 198], [82, 52], [50, 21], [17, 96], [137, 3], [168, 106], [88, 134], [0, 1]], ![[0, 1], [0, 147], [147, 178], [34, 103], [94, 196], [108, 93], [91, 65], [52, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114]]
 b := ![[], [110, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [182, 147, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1196, -1768, 1725]
  a := ![-1, 1, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1679, -607, 1725]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-24, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-24, 1, 0]] 
 ![![199, 0, 0], ![175, 1, 0], ![5, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-24, 1, 0], ![0, -23, 9], ![-144, 1, -24]]]
  hmulB := by decide  
  f := ![![![3433, -143, 0], ![28457, 0, 0]], ![![3025, -126, 0], ![25075, 0, 0]], ![![107, 16, -8], ![887, 177, 0]]]
  g := ![![![1, 0, 0], ![-175, 199, 0], ![-5, 0, 199]], ![![-1, 1, 0], ![20, -23, 9], ![-1, 1, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-6, 69, 1]] ![![199, 0, 0], ![-24, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-4776, 199, 0]], ![![-1194, 13731, 199], ![0, -1592, 597]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-24, 1, 0]]], ![![![-6, 69, 1]], ![![0, -8, 3]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![56, 60, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![56, 60, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![56, 60, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![56, 60, 1], ![-144, 117, 540], ![-8624, 44, 57]]]
  hmulB := by decide  
  f := ![![![-55, -60, -1], ![211, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -60, 211]], ![![0, 0, 1], ![-144, -153, 540], ![-56, -16, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [109, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [138, 210], [0, 1]]
 g := ![![[51, 151], [162, 53], [4], [19], [170, 179], [71], [138, 1]], ![[0, 60], [91, 158], [4], [19], [185, 32], [71], [65, 210]]]
 h' := ![![[138, 210], [66, 183], [22, 106], [6, 209], [38, 21], [202, 50], [150, 156], [0, 1]], ![[0, 1], [0, 28], [91, 105], [152, 2], [193, 190], [139, 161], [156, 55], [138, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [14, 116]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [109, 73, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-451, -16, 56]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17, -16, 56]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![93, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![93, 1, 0]] 
 ![![211, 0, 0], ![93, 1, 0], ![154, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![93, 1, 0], ![0, 94, 9], ![-144, 1, 93]]]
  hmulB := by decide  
  f := ![![![3256, 35, 0], ![-7385, 0, 0]], ![![1302, 14, 0], ![-2953, 0, 0]], ![![2320, 4, -2], ![-5262, 47, 0]]]
  g := ![![![1, 0, 0], ![-93, 211, 0], ![-154, 0, 211]], ![![0, 1, 0], ![-48, 94, 9], ![-69, 1, 93]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![56, 60, 1]] ![![211, 0, 0], ![93, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![19623, 211, 0]], ![![11816, 12660, 211], ![5064, 5697, 633]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![93, 1, 0]]], ![![![56, 60, 1]], ![![24, 27, 3]]]]
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


lemma PB212I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 211 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 211 (by omega)

def PB212I4 : PrimesBelowBoundCertificateInterval O 193 211 212 where
  m := 3
  g := ![1, 2, 2]
  P := ![197, 199, 211]
  hP := PB212I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1]
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
    · exact ![7645373]
    · exact ![39601, 199]
    · exact ![44521, 211]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
  β := ![I199N1, I211N1]
  Il := ![[], [I199N1], [I211N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
