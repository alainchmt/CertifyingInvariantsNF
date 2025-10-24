import IdealArithmetic.Examples.NF6.PrimesBelow3

open Classical Polynomial

noncomputable section

instance hp109 : Fact (Nat.Prime 109) := by decide
def I109N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0, 0, 0]] i)))

def SI109N: IdealEqSpanCertificate O ℤ timesTableO I109N
 ![![109, 0, 0, 0, 0]]
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI109N : Nat.card (O ⧸ I109N) = 15386239549 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI109N)

def MemCI109N : IdealMemCertificate O ℤ B I109N
  ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]] ![-33445296220, 44291906712, -26324472062, -77897316084, -233826635192] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI109N
 g := ![-306837580, 406347768, -241508918, -714654276, -2145198488]
 hmem := by decide

def P109P : CertificateIrreducibleZModOfList' 109 5 2 6 [32, 40, 39, 101, 105, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 46, 32, 10, 67], [97, 16, 45, 34, 50], [19, 76, 73, 37, 49], [37, 79, 68, 28, 52], [0, 1]]
 g := ![![[83, 64, 3, 102, 108], [107, 31, 85, 3], [85, 30, 105, 72, 71], [32, 55, 69, 6, 31], [4, 1], []],![[40, 10, 100, 8, 28, 72, 77, 90], [59, 2, 70, 9], [85, 32, 94, 81, 71, 30, 31, 50], [108, 64, 26, 74, 93, 1, 1, 58], [89, 32, 108, 84], [21, 67, 30, 29, 108, 9, 74, 32]],![[87, 16, 61, 6, 77, 61, 41, 99], [104, 98, 31, 16], [34, 74, 27, 91, 7, 27, 1, 103], [70, 84, 47, 62, 10, 14, 64, 8], [61, 4, 11, 108], [23, 87, 94, 58, 16, 97, 66, 86]],![[59, 37, 79, 88, 41, 56, 76, 36], [17, 48, 90, 81], [2, 46, 10, 31, 44, 16, 42, 87], [27, 47, 22, 61, 76, 64, 67, 9], [107, 48, 2, 75], [83, 97, 63, 28, 84, 96, 49, 38]],![[89, 84, 3, 106, 57, 84, 97, 56], [46, 64, 69, 108], [60, 73, 13, 84, 31, 70, 59, 8], [28, 72, 93, 32, 88, 6, 81, 52], [97, 80, 86, 102], [102, 89, 1, 52, 75, 63, 81, 107]]]
 h' := ![![[69, 46, 32, 10, 67], [89, 29, 13, 5, 76], [5, 105, 50, 33, 49], [66, 46, 5, 13, 17], [90, 26, 22, 102, 24], [0, 0, 0, 1], [0, 1]],![[97, 16, 45, 34, 50], [1, 99, 6, 92, 47], [103, 35, 98, 67, 106], [49, 72, 38, 2, 107], [12, 12, 63, 96, 3], [74, 34, 79, 33, 56], [69, 46, 32, 10, 67]],![[19, 76, 73, 37, 49], [22, 21, 30, 68, 95], [84, 100, 68, 45, 105], [53, 69, 90, 92, 40], [6, 57, 75, 97, 65], [43, 47, 5, 84, 76], [97, 16, 45, 34, 50]],![[37, 79, 68, 28, 52], [81, 57, 3, 62, 32], [84, 57, 93, 13, 100], [104, 48, 30, 19, 107], [79, 3, 20, 1, 16], [61, 20, 0, 51, 27], [19, 76, 73, 37, 49]],![[0, 1], [28, 12, 57, 100, 77], [65, 30, 18, 60, 76], [31, 92, 55, 92, 56], [79, 11, 38, 31, 1], [83, 8, 25, 49, 59], [37, 79, 68, 28, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 53, 21, 98], [], [], []]
 b := ![[], [57, 0, 30, 22, 75], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N : PrimeIdeal O 109 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I109N
  hcard := NI109N
  P := [32, 40, 39, 101, 105, 1]
  f := ofList [32, 40, 39, 101, 105, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P109P
  hneq := by decide
  hlen := by decide
  c := ![-33445296220, 44291906712, -26324472062, -77897316084, -233826635192]
  a := ![-14, 1, -14, -20, -56]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI109N
  hpmem := by
    show  _ ∈ I109N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI109N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI109N : Ideal.IsPrime I109N := PrimeIdeal_isPrime PI109N
def PBC109 : PrimesBelowPCertificate 109 ![I109N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI109N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I109N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp113 : Fact (Nat.Prime 113) := by decide
def I113N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0]] i)))

def SI113N: IdealEqSpanCertificate O ℤ timesTableO I113N
 ![![113, 0, 0, 0, 0]]
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI113N : Nat.card (O ⧸ I113N) = 18424351793 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI113N)

def MemCI113N : IdealMemCertificate O ℤ B I113N
  ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]] ![514898851, -24842711, 240811249, -441681292, 435245490] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI113N
 g := ![4556627, -219847, 2131073, -3908684, 3851730]
 hmem := by decide

def P113P : CertificateIrreducibleZModOfList' 113 5 2 6 [49, 15, 58, 46, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 105, 43, 15, 6], [111, 16, 45, 14, 55], [88, 17, 6, 13, 106], [49, 87, 19, 71, 59], [0, 1]]
 g := ![![[102, 74, 58, 92, 69], [5, 108, 25, 95], [6, 20, 26, 112], [89, 43, 17, 61], [83, 109, 1], []],![[4, 26, 109, 70, 47, 67, 76, 79], [66, 31, 29, 13], [95, 30, 74, 44], [57, 39, 18, 98], [108, 71, 68, 14, 94, 101, 109, 79], [86, 44, 65, 92, 11, 28, 78, 103]],![[63, 29, 23, 92, 91, 1, 99, 33], [32, 36, 111, 82], [58, 103, 19, 2], [80, 14, 82, 57], [43, 33, 108, 87, 49, 106, 88, 19], [99, 20, 5, 70, 39, 49, 108, 39]],![[51, 47, 25, 85, 60, 59, 0, 60], [40, 13, 72, 25], [40, 45, 72, 88], [0, 70, 21, 72], [82, 24, 70, 3, 74, 83, 80, 30], [54, 67, 48, 100, 104, 92, 6, 109]],![[4, 56, 97, 37, 89, 18, 98, 47], [60, 5, 14, 100], [62, 59, 68, 81], [25, 104, 109, 2], [14, 69, 12, 46, 89, 71, 85, 80], [25, 90, 53, 107, 2, 52, 54, 58]]]
 h' := ![![[87, 105, 43, 15, 6], [17, 9, 15, 1, 71], [107, 4, 59, 30, 35], [47, 110, 33, 61, 15], [1, 81, 56, 15, 20], [0, 0, 0, 1], [0, 1]],![[111, 16, 45, 14, 55], [107, 90, 43, 38, 91], [105, 0, 71, 24, 37], [63, 101, 19, 28, 65], [12, 30, 68, 20, 95], [19, 105, 42, 52, 91], [87, 105, 43, 15, 6]],![[88, 17, 6, 13, 106], [86, 3, 0, 11, 59], [80, 43, 36, 6, 46], [53, 101, 69, 23, 62], [40, 111, 82, 108, 82], [0, 100, 62, 78, 108], [111, 16, 45, 14, 55]],![[49, 87, 19, 71, 59], [85, 59, 95, 30, 13], [89, 86, 78, 85, 5], [44, 29, 86, 42, 75], [48, 89, 86, 21, 80], [35, 97, 36, 77, 49], [88, 17, 6, 13, 106]],![[0, 1], [2, 65, 73, 33, 105], [111, 93, 95, 81, 103], [95, 111, 19, 72, 9], [23, 28, 47, 62, 62], [34, 37, 86, 18, 91], [49, 87, 19, 71, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 26, 31, 80], [], [], []]
 b := ![[], [107, 63, 82, 69, 62], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N : PrimeIdeal O 113 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I113N
  hcard := NI113N
  P := [49, 15, 58, 46, 4, 1]
  f := ofList [49, 15, 58, 46, 4, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P113P
  hneq := by decide
  hlen := by decide
  c := ![514898851, -24842711, 240811249, -441681292, 435245490]
  a := ![-6, -1, -5, -8, -18]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI113N
  hpmem := by
    show  _ ∈ I113N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI113N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI113N : Ideal.IsPrime I113N := PrimeIdeal_isPrime PI113N
def PBC113 : PrimesBelowPCertificate 113 ![I113N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI113N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I113N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp127 : Fact (Nat.Prime 127) := by decide
def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0, 0, 0], ![31, -9, -3, -1, -5]] i)))

def SI127N0: IdealEqSpanCertificate O ℤ timesTableO I127N0
 ![![127, 0, 0, 0, 0], ![31, -9, -3, -1, -5]]
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![18, 101, 1, 0, 0], ![107, 116, 0, 1, 0], ![114, 45, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![0, 0, 0, 0, 127]], ![![31, -9, -3, -1, -5], ![-3, 29, -11, 1, 3], ![3, -15, 31, -25, 3], ![-36, 15, -27, -10, -156], ![-2, -1, 1, 26, 69]]]
  hmulB := by decide
  f := ![![![74185488, -893885511, 342597969, -30058409, -90063667], ![77144245, 3939472563, 1796415, 0, 0]], ![![25935289, -312502996, 119772493, -10508443, -31486319], ![26969720, 1377242356, 628015, 0, 0]], ![![31135435, -375161216, 143787400, -12615431, -37799465], ![32377238, 1653385475, 753940, 0, 0]], ![![86191685, -1038551954, 398044028, -34923065, -104639574], ![89629200, 4577036831, 2087135, 0, 0]], ![![75781397, -913114836, 349967955, -30705029, -92001126], ![78803668, 4024218726, 1835055, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-18, -101, 127, 0, 0], ![-107, -116, 0, 127, 0], ![-114, -45, 0, 0, 127]], ![![6, 5, -3, -1, -5], ![-2, 7, -11, 1, 3], ![14, -3, 31, -25, 3], ![152, 86, -27, -10, -156], ![-84, -49, 1, 26, 69]]]
  hle1 := by decide
  hle2 := by decide

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI127N0)

def MemCI127N0 : IdealMemCertificate O ℤ B I127N0
  ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![18, 101, 1, 0, 0], ![107, 116, 0, 1, 0], ![114, 45, 0, 0, 1]] ![2427, -1372, 2270, 4478, 12626] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI127N0
 g := ![-15409, -10380, 2270, 4478, 12626]
 hmem := by decide

def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [63, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 126], [0, 1]]
 g := ![![[17, 22], [124, 9], [37, 60], [44, 52], [32, 30], [72, 1]],![[77, 105], [10, 118], [39, 67], [105, 75], [33, 97], [17, 126]]]
 h' := ![![[72, 126], [62, 99], [82, 3], [22, 21], [16, 59], [36, 41], [0, 1]],![[0, 1], [78, 28], [44, 124], [10, 106], [73, 68], [67, 86], [72, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [51, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : PrimeIdeal O 127 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I127N0
  hcard := NI127N0
  P := [63, 55, 1]
  f := ofList [63, 55, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P127P0
  hneq := by decide
  hlen := by decide
  c := ![2427, -1372, 2270, 4478, 12626]
  a := ![13, 0, 14, 18, 50]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI127N0
  hpmem := by
    show  _ ∈ I127N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI127N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := PrimeIdeal_isPrime PI127N0
def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0, 0, 0], ![-17, -49, -3, -1, -5]] i)))

def SI127N1: IdealEqSpanCertificate O ℤ timesTableO I127N1
 ![![127, 0, 0, 0, 0], ![-17, -49, -3, -1, -5]]
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![90, 50, 1, 0, 0], ![36, 2, 0, 1, 0], ![120, 81, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![0, 0, 0, 0, 127]], ![![-17, -49, -3, -1, -5], ![-3, -19, -51, 1, 3], ![3, -55, -17, -105, 3], ![-156, 55, -107, -178, -636], ![-2, -1, 1, 106, 141]]]
  hmulB := by decide
  f := ![![![-1186765, -9588326, -30287250, 635106, 1964602], ![4491482, -75686920, 4572, 0, 0]], ![![-69375870, -560511997, -1770517056, 37124942, 114845592], ![262556625, -4424467529, 265176, 0, 0]], ![![-28149640, -227430844, -718397183, 15063674, 46599242], ![106533868, -1795252420, 107622, 0, 0]], ![![-1428936, -11544902, -36467520, 764675, 2365488], ![5407950, -91131214, 5472, 0, 0]], ![![-45368968, -366551777, -1157845290, 24278212, 75104289], ![171701197, -2893419687, 173448, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-90, -50, 127, 0, 0], ![-36, -2, 0, 127, 0], ![-120, -81, 0, 0, 127]], ![![7, 4, -3, -1, -5], ![33, 18, -51, 1, 3], ![39, 6, -17, -105, 3], ![726, 451, -107, -178, -636], ![-164, -92, 1, 106, 141]]]
  hle1 := by decide
  hle2 := by decide

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI127N1)

def MemCI127N1 : IdealMemCertificate O ℤ B I127N1
  ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![90, 50, 1, 0, 0], ![36, 2, 0, 1, 0], ![120, 81, 0, 0, 1]] ![-648, -167, 415, 4687, 5040] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI127N1
 g := ![-6390, -3453, 415, 4687, 5040]
 hmem := by decide

def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [120, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 126], [0, 1]]
 g := ![![[28, 18], [74, 11], [112, 18], [58, 117], [66, 62], [69, 1]],![[0, 109], [71, 116], [84, 109], [3, 10], [26, 65], [11, 126]]]
 h' := ![![[69, 126], [10, 79], [22, 97], [25, 79], [81, 25], [102, 69], [0, 1]],![[0, 1], [0, 48], [111, 30], [15, 48], [28, 102], [37, 58], [69, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [5, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : PrimeIdeal O 127 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I127N1
  hcard := NI127N1
  P := [120, 58, 1]
  f := ofList [120, 58, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P127P1
  hneq := by decide
  hlen := by decide
  c := ![-648, -167, 415, 4687, 5040]
  a := ![8, 3, 9, 19, 36]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI127N1
  hpmem := by
    show  _ ∈ I127N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI127N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := PrimeIdeal_isPrime PI127N1
def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0, 0, 0], ![-24, 1, 0, 0, 0]] i)))

def SI127N2: IdealEqSpanCertificate O ℤ timesTableO I127N2
 ![![127, 0, 0, 0, 0], ![-24, 1, 0, 0, 0]]
 ![![127, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![59, 0, 1, 0, 0], ![85, 0, 0, 1, 0], ![116, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![0, 0, 0, 0, 127]], ![![-24, 1, 0, 0, 0], ![0, -24, 1, 0, 0], ![0, 1, -24, 2, 0], ![3, -1, 2, -21, 12], ![0, 0, 0, -2, -27]]]
  hmulB := by decide
  f := ![![![-4664909, 542722, -8892923, 748030, -3960], ![-24679910, -118999, -47059850, 41910, 0]], ![![-4666133, 542898, -8895923, 748280, -3960], ![-24686386, -118999, -47075725, 41910, 0]], ![![-3111295, 362005, -5932015, 498970, -2640], ![-16460446, -79374, -31391225, 27940, 0]], ![![-3109913, 361830, -5928572, 498683, -2640], ![-16453134, -79236, -31373000, 27940, 0]], ![![-4260844, 495718, -8122670, 683240, -3617], ![-22542186, -108670, -42983800, 38280, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-103, 127, 0, 0, 0], ![-59, 0, 127, 0, 0], ![-85, 0, 0, 127, 0], ![-116, 0, 0, 0, 127]], ![![-1, 1, 0, 0, 0], ![19, -24, 1, 0, 0], ![9, 1, -24, 2, 0], ![3, -1, 2, -21, 12], ![26, 0, 0, -2, -27]]]
  hle1 := by decide
  hle2 := by decide

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulEqCertificate O ℤ timesTableO (I127N0) I127N1
  ![![127, 0, 0, 0, 0], ![31, -9, -3, -1, -5]] ![![127, 0, 0, 0, 0], ![-17, -49, -3, -1, -5]]
  ![![127, 0, 0, 0, 0], ![-71, -273, 190, 67, 312]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![16129, 0, 0, 0, 0], ![-2159, -6223, -381, -127, -635]], ![![3937, -1143, -381, -127, -635], ![-343, -1233, 519, -77, -260]]]
 hmul := by decide
 f :=  ![![![![4073938709073602742, 32914779953411558205, 103969533126580146975, -2180070212182350883, -6744042623348073736], ![-15418027494663270137, 259816654558411997168, -15564133435384836, 0, 0]], ![![-883427759508, -59863443, 0, 0, 0], ![14859, 0, 0, 0, 0]]], ![![![-2278111611419986435, -18405662861887194899, -58138871878962767402, 1219076578894530389, 3771210836810599057], ![8621628838587032379, -145287246534056873729, 8703330028473348, 0, 0]], ![![494005231916, 33475125, 0, 0, 0], ![-8307, 0, 0, 0, 0]]]]
 g :=  ![![![![127, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![54, 224, -193, -68, -317], ![127, 0, 0, 0, 0]]], ![![![31, -9, -3, -1, -5], ![0, 0, 0, 0, 0]], ![![56, 216, -153, -56, -260], ![105, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI127N1 : IdealMulEqCertificate O ℤ timesTableO (I127N0*I127N1) I127N2
  ![![127, 0, 0, 0, 0], ![-71, -273, 190, 67, 312]] ![![127, 0, 0, 0, 0], ![-24, 1, 0, 0, 0]]
  ![![127, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI127N0
 hI2 := rfl
 M :=  ![![![16129, 0, 0, 0, 0], ![-3048, 127, 0, 0, 0]], ![![-9017, -34671, 24130, 8509, 39624], ![1905, 6604, -4699, -1651, -7620]]]
 hmul := by decide
 f :=  ![![![![-1175711361023663, 50247976909552, -12572427278435, 1054819585978, -5573702736], ![-6221465245210256, 3900298648913, -66361666204550, 58988336016, 0]], ![![690, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![127, 0, 0, 0, 0]], ![![-24, 1, 0, 0, 0]]], ![![![-71, -273, 190, 67, 312]], ![![15, 52, -37, -13, -60]]]]
 hle1 := by decide
 hle2 := by decide

def PBC127 : PrimesBelowPCertificate 127 ![I127N0, I127N1, I127N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI127N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp131 : Fact (Nat.Prime 131) := by decide
def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0], ![-49, 36, -3, -1, -5]] i)))

def SI131N0: IdealEqSpanCertificate O ℤ timesTableO I131N0
 ![![131, 0, 0, 0, 0], ![-49, 36, -3, -1, -5]]
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![121, 40, 1, 0, 0], ![69, 47, 0, 1, 0], ![2, 38, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]], ![![-49, 36, -3, -1, -5], ![-3, -51, 34, 1, 3], ![3, 30, -49, 65, 3], ![99, -30, 63, 45, 384], ![-2, -1, 1, -64, -146]]]
  hmulB := by decide
  f := ![![![-18141842, -120038304, 84533939, 2390669, 6443481], ![-28401717, -328500316, -201216, 0, 0]], ![![-10200942, -67496105, 47532416, 1344266, 3623094], ![-15969948, -184711834, -113184, 0, 0]], ![![-19867433, -131455948, 92574523, 2618068, 7056364], ![-31103192, -359746180, -220368, 0, 0]], ![![-13215519, -87442433, 61579124, 1741501, 4693782], ![-20689392, -239297542, -146592, 0, 0]], ![![-3236003, -21411686, 15078625, 426439, 1149350], ![-5066055, -58595804, -35904, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-121, -40, 131, 0, 0], ![-69, -47, 0, 131, 0], ![-2, -38, 0, 0, 131]], ![![3, 3, -3, -1, -5], ![-32, -12, 34, 1, 3], ![11, -9, -49, 65, 3], ![-87, -147, 63, 45, 384], ![35, 65, 1, -64, -146]]]
  hle1 := by decide
  hle2 := by decide

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI131N0)

def MemCI131N0 : IdealMemCertificate O ℤ B I131N0
  ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![121, 40, 1, 0, 0], ![69, 47, 0, 1, 0], ![2, 38, 0, 0, 1]] ![1952, -576, 904, -600, 3664] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI131N0
 g := ![-560, -1128, 904, -600, 3664]
 hmem := by decide

def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [19, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 130], [0, 1]]
 g := ![![[23, 49], [12, 123], [81], [125], [33], [102], [1]],![[94, 82], [102, 8], [81], [125], [33], [102], [1]]]
 h' := ![![[87, 130], [34, 7], [11, 56], [41, 9], [53, 115], [126, 66], [112, 87], [0, 1]],![[0, 1], [119, 124], [36, 75], [38, 122], [102, 16], [104, 65], [83, 44], [87, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [89, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : PrimeIdeal O 131 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I131N0
  hcard := NI131N0
  P := [19, 44, 1]
  f := ofList [19, 44, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P131P0
  hneq := by decide
  hlen := by decide
  c := ![1952, -576, 904, -600, 3664]
  a := ![-11, 4, -10, -8, -40]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI131N0
  hpmem := by
    show  _ ∈ I131N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI131N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := PrimeIdeal_isPrime PI131N0
def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0], ![-20, 8, -3, -1, -5]] i)))

def SI131N1: IdealEqSpanCertificate O ℤ timesTableO I131N1
 ![![131, 0, 0, 0, 0], ![-20, 8, -3, -1, -5]]
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![52, 30, 1, 0, 0], ![6, 35, 0, 1, 0], ![24, 52, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]], ![![-20, 8, -3, -1, -5], ![-3, -22, 6, 1, 3], ![3, 2, -20, 9, 3], ![15, -2, 7, -10, 48], ![-2, -1, 1, -8, -33]]]
  hmulB := by decide
  f := ![![![202100799, 1398226132, -380983923, -63167891, -188534875], ![70935845, 8351539248, -623298, 0, 0]], ![![248721511, 1720769679, -468869505, -77739490, -232026200], ![87299317, 10278076731, -767136, 0, 0]], ![![137142784, 948816794, -258530390, -42864851, -127937143], ![48136043, 5667238290, -422974, 0, 0]], ![![75708849, 523788511, -142720122, -23663278, -70626915], ![26573292, 3128564283, -233508, 0, 0]], ![![135755248, 939217180, -255914721, -42431167, -126642744], ![47649031, 5609900244, -418704, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-52, -30, 131, 0, 0], ![-6, -35, 0, 131, 0], ![-24, -52, 0, 0, 131]], ![![2, 3, -3, -1, -5], ![-3, -3, 6, 1, 3], ![7, 1, -20, 9, 3], ![-11, -18, 7, -10, 48], ![6, 15, 1, -8, -33]]]
  hle1 := by decide
  hle2 := by decide

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI131N1)

def MemCI131N1 : IdealMemCertificate O ℤ B I131N1
  ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![52, 30, 1, 0, 0], ![6, 35, 0, 1, 0], ![24, 52, 0, 0, 1]] ![-432, 68, -554, -210, -1014] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI131N1
 g := ![412, 586, -554, -210, -1014]
 hmem := by decide

def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [28, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 130], [0, 1]]
 g := ![![[102, 117], [4, 20], [4], [15], [49], [21], [1]],![[0, 14], [0, 111], [4], [15], [49], [21], [1]]]
 h' := ![![[26, 130], [19, 95], [17, 85], [28, 2], [102, 88], [65, 7], [103, 26], [0, 1]],![[0, 1], [0, 36], [0, 46], [80, 129], [32, 43], [116, 124], [124, 105], [26, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [112, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : PrimeIdeal O 131 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I131N1
  hcard := NI131N1
  P := [28, 105, 1]
  f := ofList [28, 105, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P131P1
  hneq := by decide
  hlen := by decide
  c := ![-432, 68, -554, -210, -1014]
  a := ![-5, 0, -6, -2, -10]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI131N1
  hpmem := by
    show  _ ∈ I131N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI131N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := PrimeIdeal_isPrime PI131N1
def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0], ![61, 1, 0, 0, 0]] i)))

def SI131N2: IdealEqSpanCertificate O ℤ timesTableO I131N2
 ![![131, 0, 0, 0, 0], ![61, 1, 0, 0, 0]]
 ![![131, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![78, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]], ![![61, 1, 0, 0, 0], ![0, 61, 1, 0, 0], ![0, 1, 61, 2, 0], ![3, -1, 2, 64, 12], ![0, 0, 0, -2, 58]]]
  hmulB := by decide
  f := ![![![510755371, 22850192, 1350194114, 44760080, 91464], ![-1096818984, 16430806, -2899833816, -998482, 0]], ![![238022225, 10648654, 629217821, 20859104, 42624], ![-511139598, 7657081, -1351381328, -465312, 0]], ![![307444704, 13754476, 812737449, 26942936, 55056], ![-660220542, 9890370, -1745529412, -601028, 0]], ![![54546678, 2440296, 144195496, 4780203, 9768], ![-117135982, 1754780, -309691008, -106634, 0]], ![![19494423, 872114, 51534126, 1708400, 3491], ![-41863198, 627194, -110680680, -38110, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-61, 131, 0, 0, 0], ![-78, 0, 131, 0, 0], ![-14, 0, 0, 131, 0], ![-5, 0, 0, 0, 131]], ![![0, 1, 0, 0, 0], ![-29, 61, 1, 0, 0], ![-37, 1, 61, 2, 0], ![-8, -1, 2, 64, 12], ![-2, 0, 0, -2, 58]]]
  hle1 := by decide
  hle2 := by decide

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulEqCertificate O ℤ timesTableO (I131N0) I131N1
  ![![131, 0, 0, 0, 0], ![-49, 36, -3, -1, -5]] ![![131, 0, 0, 0, 0], ![-20, 8, -3, -1, -5]]
  ![![131, 0, 0, 0, 0], ![-8, -116, -2, -12, 7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![17161, 0, 0, 0, 0], ![-2620, 1048, -393, -131, -655]], ![![-6419, 4716, -393, -131, -655], ![858, -1183, 411, 108, 461]]]
 hmul := by decide
 f :=  ![![![![101170527288578120108144817, 699988495198497805857104068, -190684388531747520404024160, -31645037494455751986958684, -94393224669884996356470352], ![35512685055385827020422298, 4181026871784211942807320416, -1586106067639104401664, 0, 0]], ![![513846320969650, -7234723728, 0, 0, 0], ![-2620, 0, 0, 0, 0]]], ![![![-6158128836695132781579819, -42607461413551010904289429, 11606730370945726567440099, 1926195534960975076604405, 5745602542627913968002384], ![-2161614610194222566577420, -254494098589504931848427887, 96544376855177346304, 0, 0]], ![![-31277210187575, 440368969, 0, 0, 0], ![160, 0, 0, 0, 0]]]]
 g :=  ![![![![131, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-20, 8, -3, -1, -5], ![0, 0, 0, 0, 0]]], ![![![-49, 36, -3, -1, -5], ![0, 0, 0, 0, 0]], ![![14, 99, 5, 12, -3], ![122, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI131N1 : IdealMulEqCertificate O ℤ timesTableO (I131N0*I131N1) I131N2
  ![![131, 0, 0, 0, 0], ![-8, -116, -2, -12, 7]] ![![131, 0, 0, 0, 0], ![61, 1, 0, 0, 0]]
  ![![131, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI131N0
 hI2 := rfl
 M :=  ![![![17161, 0, 0, 0, 0], ![7991, 131, 0, 0, 0]], ![![-1048, -15196, -262, -1572, 917], ![-524, -7074, -262, -786, 262]]]
 hmul := by decide
 f :=  ![![![![24709479597832785, 1105453543608211, 65319857603422959, 2165410551290060, 4425208362849], ![-53062244290568018, 794885902264601, -140288518276978896, -48308525678512, 0]], ![![1801275, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![131, 0, 0, 0, 0]], ![![61, 1, 0, 0, 0]]], ![![![-8, -116, -2, -12, 7]], ![![-4, -54, -2, -6, 2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC131 : PrimesBelowPCertificate 131 ![I131N0, I131N1, I131N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI131N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp137 : Fact (Nat.Prime 137) := by decide
def I137N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0, 0, 0]] i)))

def SI137N: IdealEqSpanCertificate O ℤ timesTableO I137N
 ![![137, 0, 0, 0, 0]]
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI137N : Nat.card (O ⧸ I137N) = 48261724457 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI137N)

def MemCI137N : IdealMemCertificate O ℤ B I137N
  ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]] ![1810181, -1172309, 1121893, 1172309, 6776568] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI137N
 g := ![13213, -8557, 8189, 8557, 49464]
 hmem := by decide

def P137P : CertificateIrreducibleZModOfList' 137 5 2 7 [98, 12, 92, 117, 87, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 48, 6, 131, 71], [76, 2, 62, 87, 99], [94, 5, 79, 69, 106], [26, 81, 127, 124, 135], [0, 1]]
 g := ![![[63, 82, 53, 41, 101], [90, 76, 118, 121], [62, 28, 99, 56], [70, 45, 125, 11, 1], [46, 54, 50, 1], [], []],![[117, 10, 74, 19, 15, 89, 67, 54], [124, 13, 117, 15], [113, 57, 37, 77], [50, 62, 2, 74, 132, 0, 0, 40], [25, 31, 39, 99], [86, 6, 78, 78], [12, 68, 77, 109]],![[29, 37, 133, 36, 79, 30, 72, 129], [97, 96, 22, 11], [92, 65, 68, 123], [69, 16, 122, 70, 57, 21, 58, 128], [15, 84, 24, 68], [3, 118, 15, 130], [136, 121, 102, 74]],![[113, 113, 115, 116, 67, 10, 121, 29], [128, 99, 100, 65], [93, 42, 35, 74], [67, 116, 53, 60, 32, 43, 102, 45], [102, 73, 104, 4], [120, 49, 129, 112], [105, 65, 69, 2]],![[31, 56, 20, 33, 0, 53, 22, 87], [25, 71, 134, 25], [73, 66, 112, 44], [114, 132, 104, 53, 62, 90, 37, 65], [82, 104, 81, 105], [61, 57, 67, 88], [89, 11, 115, 4]]]
 h' := ![![[128, 48, 6, 131, 71], [49, 16, 67, 48, 52], [52, 40, 7, 33, 126], [127, 125, 76, 34, 59], [13, 47, 84, 49, 1], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]],![[76, 2, 62, 87, 99], [23, 88, 86, 78, 7], [121, 125, 87, 71, 120], [57, 68, 88, 58, 25], [121, 15, 57, 124, 4], [67, 24, 109, 86, 28], [1, 0, 128, 50, 107], [128, 48, 6, 131, 71]],![[94, 5, 79, 69, 106], [47, 26, 62, 29, 104], [10, 23, 6, 50, 55], [11, 73, 39, 6, 64], [62, 128, 66, 15, 48], [132, 105, 115, 85, 43], [120, 103, 127, 9, 104], [76, 2, 62, 87, 99]],![[26, 81, 127, 124, 135], [11, 136, 56, 52, 116], [15, 96, 79, 122, 105], [118, 4, 41, 32, 99], [66, 49, 44, 23, 78], [91, 32, 110, 24, 135], [53, 23, 4, 90, 48], [94, 5, 79, 69, 106]],![[0, 1], [76, 8, 3, 67, 132], [34, 127, 95, 135, 5], [129, 4, 30, 7, 27], [119, 35, 23, 63, 6], [49, 113, 77, 79, 67], [37, 11, 14, 125, 15], [26, 81, 127, 124, 135]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 103, 2, 51], [], [], []]
 b := ![[], [84, 25, 109, 77, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N : PrimeIdeal O 137 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I137N
  hcard := NI137N
  P := [98, 12, 92, 117, 87, 1]
  f := ofList [98, 12, 92, 117, 87, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P137P
  hneq := by decide
  hlen := by decide
  c := ![1810181, -1172309, 1121893, 1172309, 6776568]
  a := ![1, 0, 0, 1, 3]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI137N
  hpmem := by
    show  _ ∈ I137N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI137N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI137N : Ideal.IsPrime I137N := PrimeIdeal_isPrime PI137N
def PBC137 : PrimesBelowPCertificate 137 ![I137N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI137N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I137N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp139 : Fact (Nat.Prime 139) := by decide
def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0, 0, 0], ![40, 46, -3, -1, -5]] i)))

def SI139N0: IdealEqSpanCertificate O ℤ timesTableO I139N0
 ![![139, 0, 0, 0, 0], ![40, 46, -3, -1, -5]]
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![20, 32, 1, 0, 0], ![97, 124, 0, 1, 0], ![44, 58, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]], ![![40, 46, -3, -1, -5], ![-3, 38, 44, 1, 3], ![3, 40, 40, 85, 3], ![129, -40, 83, 164, 504], ![-2, -1, 1, -84, -87]]]
  hmulB := by decide
  f := ![![![-62454441, 393401754, 496008853, 12212621, 37272533], ![100084309, -1559709270, -444244, 0, 0]], ![![-118232719, 744750433, 938996299, 23119898, 70560776], ![189469927, -2952691515, -841228, 0, 0]], ![![-36195728, 227997714, 287464086, 7077909, 21601457], ![58004251, -903936240, -257516, 0, 0]], ![![-149057087, 938913864, 1183801436, 29147421, 88956630], ![238866468, -3722485950, -1060460, 0, 0]], ![![-69104254, 435289240, 548821401, 13513017, 41241124], ![110740713, -1725779250, -491640, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-20, -32, 139, 0, 0], ![-97, -124, 0, 139, 0], ![-44, -58, 0, 0, 139]], ![![3, 4, -3, -1, -5], ![-8, -12, 44, 1, 3], ![-66, -86, 40, 85, 3], ![-285, -376, 83, 164, 504], ![86, 111, 1, -84, -87]]]
  hle1 := by decide
  hle2 := by decide

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI139N0)

def MemCI139N0 : IdealMemCertificate O ℤ B I139N0
  ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![20, 32, 1, 0, 0], ![97, 124, 0, 1, 0], ![44, 58, 0, 0, 1]] ![2341, -1934, 1384, 2064, 9788] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI139N0
 g := ![-4721, -6258, 1384, 2064, 9788]
 hmem := by decide

def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [91, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 138], [0, 1]]
 g := ![![[48, 55], [77, 77], [91], [88, 136], [13], [6], [1]],![[0, 84], [121, 62], [91], [126, 3], [13], [6], [1]]]
 h' := ![![[80, 138], [82, 65], [56, 76], [54, 62], [106, 54], [90, 98], [48, 80], [0, 1]],![[0, 1], [0, 74], [20, 63], [10, 77], [117, 85], [7, 41], [54, 59], [80, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [138, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : PrimeIdeal O 139 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I139N0
  hcard := NI139N0
  P := [91, 59, 1]
  f := ofList [91, 59, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P139P0
  hneq := by decide
  hlen := by decide
  c := ![2341, -1934, 1384, 2064, 9788]
  a := ![-13, 2, -12, -16, -52]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI139N0
  hpmem := by
    show  _ ∈ I139N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI139N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := PrimeIdeal_isPrime PI139N0
def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0, 0, 0], ![-60, -38, -3, -1, -5]] i)))

def SI139N1: IdealEqSpanCertificate O ℤ timesTableO I139N1
 ![![139, 0, 0, 0, 0], ![-60, -38, -3, -1, -5]]
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![64, 122, 1, 0, 0], ![127, 27, 0, 1, 0], ![115, 68, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]], ![![-60, -38, -3, -1, -5], ![-3, -62, -40, 1, 3], ![3, -44, -60, -83, 3], ![-123, 44, -85, -188, -504], ![-2, -1, 1, 84, 65]]]
  hmulB := by decide
  f := ![![![1552409947, -25737745896, -17639532402, 494051148, 1574339112], ![6686637534, -61802203074, 2220108, 0, 0]], ![![776219832, -12869118781, -8819934701, 247030281, 787184597], ![3343382707, -30901691870, 1110054, 0, 0]], ![![1395980491, -23144267960, -15862075340, 444267804, 1415699974], ![6012854813, -55574670486, 1996379, 0, 0]], ![![1569165427, -26015539127, -17829919800, 499383549, 1591331302], ![6758807840, -62469247992, 2244066, 0, 0]], ![![1664101339, -27589502584, -18908645944, 529596698, 1687608273], ![7167721768, -66248693530, 2379828, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-64, -122, 139, 0, 0], ![-127, -27, 0, 139, 0], ![-115, -68, 0, 0, 139]], ![![6, 5, -3, -1, -5], ![15, 33, -40, 1, 3], ![101, 67, -60, -83, 3], ![627, 358, -85, -188, -504], ![-131, -49, 1, 84, 65]]]
  hle1 := by decide
  hle2 := by decide

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 19321 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI139N1)

def MemCI139N1 : IdealMemCertificate O ℤ B I139N1
  ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![64, 122, 1, 0, 0], ![127, 27, 0, 1, 0], ![115, 68, 0, 0, 1]] ![6824529, -3480637, 4130089, 2622149, 21768424] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI139N1
 g := ![-22258150, -14808650, 4130089, 2622149, 21768424]
 hmem := by decide

def P139P1 : CertificateIrreducibleZModOfList' 139 2 2 7 [71, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 138], [0, 1]]
 g := ![![[11, 47], [31, 44], [112], [14, 16], [5], [29], [1]],![[0, 92], [0, 95], [112], [28, 123], [5], [29], [1]]]
 h' := ![![[53, 138], [23, 73], [134, 105], [118, 23], [0, 4], [63, 127], [68, 53], [0, 1]],![[0, 1], [0, 66], [0, 34], [86, 116], [73, 135], [122, 12], [97, 86], [53, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [99, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N1 : PrimeIdeal O 139 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I139N1
  hcard := NI139N1
  P := [71, 86, 1]
  f := ofList [71, 86, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P139P1
  hneq := by decide
  hlen := by decide
  c := ![6824529, -3480637, 4130089, 2622149, 21768424]
  a := ![528, -176, 436, 529, 2113]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI139N1
  hpmem := by
    show  _ ∈ I139N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI139N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := PrimeIdeal_isPrime PI139N1
def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0, 0, 0], ![-15, 1, 0, 0, 0]] i)))

def SI139N2: IdealEqSpanCertificate O ℤ timesTableO I139N2
 ![![139, 0, 0, 0, 0], ![-15, 1, 0, 0, 0]]
 ![![139, 0, 0, 0, 0], ![124, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![127, 0, 0, 1, 0], ![94, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]], ![![-15, 1, 0, 0, 0], ![0, -15, 1, 0, 0], ![0, 1, -15, 2, 0], ![3, -1, 2, -12, 12], ![0, 0, 0, -2, -18]]]
  hmulB := by decide
  f := ![![![104056546, -33100568, 401115021, -53587002, 102060], ![964020878, 5428506, 3717203469, -1182195, 0]], ![![93779371, -29831384, 361498868, -48294478, 91980], ![868809076, 4892383, 3350073611, -1065435, 0]], ![![39824102, -12668107, 153513083, -20508596, 39060], ![368946186, 2077634, 1422632752, -452445, 0]], ![![95064013, -30240032, 366450764, -48956027, 93240], ![880710506, 4959319, 3395963697, -1080030, 0]], ![![70369186, -22384556, 271257640, -36238692, 69019], ![651927890, 3671090, 2513792274, -799470, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-124, 139, 0, 0, 0], ![-53, 0, 139, 0, 0], ![-127, 0, 0, 139, 0], ![-94, 0, 0, 0, 139]], ![![-1, 1, 0, 0, 0], ![13, -15, 1, 0, 0], ![3, 1, -15, 2, 0], ![3, -1, 2, -12, 12], ![14, 0, 0, -2, -18]]]
  hle1 := by decide
  hle2 := by decide

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulEqCertificate O ℤ timesTableO (I139N0) I139N1
  ![![139, 0, 0, 0, 0], ![40, 46, -3, -1, -5]] ![![139, 0, 0, 0, 0], ![-60, -38, -3, -1, -5]]
  ![![139, 0, 0, 0, 0], ![58, -214, 80, 12, 147]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![19321, 0, 0, 0, 0], ![-8340, -5282, -417, -139, -695]], ![![5560, 6394, -417, -139, -695], ![-2414, -4279, -1700, 23, 108]]]
 hmul := by decide
 f :=  ![![![![87739473618101177901972589191, -1454652073669691420719715122635, -996955307501742688124564413966, 27922899362055744052723695839, 88978873870957870300454782056], ![377916971483097743036327445738, -3492951677792102985846409057136, 125474241582277926265908782, 0, 0]], ![![-781373438106166620, -3892958968, 0, 0, 0], ![15151, 0, 0, 0, 0]]], ![![![36610622034457089498332252538, -606975572848357382049574737020, -415994676547298666562332995855, 11651251967842948697194613703, 37127780530349703710122723528], ![157691570656060861010238098036, -1457486902837848754279095510452, 52356024537184259047268279, 0, 0]], ![![-326039881829965875, -1624395993, 0, 0, 0], ![6322, 0, 0, 0, 0]]]]
 g :=  ![![![![81, 214, -80, -12, -147], ![139, 0, 0, 0, 0]], ![![-118, 176, -83, -13, -152], ![139, 0, 0, 0, 0]]], ![![![40, 46, -3, -1, -5], ![0, 0, 0, 0, 0]], ![![-52, 97, -60, -7, -87], ![83, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI139N1 : IdealMulEqCertificate O ℤ timesTableO (I139N0*I139N1) I139N2
  ![![139, 0, 0, 0, 0], ![58, -214, 80, 12, 147]] ![![139, 0, 0, 0, 0], ![-15, 1, 0, 0, 0]]
  ![![139, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI139N0
 hI2 := rfl
 M :=  ![![![19321, 0, 0, 0, 0], ![-2085, 139, 0, 0, 0]], ![![8062, -29746, 11120, 1668, 20433], ![-834, 3336, -1390, -278, -2502]]]
 hmul := by decide
 f :=  ![![![![-935046955308389088992, 64388085129925234842, -31450169123705211341, 4193811280548714858, -54286659338049], ![-8664768326760314297952, -419415573061240852, -291466111075150456263, 628820495509653, 0]], ![![-2028075, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![139, 0, 0, 0, 0]], ![![-15, 1, 0, 0, 0]]], ![![![58, -214, 80, 12, 147]], ![![-6, 24, -10, -2, -18]]]]
 hle1 := by decide
 hle2 := by decide

def PBC139 : PrimesBelowPCertificate 139 ![I139N0, I139N1, I139N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI139N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp149 : Fact (Nat.Prime 149) := by decide
def I149N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0, 0]] i)))

def SI149N: IdealEqSpanCertificate O ℤ timesTableO I149N
 ![![149, 0, 0, 0, 0]]
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI149N : Nat.card (O ⧸ I149N) = 73439775749 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI149N)

def MemCI149N : IdealMemCertificate O ℤ B I149N
  ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]] ![-84706649, 48149499, -50210169, -35585968, -281404380] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI149N
 g := ![-568501, 323151, -336981, -238832, -1888620]
 hmem := by decide

def P149P : CertificateIrreducibleZModOfList' 149 5 2 7 [121, 17, 68, 70, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 111, 131, 66, 107], [70, 10, 92, 4, 19], [46, 40, 108, 129, 90], [122, 136, 116, 99, 82], [0, 1]]
 g := ![![[2, 91, 119, 40, 129], [94, 80, 92, 6], [79, 26, 58, 80, 53], [90, 139, 78, 37], [88, 130, 95, 145, 1], [], []],![[125, 15, 23, 57, 115, 148, 33, 140], [71, 39, 87, 120], [11, 15, 136, 128, 20, 2, 136, 127], [72, 33, 95, 119], [130, 16, 61, 80, 49, 127, 124, 19], [46, 145, 82, 82], [36, 136, 65, 125]],![[70, 107, 104, 50, 92, 43, 20, 127], [41, 132, 87, 16], [53, 99, 138, 68, 11, 47, 51, 133], [123, 146, 32, 17], [101, 91, 142, 58, 95, 117, 44, 112], [50, 26, 3, 103], [13, 98, 49, 63]],![[147, 0, 84, 16, 35, 88, 59, 122], [86, 115, 30, 26], [87, 115, 49, 104, 91, 23, 140, 32], [113, 20, 11, 36], [3, 85, 131, 87, 69, 47, 48, 147], [62, 61, 95, 119], [78, 34, 58, 54]],![[18, 129, 31, 106, 127, 110, 117, 85], [7, 7, 55, 69], [117, 7, 68, 9, 4, 37, 3, 133], [90, 41, 91, 35], [104, 47, 37, 99, 41, 88, 97, 104], [112, 131, 32, 80], [60, 105, 68, 19]]]
 h' := ![![[56, 111, 131, 66, 107], [32, 102, 5, 24, 24], [126, 83, 76, 8, 119], [129, 20, 112, 16, 65], [80, 58, 128, 110, 127], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]],![[70, 10, 92, 4, 19], [42, 41, 10, 56, 29], [132, 48, 131, 46, 92], [126, 15, 2, 33, 6], [14, 123, 145, 1, 62], [135, 58, 113, 8, 88], [121, 132, 64, 132, 23], [56, 111, 131, 66, 107]],![[46, 40, 108, 129, 90], [37, 84, 64, 53, 17], [140, 104, 122, 112, 4], [10, 92, 60, 40, 93], [80, 30, 29, 74, 49], [76, 61, 42, 52, 10], [49, 49, 31, 78, 38], [70, 10, 92, 4, 19]],![[122, 136, 116, 99, 82], [73, 123, 11, 136, 36], [7, 128, 9, 137, 131], [26, 13, 38, 4, 38], [17, 93, 92, 74, 143], [91, 74, 51, 94, 29], [128, 28, 126, 1, 62], [46, 40, 108, 129, 90]],![[0, 1], [77, 97, 59, 29, 43], [103, 84, 109, 144, 101], [75, 9, 86, 56, 96], [104, 143, 53, 39, 66], [36, 105, 92, 144, 21], [25, 89, 76, 87, 26], [122, 136, 116, 99, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 97, 6, 49], [], [], []]
 b := ![[], [10, 17, 21, 145, 26], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N : PrimeIdeal O 149 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I149N
  hcard := NI149N
  P := [121, 17, 68, 70, 4, 1]
  f := ofList [121, 17, 68, 70, 4, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P149P
  hneq := by decide
  hlen := by decide
  c := ![-84706649, 48149499, -50210169, -35585968, -281404380]
  a := ![3, 1, 4, 6, 12]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI149N
  hpmem := by
    show  _ ∈ I149N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI149N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI149N : Ideal.IsPrime I149N := PrimeIdeal_isPrime PI149N
def PBC149 : PrimesBelowPCertificate 149 ![I149N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI149N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I149N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp151 : Fact (Nat.Prime 151) := by decide
def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 3, -1, -4, -10]] i)))

def SI151N0: IdealEqSpanCertificate O ℤ timesTableO I151N0
 ![![-3, 3, -1, -4, -10]]
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![83, 39, 1, 0, 0], ![118, 112, 0, 1, 0], ![126, 102, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![-3, 3, -1, -4, -10], ![-12, 0, -5, 6, -18], ![18, -23, 12, 44, 126], ![72, -7, 35, -51, 84], ![-34, 18, -20, -14, -113]]]
  hmulB := by decide
  f := ![![![-91, -51, -33, -18, -34]], ![![-54, -106, -87, -52, -114]], ![![-65, -56, -42, -24, -50]], ![![-112, -119, -91, -53, -112]], ![![-112, -114, -86, -50, -105]]]
  g := ![![![12, 10, -1, -4, -10], ![13, 9, -5, 6, -18], ![-146, -121, 12, 44, 126], ![-49, -28, 35, -51, 84], ![116, 92, -20, -14, -113]]]
  hle1 := by decide
  hle2 := by decide

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI151N0)

def MemCI151N0 : IdealMemCertificate O ℤ B I151N0
  ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![83, 39, 1, 0, 0], ![118, 112, 0, 1, 0], ![126, 102, 0, 0, 1]] ![195, 142, 126, -114, -194] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI151N0
 g := ![183, 184, 126, -114, -194]
 hmem := by decide

def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [55, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [124, 150], [0, 1]]
 g := ![![[146, 11], [44, 32], [101, 20], [85], [52, 39], [125], [1]],![[0, 140], [86, 119], [14, 131], [85], [56, 112], [125], [1]]]
 h' := ![![[124, 150], [147, 39], [32, 118], [87, 41], [9, 113], [76, 48], [96, 124], [0, 1]],![[0, 1], [0, 112], [17, 33], [37, 110], [129, 38], [139, 103], [70, 27], [124, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [13, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : PrimeIdeal O 151 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I151N0
  hcard := NI151N0
  P := [55, 27, 1]
  f := ofList [55, 27, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P151P0
  hneq := by decide
  hlen := by decide
  c := ![195, 142, 126, -114, -194]
  a := ![1, 2, 2, 2, -2]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI151N0
  hpmem := by
    show  _ ∈ I151N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI151N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := PrimeIdeal_isPrime PI151N0
def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 11, -11, -4, -19]] i)))

def SI151N1: IdealEqSpanCertificate O ℤ timesTableO I151N1
 ![![9, 11, -11, -4, -19]]
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![68, 9, 1, 0, 0], ![147, 145, 0, 1, 0], ![112, 67, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![9, 11, -11, -4, -19], ![-12, 2, 3, 4, 9], ![12, -13, 10, 0, 21], ![6, 10, -8, -13, -36], ![-10, -2, 2, 6, 7]]]
  hmulB := by decide
  f := ![![![29, 13, 31, 14, 41]], ![![42, 46, 41, 22, 45]], ![![16, 9, 17, 8, 22]], ![![69, 57, 70, 35, 84]], ![![40, 30, 41, 20, 50]]]
  g := ![![![23, 13, -11, -4, -19], ![-12, -8, 3, 4, 9], ![-20, -10, 10, 0, 21], ![43, 29, -8, -13, -36], ![-12, -9, 2, 6, 7]]]
  hle1 := by decide
  hle2 := by decide

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI151N1)

def MemCI151N1 : IdealMemCertificate O ℤ B I151N1
  ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![68, 9, 1, 0, 0], ![147, 145, 0, 1, 0], ![112, 67, 0, 0, 1]] ![26807, -13991, 15683, 7968, 82167] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI151N1
 g := ![-75587, -45137, 15683, 7968, 82167]
 hmem := by decide

def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [79, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 150], [0, 1]]
 g := ![![[39, 136], [137, 62], [47, 37], [85], [11, 47], [97], [1]],![[48, 15], [130, 89], [55, 114], [85], [13, 104], [97], [1]]]
 h' := ![![[90, 150], [49, 102], [62, 45], [90, 43], [37, 38], [88, 97], [72, 90], [0, 1]],![[0, 1], [18, 49], [35, 106], [34, 108], [135, 113], [60, 54], [18, 61], [90, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [12, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : PrimeIdeal O 151 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I151N1
  hcard := NI151N1
  P := [79, 61, 1]
  f := ofList [79, 61, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P151P1
  hneq := by decide
  hlen := by decide
  c := ![26807, -13991, 15683, 7968, 82167]
  a := ![-33, 11, -24, -32, -131]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI151N1
  hpmem := by
    show  _ ∈ I151N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI151N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := PrimeIdeal_isPrime PI151N1
def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -15, 9, 2, 14]] i)))

def SI151N2: IdealEqSpanCertificate O ℤ timesTableO I151N2
 ![![5, -15, 9, 2, 14]]
 ![![151, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![5, -15, 9, 2, 14], ![6, 12, -11, -4, -18], ![-12, -1, 4, 2, 6], ![0, -11, 7, 3, 12], ![2, 8, -6, -2, -9]]]
  hmulB := by decide
  f := ![![![-39, -33, -55, -20, -58]], ![![-27, -23, -38, -14, -40]], ![![-30, -25, -42, -16, -46]], ![![-39, -32, -54, -19, -58]], ![![-4, -4, -6, -2, -5]]]
  g := ![![![0, -15, 9, 2, 14], ![6, 12, -11, -4, -18], ![-5, -1, 4, 2, 6], ![-2, -11, 7, 3, 12], ![2, 8, -6, -2, -9]]]
  hle1 := by decide
  hle2 := by decide

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulEqCertificate O ℤ timesTableO (I151N0) I151N1
  ![![-3, 3, -1, -4, -10]] ![![9, 11, -11, -4, -19]]
  ![![1, -34, 44, 16, 137]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![1, -34, 44, 16, 137]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI151N1 : IdealMulEqCertificate O ℤ timesTableO (I151N0*I151N1) I151N2
  ![![1, -34, 44, 16, 137]] ![![5, -15, 9, 2, 14]]
  ![![151, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI151N0
 hI2 := rfl
 M :=  ![![![-453, 453, -151, 0, -151]]]
 hmul := by decide
 f :=  ![![![![83, 71, 95, 50, 125]]]]
 g :=  ![![![![-3, 3, -1, 0, -1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC151 : PrimesBelowPCertificate 151 ![I151N0, I151N1, I151N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI151N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl




-- I'm using native decide for this one, or increase rec depth

set_option maxRecDepth 700
lemma primes_below_156 : Set.range ![151, 149, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2] = ↑(Nat.primesBelow 156) := by
  have : Nat.primesBelow 156 =  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151} := by decide
  rw [this]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
    Set.union_empty, Set.union_singleton, Set.union_insert, Finset.coe_insert, Finset.coe_singleton]



set_option maxHeartbeats 700000

def PB153 : PrimesBelowBoundCertificate O 156 where
  m := 36
  g := ![3, 1, 3, 1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 1, 3, 3, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 5, 3, 5]
  P := ![151, 149, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]
  hP := primes_below_156
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I149N]
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I137N]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I113N]
    · exact ![I109N]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I101N]
    · exact ![I97N]
    · exact ![I89N]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I73N]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I61N]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I53N]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I41N]
    · exact ![I37N]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I29N]
    · exact ![I23N0, I23N1, I23N2]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I17N]
    · exact ![I13N]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I5N, I5N, I5N, I5N, I5N]
    · exact ![I3N0, I3N1, I3N2]
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC151
    · exact PBC149
    · exact PBC139
    · exact PBC137
    · exact PBC131
    · exact PBC127
    · exact PBC113
    · exact PBC109
    · exact PBC107
    · exact PBC103
    · exact PBC101
    · exact PBC97
    · exact PBC89
    · exact PBC83
    · exact PBC79
    · exact PBC73
    · exact PBC71
    · exact PBC67
    · exact PBC61
    · exact PBC59
    · exact PBC53
    · exact PBC47
    · exact PBC43
    · exact PBC41
    · exact PBC37
    · exact PBC31
    · exact PBC29
    · exact PBC23
    · exact PBC19
    · exact PBC17
    · exact PBC13
    · exact PBC11
    · exact PBC7
    · exact PBC5
    · exact PBC3
    · exact PBC2
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![22801, 22801, 151]
    · exact ![73439775749]
    · exact ![19321, 19321, 139]
    · exact ![48261724457]
    · exact ![17161, 17161, 131]
    · exact ![16129, 16129, 127]
    · exact ![18424351793]
    · exact ![15386239549]
    · exact ![11449, 11449, 107]
    · exact ![10609, 10609, 103]
    · exact ![10510100501]
    · exact ![8587340257]
    · exact ![5584059449]
    · exact ![6889, 6889, 83]
    · exact ![6241, 6241, 79]
    · exact ![2073071593]
    · exact ![5041, 5041, 71]
    · exact ![4489, 4489, 67]
    · exact ![844596301]
    · exact ![3481, 3481, 59]
    · exact ![418195493]
    · exact ![2209, 2209, 47]
    · exact ![1849, 1849, 43]
    · exact ![115856201]
    · exact ![69343957]
    · exact ![961, 961, 31]
    · exact ![20511149]
    · exact ![529, 529, 23]
    · exact ![361, 361, 19]
    · exact ![1419857]
    · exact ![371293]
    · exact ![121, 121, 11]
    · exact ![49, 49, 7]
    · exact ![5, 5, 5, 5, 5]
    · exact ![9, 9, 3]
    · exact ![2, 2, 2, 2, 2]
  hN := fun i => by
     cases i
     rename_i i h
     interval_cases i
     · dsimp ; intro j
       fin_cases j
       exact NI151N0
       exact NI151N1
       exact NI151N2
     · dsimp ; intro j
       fin_cases j
       exact NI149N
     · dsimp ; intro j
       fin_cases j
       exact NI139N0
       exact NI139N1
       exact NI139N2
     · dsimp ; intro j
       fin_cases j
       exact NI137N
     · dsimp ; intro j
       fin_cases j
       exact NI131N0
       exact NI131N1
       exact NI131N2
     · dsimp ; intro j
       fin_cases j
       exact NI127N0
       exact NI127N1
       exact NI127N2
     · dsimp ; intro j
       fin_cases j
       exact NI113N
     · dsimp ; intro j
       fin_cases j
       exact NI109N
     · dsimp ; intro j
       fin_cases j
       exact NI107N0
       exact NI107N1
       exact NI107N2
     · dsimp ; intro j
       fin_cases j
       exact NI103N0
       exact NI103N1
       exact NI103N2
     · dsimp ; intro j
       fin_cases j
       exact NI101N
     · dsimp ; intro j
       fin_cases j
       exact NI97N
     · dsimp ; intro j
       fin_cases j
       exact NI89N
     · dsimp ; intro j
       fin_cases j
       exact NI83N0
       exact NI83N1
       exact NI83N2
     · dsimp ; intro j
       fin_cases j
       exact NI79N0
       exact NI79N1
       exact NI79N2
     · dsimp ; intro j
       fin_cases j
       exact NI73N
     · dsimp ; intro j
       fin_cases j
       exact NI71N0
       exact NI71N1
       exact NI71N2
     · dsimp ; intro j
       fin_cases j
       exact NI67N0
       exact NI67N1
       exact NI67N2
     · dsimp ; intro j
       fin_cases j
       exact NI61N
     · dsimp ; intro j
       fin_cases j
       exact NI59N0
       exact NI59N1
       exact NI59N2
     · dsimp ; intro j
       fin_cases j
       exact NI53N
     · dsimp ; intro j
       fin_cases j
       exact NI47N0
       exact NI47N1
       exact NI47N2
     · dsimp ; intro j
       fin_cases j
       exact NI43N0
       exact NI43N1
       exact NI43N2
     · dsimp ; intro j
       fin_cases j
       exact NI41N
     · dsimp ; intro j
       fin_cases j
       exact NI37N
     · dsimp ; intro j
       fin_cases j
       exact NI31N0
       exact NI31N1
       exact NI31N2
     · dsimp ; intro j
       fin_cases j
       exact NI29N
     · dsimp ; intro j
       fin_cases j
       exact NI23N0
       exact NI23N1
       exact NI23N2
     · dsimp ; intro j
       fin_cases j
       exact NI19N0
       exact NI19N1
       exact NI19N2
     · dsimp ; intro j
       fin_cases j
       exact NI17N
     · dsimp ; intro j
       fin_cases j
       exact NI13N
     · dsimp ; intro j
       fin_cases j
       exact NI11N0
       exact NI11N1
       exact NI11N2
     · dsimp ; intro j
       fin_cases j
       exact NI7N0
       exact NI7N1
       exact NI7N2
     · dsimp ; intro j
       fin_cases j
       exact NI5N
       exact NI5N
       exact NI5N
       exact NI5N
       exact NI5N
     · dsimp ; intro j
       fin_cases j
       exact NI3N0
       exact NI3N1
       exact NI3N2
     · dsimp ; intro j
       fin_cases j
       exact NI2N0
       exact NI2N1
       exact NI2N1
       exact NI2N2
       exact NI2N2
  Il := ![[I151N2], [], [I139N2], [], [I131N2], [I127N2], [], [], [I107N2], [I103N2], [], [], [], [I83N2], [I79N2], [], [I71N2], [I67N2], [], [I59N2], [], [I47N2], [I43N2], [], [], [I31N2], [], [I23N2], [I19N2], [], [], [I11N0, I11N1, I11N2], [I7N0, I7N1, I7N2], [I5N, I5N, I5N, I5N, I5N], [I3N0, I3N1, I3N2], [I2N0, I2N1, I2N1, I2N2, I2N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl


/- def PB153I0 : PrimesBelowBoundCertificateInterval O 1 61 156 where
  m := 18
  g := ![5, 3, 5, 3, 3, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 1, 3, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := sorry
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N2]
    · exact ![I5N, I5N, I5N, I5N, I5N]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N]
    · exact ![I17N]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1, I23N2]
    · exact ![I29N]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N]
    · exact ![I41N]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![9, 9, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![49, 49, 7]
    · exact ![121, 121, 11]
    · exact ![371293]
    · exact ![1419857]
    · exact ![361, 361, 19]
    · exact ![529, 529, 23]
    · exact ![20511149]
    · exact ![961, 961, 31]
    · exact ![69343957]
    · exact ![115856201]
    · exact ![1849, 1849, 43]
    · exact ![2209, 2209, 47]
    · exact ![418195493]
    · exact ![3481, 3481, 59]
    · exact ![844596301]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N2
    · dsimp ; intro j
      fin_cases j
      exact NI5N
      exact NI5N
      exact NI5N
      exact NI5N
      exact NI5N
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N
    · dsimp ; intro j
      fin_cases j
      exact NI17N
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
    · dsimp ; intro j
      fin_cases j
      exact NI29N
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N
    · dsimp ; intro j
      fin_cases j
      exact NI41N
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N2], [I5N, I5N, I5N, I5N, I5N], [I7N0, I7N1, I7N2], [I11N0, I11N1, I11N2], [], [], [I19N2], [I23N2], [], [I31N2], [], [], [I43N2], [I47N2], [], [I59N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl




def PB153I1 : PrimesBelowBoundCertificateInterval O 61 155 156 where
  m := 18
  g := ![3, 3, 1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 1, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := sorry
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N]
    · exact ![I97N]
    · exact ![I101N]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N]
    · exact ![I113N]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N]
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N]
    · exact ![I151N0, I151N1, I151N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
    · exact PBC139
    · exact PBC149
    · exact PBC151
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4489, 4489, 67]
    · exact ![5041, 5041, 71]
    · exact ![2073071593]
    · exact ![6241, 6241, 79]
    · exact ![6889, 6889, 83]
    · exact ![5584059449]
    · exact ![8587340257]
    · exact ![10510100501]
    · exact ![10609, 10609, 103]
    · exact ![11449, 11449, 107]
    · exact ![15386239549]
    · exact ![18424351793]
    · exact ![16129, 16129, 127]
    · exact ![17161, 17161, 131]
    · exact ![48261724457]
    · exact ![19321, 19321, 139]
    · exact ![73439775749]
    · exact ![22801, 22801, 151]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N
    · dsimp ; intro j
      fin_cases j
      exact NI97N
    · dsimp ; intro j
      fin_cases j
      exact NI101N
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N
    · dsimp ; intro j
      fin_cases j
      exact NI113N
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  Il := ![[I67N2], [I71N2], [], [I79N2], [I83N2], [], [], [], [I103N2], [I107N2], [], [], [I127N2], [I131N2], [], [I139N2], [], [I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl


def PB156 : PrimesBelowBoundCertificate O 156 := by
  refine primesBelowBoundCertificate_of_Interval O ![1, 61, 155] 155 rfl rfl ?_ ?_
  · decide
  · intro i
    match i with
    | 0 => exact PB153I0
    | 1 => exact PB153I1 -/
