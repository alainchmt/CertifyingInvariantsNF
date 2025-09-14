import IdealArithmetic.Examples.SmallDisc.PrimesBelowSmallDisc

open Classical Polynomial

noncomputable section

--- Primes above 29


instance hp29 : Fact $ Nat.Prime 29 := by decide

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -2, 1, 2, -1]] i)))

def SI29N0: IdealEqSpanCertificate O ℤ timesTableO I29N0
 ![![-13, -2, 1, 2, -1]]
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![24, 3, 9, 1, 0], ![3, 8, 17, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![-13, -2, 1, 2, -1], ![-4, -7, -6, 2, 2], ![4, -10, -8, -6, 1], ![4, -1, -4, -9, -4], ![-12, 10, -1, -14, -8]]]
  hmulB := by decide
  f := ![![![-1, 0, -1, 2, -1]], ![![-4, 3, -2, -2, 2]], ![![4, -8, 4, -2, -1]], ![![0, -2, 0, 1, -1]], ![![1, -4, 2, -2, 0]]]
  g := ![![![-2, 0, 0, 2, -1], ![-2, -1, -2, 2, 2], ![5, 0, 1, -6, 1], ![8, 2, 5, -9, -4], ![12, 4, 9, -14, -8]]]
  hle1 := by decide
  hle2 := by decide

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI29N0)

def MemCI29N0 : IdealMemCertificate O ℤ B I29N0
  ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![24, 3, 9, 1, 0], ![3, 8, 17, 0, 1]] ![-97, 371, -229, 180, -322] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI29N0
 g := ![-119, 83, 125, 180, -322]
 hmem := by decide

def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [28, 3, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 22, 26], [18, 6, 3], [0, 1]]
 g := ![![[13, 7, 6], [4, 16], [22, 25, 4], [1]],![[22, 27], [23, 23], [11, 21, 15, 11], [21, 27, 18, 2]],![[26, 17, 11, 18], [11, 25], [11, 16, 28, 21], [4, 1, 13, 27]]]
 h' := ![![[13, 22, 26], [24, 13, 21], [22, 18, 25], [1, 26, 2], [0, 1]],![[18, 6, 3], [14, 7], [7, 10, 9], [14, 11, 21], [13, 22, 26]],![[0, 1], [18, 9, 8], [23, 1, 24], [7, 21, 6], [18, 6, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 13], []]
 b := ![[], [28, 17, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : PrimeIdeal O 29 where
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I29N0
  hcard := NI29N0
  P := [28, 3, 27, 1]
  f := ofList [28, 3, 27, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P29P0
  hneq := by decide
  hlen := by decide
  c := ![-97, 371, -229, 180, -322]
  a := ![1, -1, 1, 0, 2]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI29N0
  hpmem := by
    show  _ ∈ I29N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI29N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := PrimeIdeal_isPrime PI29N0
def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] i)))

def SI29N1: IdealEqSpanCertificate O ℤ timesTableO I29N1
 ![![29, 0, 0, 0, 0], ![3, 1, 0, 0, 0]]
 ![![29, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![3, 1, 0, 0, 0], ![0, 3, 2, 0, 0], ![0, 1, 3, 2, 0], ![0, 0, -1, 3, 1], ![4, -5, 0, 0, 3]]]
  hmulB := by decide
  f := ![![![-359, -1944, -5766, -3306, 154], ![3480, -580, 54636, -4466, 0]], ![![-57, -289, -846, -486, 22], ![552, -58, 8004, -638, 0]], ![![-130, -696, -2058, -1179, 55], ![1260, -188, 19488, -1595, 0]], ![![-333, -1806, -5355, -3070, 143], ![3228, -530, 50736, -4147, 0]], ![![-202, -1075, -3182, -1824, 85], ![1958, -309, 30144, -2464, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 29, 0, 0, 0], ![-10, 0, 29, 0, 0], ![-27, 0, 0, 29, 0], ![-16, 0, 0, 0, 29]], ![![0, 1, 0, 0, 0], ![-1, 3, 2, 0, 0], ![-3, 1, 3, 2, 0], ![-3, 0, -1, 3, 1], ![-1, -5, 0, 0, 3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![8, 1, 0, 0, 0]] i)))

def SI29N2: IdealEqSpanCertificate O ℤ timesTableO I29N2
 ![![29, 0, 0, 0, 0], ![8, 1, 0, 0, 0]]
 ![![29, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![8, 1, 0, 0, 0], ![0, 8, 2, 0, 0], ![0, 1, 8, 2, 0], ![0, 0, -1, 8, 1], ![4, -5, 0, 0, 8]]]
  hmulB := by decide
  f := ![![![-8487, -5447, -44389, -9628, 187], ![30769, -4263, 161298, -5423, 0]], ![![-3064, -1965, -15948, -3452, 68], ![11108, -1508, 57942, -1972, 0]], ![![-7694, -4943, -40295, -8738, 170], ![27894, -3871, 146421, -4930, 0]], ![![-2328, -1489, -12119, -2629, 51], ![8440, -1162, 44037, -1479, 0]], ![![-5852, -3760, -30614, -6640, 129], ![21216, -2927, 111240, -3740, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-8, 29, 0, 0, 0], ![-26, 0, 29, 0, 0], ![-8, 0, 0, 29, 0], ![-20, 0, 0, 0, 29]], ![![0, 1, 0, 0, 0], ![-4, 8, 2, 0, 0], ![-8, 1, 8, 2, 0], ![-2, 0, -1, 8, 1], ![-4, -5, 0, 0, 8]]]
  hle1 := by decide
  hle2 := by decide

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulEqCertificate O ℤ timesTableO (I29N0) I29N1
  ![![-13, -2, 1, 2, -1]] ![![29, 0, 0, 0, 0], ![3, 1, 0, 0, 0]]
  ![![29, 0, 0, 0, 0], ![14, -16, 3, -8, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-377, -58, 29, 58, -29], ![-43, -13, -3, 8, -1]]]
 hmul := by decide
 f :=  ![![![![5068, -1436499, -955877, 2310, -49], ![-48991, 13914362, -35624, 1420, 0]]], ![![![2584, -732571, -487468, 1178, -25], ![-24978, 7095900, -18167, 724, 0]]]]
 g :=  ![![![![-13, -2, 1, 2, -1], ![0, 0, 0, 0, 0]], ![![-15, 15, -3, 8, -1], ![28, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI29N1 : IdealMulEqCertificate O ℤ timesTableO (I29N0*I29N1) I29N2
  ![![29, 0, 0, 0, 0], ![14, -16, 3, -8, 1]] ![![29, 0, 0, 0, 0], ![8, 1, 0, 0, 0]]
  ![![29, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI29N0
 hI2 := rfl
 M :=  ![![![841, 0, 0, 0, 0], ![232, 29, 0, 0, 0]], ![![406, -464, 87, -232, 29], ![116, -116, 0, -58, 0]]]
 hmul := by decide
 f :=  ![![![![-1939741507, -1238274469, -10034830511, -2512966420, 1504171], ![7031562627, -966762302, 36612498462, -43621151, 0]], ![![192, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![29, 0, 0, 0, 0]], ![![8, 1, 0, 0, 0]]], ![![![14, -16, 3, -8, 1]], ![![4, -4, 0, -2, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC29 : PrimesBelowPCertificate 29 ![I29N0, I29N1, I29N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI29N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl

--- Primes above 31

instance hp31 : Fact $ Nat.Prime 31 := by decide

def I31N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N: IdealEqSpanCertificate O ℤ timesTableO I31N
 ![![31, 0, 0, 0, 0]]
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI31N : Nat.card (O ⧸ I31N) = 28629151 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI31N)

def MemCI31N : IdealMemCertificate O ℤ B I31N
  ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] ![5177, 8494, -3627, -3875, 1178] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI31N
 g := ![167, 274, -117, -125, 38]
 hmem := by decide

def P31P : CertificateIrreducibleZModOfList' 31 5 2 4 [27, 11, 19, 18, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 8, 16, 29, 1], [6, 25, 0, 25, 14], [0, 11, 18, 30, 7], [3, 17, 28, 9, 9], [0, 1]]
 g := ![![[13, 26, 28, 17, 7], [1, 20, 28, 27, 8], [14, 30, 1], []],![[4, 1, 17, 29, 27, 24, 16, 9], [2, 23, 16, 6, 2, 13, 5, 7], [21, 11, 6, 3, 19, 14, 14, 5], [20, 12, 3, 6, 6, 18, 24, 1]],![[10, 20, 19, 25, 12, 29, 18, 20], [29, 0, 19, 12, 25, 6, 26, 25], [0, 12, 5, 10, 12, 29, 16, 14], [19, 14, 13, 27, 13, 25, 21, 16]],![[24, 26, 30, 9, 29, 29, 9, 20], [2, 2, 19, 29, 23, 20, 24, 14], [9, 10, 24, 29, 15, 4, 26, 28], [18, 29, 14, 12, 11, 21, 6, 2]],![[28, 15, 12, 19, 27, 1, 19, 18], [20, 20, 26, 25, 9, 18], [21, 21, 21, 24, 18, 29, 1, 19], [15, 1, 8, 20, 20, 22, 1, 16]]]
 h' := ![![[21, 8, 16, 29, 1], [4, 12, 2, 5, 21], [25, 28, 28, 4, 16], [0, 0, 0, 1], [0, 1]],![[6, 25, 0, 25, 14], [1, 8, 13, 2, 3], [14, 18, 30, 8, 21], [10, 27, 24, 5, 6], [21, 8, 16, 29, 1]],![[0, 11, 18, 30, 7], [13, 1, 6, 10, 20], [22, 0, 1, 3, 2], [13, 5, 30, 12, 30], [6, 25, 0, 25, 14]],![[3, 17, 28, 9, 9], [8, 13, 28, 1, 26], [5, 18, 5, 24, 23], [10, 11, 15, 9, 29], [0, 11, 18, 30, 7]],![[0, 1], [2, 28, 13, 13, 23], [6, 29, 29, 23], [25, 19, 24, 4, 28], [3, 17, 28, 9, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 8, 7, 27], [], [], []]
 b := ![[], [26, 6, 3, 5, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N : PrimeIdeal O 31 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I31N
  hcard := NI31N
  P := [27, 11, 19, 18, 1, 1]
  f := ofList [27, 11, 19, 18, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P31P
  hneq := by decide
  hlen := by decide
  c := ![5177, 8494, -3627, -3875, 1178]
  a := ![6, -1, 1, -1, 0]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI31N
  hpmem := by
    show  _ ∈ I31N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI31N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI31N : Ideal.IsPrime I31N := PrimeIdeal_isPrime PI31N
def PBC31 : PrimesBelowPCertificate 31 ![I31N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI31N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I31N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl

--- Primes above 37

instance hp37 : Fact $ Nat.Prime 37 := by decide


def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -1, 0, -2, -2]] i)))

def SI37N0: IdealEqSpanCertificate O ℤ timesTableO I37N0
 ![![-13, -1, 0, -2, -2]]
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![26, 12, 1, 0, 0], ![21, 36, 0, 1, 0], ![4, 20, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![-13, -1, 0, -2, -2], ![-8, -3, 0, 0, -2], ![-4, 1, -3, 0, 0], ![4, -2, 1, -3, 1], ![0, 1, -4, 2, -3]]]
  hmulB := by decide
  f := ![![![-1, -1, -2, 2, 2]], ![![8, -13, -4, -4, 2]], ![![2, -5, -3, 0, 2]], ![![7, -13, -5, -3, 3]], ![![4, -7, -2, -2, 1]]]
  g := ![![![1, 3, 0, -2, -2], ![0, 1, 0, 0, -2], ![2, 1, -3, 0, 0], ![1, 2, 1, -3, 1], ![2, 1, -4, 2, -3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI37N0)

def MemCI37N0 : IdealMemCertificate O ℤ B I37N0
  ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![26, 12, 1, 0, 0], ![21, 36, 0, 1, 0], ![4, 20, 0, 0, 1]] ![70, 177, -76, 377, -71] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI37N0
 g := ![-151, -299, -76, 377, -71]
 hmem := by decide

def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [22, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 36], [0, 1]]
 g := ![![[30, 12], [28], [28, 10], [36], [1]],![[28, 25], [28], [14, 27], [36], [1]]]
 h' := ![![[6, 36], [34, 7], [13, 18], [25, 26], [15, 6], [0, 1]],![[0, 1], [2, 30], [10, 19], [33, 11], [14, 31], [6, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [7, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : PrimeIdeal O 37 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I37N0
  hcard := NI37N0
  P := [22, 31, 1]
  f := ofList [22, 31, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P37P0
  hneq := by decide
  hlen := by decide
  c := ![70, 177, -76, 377, -71]
  a := ![0, 4, 2, 7, -2]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI37N0
  hpmem := by
    show  _ ∈ I37N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI37N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := PrimeIdeal_isPrime PI37N0
def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 0, 0, -2, 0]] i)))

def SI37N1: IdealEqSpanCertificate O ℤ timesTableO I37N1
 ![![1, 0, 0, -2, 0]]
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![34, 6, 1, 0, 0], ![18, 0, 0, 1, 0], ![34, 24, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![1, 0, 0, -2, 0], ![0, 1, 2, 0, -2], ![-4, 6, 1, 2, 0], ![0, -2, 4, 1, 2], ![4, 0, -4, 10, 1]]]
  hmulB := by decide
  f := ![![![21, 4, 0, 2, 4]], ![![16, 1, 6, 0, 2]], ![![22, 4, 1, 2, 4]], ![![10, 2, 0, 1, 2]], ![![30, 4, 4, 2, 5]]]
  g := ![![![1, 0, 0, -2, 0], ![0, 1, 2, 0, -2], ![-2, 0, 1, 2, 0], ![-6, -2, 4, 1, 2], ![-2, 0, -4, 10, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI37N1)

def MemCI37N1 : IdealMemCertificate O ℤ B I37N1
  ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![34, 6, 1, 0, 0], ![18, 0, 0, 1, 0], ![34, 24, 0, 0, 1]] ![336, -345, -1146, -322, 545] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI37N1
 g := ![718, -177, -1146, -322, 545]
 hmem := by decide

def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [16, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 36], [0, 1]]
 g := ![![[34, 7], [3], [5, 30], [10], [1]],![[0, 30], [3], [2, 7], [10], [1]]]
 h' := ![![[11, 36], [25, 28], [31, 22], [22, 17], [21, 11], [0, 1]],![[0, 1], [0, 9], [14, 15], [24, 20], [31, 26], [11, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [32, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : PrimeIdeal O 37 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I37N1
  hcard := NI37N1
  P := [16, 26, 1]
  f := ofList [16, 26, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P37P1
  hneq := by decide
  hlen := by decide
  c := ![336, -345, -1146, -322, 545]
  a := ![-2, -23, -4, -23, 0]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI37N1
  hpmem := by
    show  _ ∈ I37N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI37N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := PrimeIdeal_isPrime PI37N1
def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0, 0, 0]] i)))

def SI37N2: IdealEqSpanCertificate O ℤ timesTableO I37N2
 ![![1, 1, 0, 0, 0]]
 ![![37, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![1, 1, 0, 0, 0], ![0, 1, 2, 0, 0], ![0, 1, 1, 2, 0], ![0, 0, -1, 1, 1], ![4, -5, 0, 0, 1]]]
  hmulB := by decide
  f := ![![![21, -3, 2, -4, 4]], ![![1, 0, 0, 0, 0]], ![![10, -1, 1, -2, 2]], ![![5, -1, 1, -1, 1]], ![![5, 0, 0, 0, 1]]]
  g := ![![![0, 1, 0, 0, 0], ![-1, 1, 2, 0, 0], ![-1, 1, 1, 2, 0], ![0, 0, -1, 1, 1], ![0, -5, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulEqCertificate O ℤ timesTableO (I37N0) I37N1
  ![![-13, -1, 0, -2, -2]] ![![1, 0, 0, -2, 0]]
  ![![-21, 3, -2, 4, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-21, 3, -2, 4, -4]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI37N1 : IdealMulEqCertificate O ℤ timesTableO (I37N0*I37N1) I37N2
  ![![-21, 3, -2, 4, -4]] ![![1, 1, 0, 0, 0]]
  ![![37, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI37N0
 hI2 := rfl
 M :=  ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![-1, 0, 0, 0, 0]]]]
 g :=  ![![![![-1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC37 : PrimesBelowPCertificate 37 ![I37N0, I37N1, I37N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI37N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl


--- Primes above 41
instance hp41 : Fact $ Nat.Prime 41 := by decide

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 5, 5, 7, 8]] i)))

def SI41N0: IdealEqSpanCertificate O ℤ timesTableO I41N0
 ![![37, 5, 5, 7, 8]]
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![29, 6, 38, 1, 0], ![10, 21, 34, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![37, 5, 5, 7, 8], ![32, 2, 3, 10, 7], ![14, 0, -3, 3, 5], ![-6, -8, -3, -8, -2], ![6, 1, -11, -3, -3]]]
  hmulB := by decide
  f := ![![![1, 1, -2, 1, 1]], ![![4, -6, 1, -4, 1]], ![![2, 0, -4, 1, -2]], ![![3, 0, -5, 1, -1]], ![![4, -3, -3, -1, -1]]]
  g := ![![![-6, -5, -13, 7, 8], ![-8, -5, -15, 10, 7], ![-3, -3, -7, 3, 5], ![6, 2, 9, -8, -2], ![3, 2, 5, -3, -3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI41N0)

def MemCI41N0 : IdealMemCertificate O ℤ B I41N0
  ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![29, 6, 38, 1, 0], ![10, 21, 34, 0, 1]] ![-1009, 1626, 5896, 4468, 886] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI41N0
 g := ![-3401, -1068, -4732, 4468, 886]
 hmem := by decide

def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [35, 7, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 40, 31], [5, 0, 10], [0, 1]]
 g := ![![[30, 39, 20], [7, 16], [30, 36], [24, 21, 1], []],![[18, 37, 39, 4], [29, 40], [17, 18], [28, 4], [29, 18]],![[24, 30, 38, 2], [29, 25], [36, 16], [5, 15, 7, 10], [9, 18]]]
 h' := ![![[16, 40, 31], [37, 25, 26], [6, 5, 4], [21, 40, 35], [0, 0, 1], [0, 1]],![[5, 0, 10], [14, 35, 37], [2, 20, 32], [8, 25, 10], [20, 37], [16, 40, 31]],![[0, 1], [2, 22, 19], [19, 16, 5], [34, 17, 37], [38, 4, 40], [5, 0, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 34], []]
 b := ![[], [34, 12, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : PrimeIdeal O 41 where
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I41N0
  hcard := NI41N0
  P := [35, 7, 20, 1]
  f := ofList [35, 7, 20, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P41P0
  hneq := by decide
  hlen := by decide
  c := ![-1009, 1626, 5896, 4468, 886]
  a := ![-17, 4, 0, 8, 1]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI41N0
  hpmem := by
    show  _ ∈ I41N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI41N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := PrimeIdeal_isPrime PI41N0
def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] i)))

def SI41N1: IdealEqSpanCertificate O ℤ timesTableO I41N1
 ![![41, 0, 0, 0, 0], ![9, 1, 0, 0, 0]]
 ![![41, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![9, 1, 0, 0, 0], ![0, 9, 2, 0, 0], ![0, 1, 9, 2, 0], ![0, 0, -1, 9, 1], ![4, -5, 0, 0, 9]]]
  hmulB := by decide
  f := ![![![3025, 1167, 8988, -984, -324], ![-13776, 615, -39606, 13284, 0]], ![![729, 285, 2233, -249, -81], ![-3320, 164, -9840, 3321, 0]], ![![1743, 672, 5246, -573, -189], ![-7938, 390, -23124, 7749, 0]], ![![1758, 676, 5242, -574, -189], ![-8006, 377, -23103, 7749, 0]], ![![722, 282, 2192, -240, -79], ![-3288, 154, -9660, 3240, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-9, 41, 0, 0, 0], ![-21, 0, 41, 0, 0], ![-24, 0, 0, 41, 0], ![-10, 0, 0, 0, 41]], ![![0, 1, 0, 0, 0], ![-3, 9, 2, 0, 0], ![-6, 1, 9, 2, 0], ![-5, 0, -1, 9, 1], ![-1, -5, 0, 0, 9]]]
  hle1 := by decide
  hle2 := by decide

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] i)))

def SI41N2: IdealEqSpanCertificate O ℤ timesTableO I41N2
 ![![41, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]]
 ![![41, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![-3, 1, 0, 0, 0], ![0, -3, 2, 0, 0], ![0, 1, -3, 2, 0], ![0, 0, -1, -3, 1], ![4, -5, 0, 0, -3]]]
  hmulB := by decide
  f := ![![![1909, -13230, 37565, -27675, 693], ![26076, 2788, 524718, -28413, 0]], ![![1798, -12431, 35293, -26001, 651], ![24560, 2624, 492984, -26691, 0]], ![![752, -5211, 14794, -10899, 273], ![10272, 1087, 206640, -11193, 0]], ![![235, -1605, 4554, -3355, 84], ![3210, 339, 63612, -3444, 0]], ![![1445, -10004, 28403, -20925, 524], ![19738, 2104, 396738, -21483, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-38, 41, 0, 0, 0], ![-16, 0, 41, 0, 0], ![-5, 0, 0, 41, 0], ![-31, 0, 0, 0, 41]], ![![-1, 1, 0, 0, 0], ![2, -3, 2, 0, 0], ![0, 1, -3, 2, 0], ![0, 0, -1, -3, 1], ![7, -5, 0, 0, -3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulEqCertificate O ℤ timesTableO (I41N0) I41N1
  ![![37, 5, 5, 7, 8]] ![![41, 0, 0, 0, 0], ![9, 1, 0, 0, 0]]
  ![![41, 0, 0, 0, 0], ![15, -2, -16, 3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![1517, 205, 205, 287, 328], ![365, 47, 48, 73, 79]]]
 hmul := by decide
 f :=  ![![![![-873416785912, 170995597419024, 38031188915784, 2415385967, -13825], ![3978898691377, -779416541656480, -49517963040, 566826, 0]]], ![![![-343681598036, 67285219526416, 14964928534262, 950432511, -5440], ![1565660613275, -306693352925130, -19484870160, 223041, 0]]]]
 g :=  ![![![![22, 7, 21, 4, 7], ![41, 0, 0, 0, 0]], ![![-5, 3, 16, -1, 1], ![38, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI41N1 : IdealMulEqCertificate O ℤ timesTableO (I41N0*I41N1) I41N2
  ![![41, 0, 0, 0, 0], ![15, -2, -16, 3, 1]] ![![41, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]]
  ![![41, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI41N0
 hI2 := rfl
 M :=  ![![![1681, 0, 0, 0, 0], ![-123, 41, 0, 0, 0]], ![![615, -82, -656, 123, 41], ![-41, 0, 41, -41, 0]]]
 hmul := by decide
 f :=  ![![![![-1762369, 12506160, -35528427, 26236041, -672463], ![-24085490, -2605172, -496482498, 27570939, 0]], ![![44, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![41, 0, 0, 0, 0]], ![![-3, 1, 0, 0, 0]]], ![![![15, -2, -16, 3, 1]], ![![-1, 0, 1, -1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC41 : PrimesBelowPCertificate 41 ![I41N0, I41N1, I41N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI41N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl

--- Primes above 43

instance hp43 : Fact $ Nat.Prime 43 := by decide

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -3, 2, 3, 1]] i)))

def SI43N0: IdealEqSpanCertificate O ℤ timesTableO I43N0
 ![![7, -3, 2, 3, 1]]
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![12, 6, 3, 1, 0], ![14, 22, 36, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![7, -3, 2, 3, 1], ![4, 4, -9, 4, 3], ![6, -10, 2, -9, 2], ![2, -3, -1, 0, -6], ![-18, 21, -4, -11, 2]]]
  hmulB := by decide
  f := ![![![9, 1, 1, 3, 2]], ![![8, 0, -1, 2, 3]], ![![6, -4, -1, -1, 1]], ![![4, 0, 0, 1, 1]], ![![12, -3, -1, 1, 3]]]
  g := ![![![-1, -1, -1, 3, 1], ![-2, -2, -3, 4, 3], ![2, 0, -1, -9, 2], ![2, 3, 5, 0, -6], ![2, 1, -1, -11, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI43N0)

def MemCI43N0 : IdealMemCertificate O ℤ B I43N0
  ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![12, 6, 3, 1, 0], ![14, 22, 36, 0, 1]] ![386, -215, -422, 137, 119] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI43N0
 g := ![-68, -85, -119, 137, 119]
 hmem := by decide

def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [34, 30, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 27, 38], [28, 15, 5], [0, 1]]
 g := ![![[23, 38, 14], [22, 30, 40], [2, 10], [26, 20, 1], []],![[29, 32, 17, 17], [5, 37, 33, 25], [], [34, 31, 38, 36], [15, 25]],![[13, 4, 35, 33], [27, 39, 17, 12], [6, 10], [39, 35, 0, 33], [5, 25]]]
 h' := ![![[35, 27, 38], [26, 18, 10], [35, 20, 13], [19, 2, 15], [0, 0, 1], [0, 1]],![[28, 15, 5], [23, 22, 17], [11, 40, 9], [21, 3], [27, 31, 15], [35, 27, 38]],![[0, 1], [5, 3, 16], [20, 26, 21], [40, 38, 28], [12, 12, 27], [28, 15, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 23], []]
 b := ![[], [26, 2, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : PrimeIdeal O 43 where
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I43N0
  hcard := NI43N0
  P := [34, 30, 23, 1]
  f := ofList [34, 30, 23, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P43P0
  hneq := by decide
  hlen := by decide
  c := ![386, -215, -422, 137, 119]
  a := ![-1, -2, -1, -3, 0]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI43N0
  hpmem := by
    show  _ ∈ I43N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI43N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := PrimeIdeal_isPrime PI43N0
def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] i)))

def SI43N1: IdealEqSpanCertificate O ℤ timesTableO I43N1
 ![![43, 0, 0, 0, 0], ![6, 1, 0, 0, 0]]
 ![![43, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]], ![![6, 1, 0, 0, 0], ![0, 6, 2, 0, 0], ![0, 1, 6, 2, 0], ![0, 0, -1, 6, 1], ![4, -5, 0, 0, 6]]]
  hmulB := by decide
  f := ![![![-19307, -16637, -86056, -22962, 918], ![138374, -5848, 612105, -39474, 0]], ![![-2874, -2474, -12786, -3414, 136], ![20598, -860, 90945, -5848, 0]], ![![-11441, -9854, -50963, -13596, 544], ![81998, -3461, 362490, -23392, 0]], ![![-3580, -3086, -15940, -4253, 170], ![25658, -1055, 113370, -7310, 0]], ![![-8980, -7738, -40026, -10680, 427], ![64360, -2721, 284700, -18360, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 43, 0, 0, 0], ![-25, 0, 43, 0, 0], ![-8, 0, 0, 43, 0], ![-20, 0, 0, 0, 43]], ![![0, 1, 0, 0, 0], ![-2, 6, 2, 0, 0], ![-4, 1, 6, 2, 0], ![-1, 0, -1, 6, 1], ![-2, -5, 0, 0, 6]]]
  hle1 := by decide
  hle2 := by decide

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![-12, 1, 0, 0, 0]] i)))

def SI43N2: IdealEqSpanCertificate O ℤ timesTableO I43N2
 ![![43, 0, 0, 0, 0], ![-12, 1, 0, 0, 0]]
 ![![43, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]], ![![-12, 1, 0, 0, 0], ![0, -12, 2, 0, 0], ![0, 1, -12, 2, 0], ![0, 0, -1, -12, 1], ![4, -5, 0, 0, -12]]]
  hmulB := by decide
  f := ![![![38665, -14842, 176958, -34400, 396], ![138546, 11481, 637432, -17028, 0]], ![![28117, -10793, 128660, -25012, 288], ![100750, 8342, 463454, -12384, 0]], ![![13922, -5340, 63719, -12404, 144], ![49886, 4150, 229534, -6192, 0]], ![![3532, -1344, 16120, -3133, 36], ![12656, 1078, 58072, -1548, 0]], ![![17089, -6554, 78190, -15200, 175], ![61234, 5089, 281656, -7524, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-31, 43, 0, 0, 0], ![-14, 0, 43, 0, 0], ![-4, 0, 0, 43, 0], ![-19, 0, 0, 0, 43]], ![![-1, 1, 0, 0, 0], ![8, -12, 2, 0, 0], ![3, 1, -12, 2, 0], ![1, 0, -1, -12, 1], ![9, -5, 0, 0, -12]]]
  hle1 := by decide
  hle2 := by decide

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulEqCertificate O ℤ timesTableO (I43N0) I43N1
  ![![7, -3, 2, 3, 1]] ![![43, 0, 0, 0, 0], ![6, 1, 0, 0, 0]]
  ![![43, 0, 0, 0, 0], ![-14, 8, -14, 12, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![301, -129, 86, 129, 43], ![46, -14, 3, 22, 9]]]
 hmul := by decide
 f :=  ![![![![-64030850241255, 20116358784127309, 6709052525426401, 14938845939, -66442], ![458887760062329, -144243665713962984, -321193758711, 2857008, 0]]], ![![![21329811426512, -6701115756496395, -2234904341871787, -4976394435, 22133], ![-152863648556670, 48050122363761024, 106995335512, -951720, 0]]]]
 g :=  ![![![![7, -3, 2, 3, 1], ![0, 0, 0, 0, 0]], ![![4, -2, 3, -2, 0], ![9, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI43N1 : IdealMulEqCertificate O ℤ timesTableO (I43N0*I43N1) I43N2
  ![![43, 0, 0, 0, 0], ![-14, 8, -14, 12, 1]] ![![43, 0, 0, 0, 0], ![-12, 1, 0, 0, 0]]
  ![![43, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI43N0
 hI2 := rfl
 M :=  ![![![1849, 0, 0, 0, 0], ![-516, 43, 0, 0, 0]], ![![-602, 344, -602, 516, 43], ![172, -129, 172, -172, 0]]]
 hmul := by decide
 f :=  ![![![![16407524443, -6336166932, 75853003000, -12722162312, 3443550], ![58793629016, 4914708661, 272638051360, -148072854, 0]], ![![204, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![43, 0, 0, 0, 0]], ![![-12, 1, 0, 0, 0]]], ![![![-14, 8, -14, 12, 1]], ![![4, -3, 4, -4, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC43 : PrimesBelowPCertificate 43 ![I43N0, I43N1, I43N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI43N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl

--- Primes above 47

instance hp47 : Fact $ Nat.Prime 47 := by decide

def I47N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0]] i)))

def SI47N: IdealEqSpanCertificate O ℤ timesTableO I47N
 ![![47, 0, 0, 0, 0]]
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI47N : Nat.card (O ⧸ I47N) = 229345007 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI47N)

def MemCI47N : IdealMemCertificate O ℤ B I47N
  ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]] ![-925853, 1768328, 1423959, 1076723, -111954] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI47N
 g := ![-19699, 37624, 30297, 22909, -2382]
 hmem := by decide

def P47P : CertificateIrreducibleZModOfList' 47 5 2 5 [32, 6, 18, 36, 22, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 12, 42, 29, 38], [34, 40, 9, 0, 32], [25, 38, 6, 10, 9], [5, 3, 37, 8, 15], [0, 1]]
 g := ![![[35, 38, 31, 6, 34], [43, 10, 2, 24, 24], [43, 5, 20, 7, 14], [1], []],![[3, 16, 25, 44, 41, 15, 26, 5], [22, 1, 31, 42, 26, 29, 12, 44], [34, 6, 42, 36, 22, 34, 36, 31], [43, 11, 26, 12, 20, 14, 43, 31], [39, 11, 46, 34]],![[7, 21, 44, 14, 26, 27, 5, 25], [33, 2, 43, 27, 31, 17, 38, 12], [30, 20, 39, 35, 45, 34, 43, 9], [19, 12, 18, 1, 28, 18, 7, 24], [9, 44, 32, 37]],![[17, 13, 5, 23, 6, 14, 43, 7], [28, 16, 26, 16, 16, 43, 34, 8], [45, 19, 0, 16, 15, 19, 14, 36], [19, 22, 16, 1, 13, 25, 42, 24], [25, 12, 43, 34]],![[38, 45, 32, 18, 40, 41, 2, 38], [26, 32, 36, 38, 14, 13, 41, 15], [38, 18, 43, 33, 18, 46, 29, 45], [15, 30, 1, 3, 31, 8, 34, 31], [46, 15, 37, 37]]]
 h' := ![![[8, 12, 42, 29, 38], [34, 14, 31, 26, 38], [34, 42, 21, 5, 27], [15, 41, 29, 11, 25], [0, 0, 1], [0, 1]],![[34, 40, 9, 0, 32], [13, 7, 46, 38, 6], [42, 21, 23, 32, 4], [24, 40, 27, 4, 17], [38, 29, 33, 10, 30], [8, 12, 42, 29, 38]],![[25, 38, 6, 10, 9], [39, 13, 14, 19, 25], [8, 32, 43, 6, 26], [9, 9, 25, 5, 15], [22, 36, 10, 14, 6], [34, 40, 9, 0, 32]],![[5, 3, 37, 8, 15], [15, 43, 20, 24, 10], [23, 10, 39, 6, 36], [45, 34, 31, 3, 2], [13, 3, 34, 45, 38], [25, 38, 6, 10, 9]],![[0, 1], [11, 17, 30, 34, 15], [32, 36, 15, 45, 1], [20, 17, 29, 24, 35], [10, 26, 16, 25, 20], [5, 3, 37, 8, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 16, 36, 11], [], [], []]
 b := ![[], [36, 39, 6, 18, 43], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N : PrimeIdeal O 47 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I47N
  hcard := NI47N
  P := [32, 6, 18, 36, 22, 1]
  f := ofList [32, 6, 18, 36, 22, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P47P
  hneq := by decide
  hlen := by decide
  c := ![-925853, 1768328, 1423959, 1076723, -111954]
  a := ![13, 0, -7, -1, 2]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI47N
  hpmem := by
    show  _ ∈ I47N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI47N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI47N : Ideal.IsPrime I47N := PrimeIdeal_isPrime PI47N
def PBC47 : PrimesBelowPCertificate 47 ![I47N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI47N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I47N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl

--- Primes above  53

instance hp53 : Fact $ Nat.Prime 53 := by decide

def I53N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0]] i)))

def SI53N: IdealEqSpanCertificate O ℤ timesTableO I53N
 ![![53, 0, 0, 0, 0]]
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI53N : Nat.card (O ⧸ I53N) = 418195493 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI53N)

def MemCI53N : IdealMemCertificate O ℤ B I53N
  ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]] ![-689, 901, 1113, 1166, -53] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI53N
 g := ![-13, 17, 21, 22, -1]
 hmem := by decide

def P53P : CertificateIrreducibleZModOfList' 53 5 2 5 [51, 31, 7, 0, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 36, 41, 10, 4], [42, 39, 50, 14, 17], [11, 6, 30, 2, 19], [36, 24, 38, 27, 13], [0, 1]]
 g := ![![[6, 3, 33, 49, 43], [13, 38, 11, 40], [24, 46, 28, 23, 42], [48, 1], []],![[22, 50, 41, 30, 15, 7, 49, 46], [0, 42, 25, 16], [6, 4, 25, 1, 12, 32, 16, 36], [16, 3, 31, 29], [23, 39, 8, 31, 15, 36, 1, 11]],![[20, 43, 27, 31, 32, 38, 34, 46], [49, 52, 6, 44], [23, 50, 41, 6, 36, 6, 21, 40], [42, 44, 12, 6], [47, 42, 39, 46, 32, 47, 28, 37]],![[51, 8, 25, 45, 23, 0, 8, 27], [0, 20, 40, 17], [34, 49, 43, 9, 37, 43, 14, 39], [47, 15, 37, 25], [6, 24, 47, 17, 6, 19, 42, 22]],![[41, 34, 0, 20, 16, 23, 10, 10], [42, 11, 24, 36], [4, 24, 28, 30, 35, 38, 47, 37], [7, 20, 34, 47], [39, 28, 34, 49, 27, 45, 1, 24]]]
 h' := ![![[12, 36, 41, 10, 4], [51, 52, 13, 46, 19], [48, 31, 39, 52, 27], [43, 51, 4, 46, 25], [0, 0, 0, 1], [0, 1]],![[42, 39, 50, 14, 17], [16, 36, 35, 27, 41], [4, 47, 4, 33, 4], [21, 21, 18, 0, 3], [25, 24, 50, 15, 20], [12, 36, 41, 10, 4]],![[11, 6, 30, 2, 19], [29, 44, 30, 11, 39], [39, 52, 28, 36, 37], [37, 33, 20, 5, 29], [35, 11, 6, 10, 18], [42, 39, 50, 14, 17]],![[36, 24, 38, 27, 13], [10, 11, 17, 29, 22], [40, 48, 4, 21, 32], [47, 39, 3, 5, 4], [18, 26, 44, 48, 5], [11, 6, 30, 2, 19]],![[0, 1], [6, 16, 11, 46, 38], [44, 34, 31, 17, 6], [52, 15, 8, 50, 45], [41, 45, 6, 32, 10], [36, 24, 38, 27, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 14, 9, 37], [], [], []]
 b := ![[], [10, 16, 11, 21, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N : PrimeIdeal O 53 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I53N
  hcard := NI53N
  P := [51, 31, 7, 0, 5, 1]
  f := ofList [51, 31, 7, 0, 5, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P53P
  hneq := by decide
  hlen := by decide
  c := ![-689, 901, 1113, 1166, -53]
  a := ![-1, -1, -1, -2, 0]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI53N
  hpmem := by
    show  _ ∈ I53N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI53N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI53N : Ideal.IsPrime I53N := PrimeIdeal_isPrime PI53N
def PBC53 : PrimesBelowPCertificate 53 ![I53N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI53N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I53N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl

--- Primes above  59

instance hp59 : Fact $ Nat.Prime 59 := by decide

def I59N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N: IdealEqSpanCertificate O ℤ timesTableO I59N
 ![![59, 0, 0, 0, 0]]
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI59N : Nat.card (O ⧸ I59N) = 714924299 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI59N)

def MemCI59N : IdealMemCertificate O ℤ B I59N
  ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] ![-206559, -1333577, 1872837, -2310676, 784759] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI59N
 g := ![-3501, -22603, 31743, -39164, 13301]
 hmem := by decide

def P59P : CertificateIrreducibleZModOfList' 59 5 2 5 [35, 41, 42, 2, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 47, 17, 30, 34], [2, 39, 52, 15, 2], [5, 7, 45, 44, 35], [17, 24, 4, 29, 47], [0, 1]]
 g := ![![[6, 23, 5, 43, 5], [15, 21, 30, 2, 29], [0, 46, 57, 21], [20, 50, 1], []],![[22, 50, 49, 45, 11, 26, 28, 34], [54, 36, 4, 11, 41, 34, 16, 54], [3, 47, 24, 46], [24, 52, 53, 39, 25, 35, 27, 43], [54, 23, 34, 53, 12, 4, 51, 10]],![[15, 57, 37, 9, 4, 26, 23, 32], [11, 38, 9, 33, 14, 21, 25, 38], [26, 17, 4, 3], [43, 50, 7, 41, 58, 44, 47, 14], [32, 15, 57, 16, 1, 42, 49, 8]],![[14, 1, 56, 27, 31, 26, 4, 36], [1, 44, 1, 40, 44, 22, 18, 7], [19, 46, 45, 16], [34, 21, 31, 10, 56, 35, 20, 15], [43, 48, 14, 39, 33, 11, 25, 41]],![[3, 22, 37, 50, 41, 44, 29, 30], [31, 44, 0, 46, 42, 11, 31, 34], [8, 1, 22, 7], [30, 45, 52, 45, 20, 42, 48, 55], [48, 27, 16, 29, 52, 19, 55, 42]]]
 h' := ![![[26, 47, 17, 30, 34], [6, 32, 33, 24, 51], [5, 45, 27, 45, 18], [8, 26, 25, 2, 32], [0, 0, 0, 1], [0, 1]],![[2, 39, 52, 15, 2], [19, 51, 46, 58, 58], [17, 28, 31, 41, 37], [57, 23, 6, 51, 39], [51, 21, 7, 14, 11], [26, 47, 17, 30, 34]],![[5, 7, 45, 44, 35], [41, 40, 36, 45, 4], [53, 49, 8, 47, 45], [14, 40, 31, 47, 11], [9, 47, 14, 4, 19], [2, 39, 52, 15, 2]],![[17, 24, 4, 29, 47], [40, 5, 18, 8, 38], [30, 13, 34, 45, 37], [39, 55, 45, 28, 55], [36, 32, 23, 25, 13], [5, 7, 45, 44, 35]],![[0, 1], [26, 49, 44, 42, 26], [44, 42, 18, 58, 40], [41, 33, 11, 49, 40], [47, 18, 15, 15, 16], [17, 24, 4, 29, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 50, 47, 6], [], [], []]
 b := ![[], [58, 8, 51, 52, 38], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N : PrimeIdeal O 59 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I59N
  hcard := NI59N
  P := [35, 41, 42, 2, 9, 1]
  f := ofList [35, 41, 42, 2, 9, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P59P
  hneq := by decide
  hlen := by decide
  c := ![-206559, -1333577, 1872837, -2310676, 784759]
  a := ![6, 3, -3, 4, -1]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI59N
  hpmem := by
    show  _ ∈ I59N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI59N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI59N : Ideal.IsPrime I59N := PrimeIdeal_isPrime PI59N
def PBC59 : PrimesBelowPCertificate 59 ![I59N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI59N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I59N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl

--- Primes above  61

instance hp61 : Fact $ Nat.Prime 61 := by decide

def I61N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N: IdealEqSpanCertificate O ℤ timesTableO I61N
 ![![61, 0, 0, 0, 0]]
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI61N : Nat.card (O ⧸ I61N) = 844596301 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI61N)

def MemCI61N : IdealMemCertificate O ℤ B I61N
  ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] ![99308, -85522, 13786, 99613, -60695] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI61N
 g := ![1628, -1402, 226, 1633, -995]
 hmem := by decide

def P61P : CertificateIrreducibleZModOfList' 61 5 2 5 [48, 11, 59, 33, 26, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 33, 35, 55, 37], [7, 17, 52, 45, 48], [37, 30, 54, 44, 19], [33, 41, 42, 39, 18], [0, 1]]
 g := ![![[39, 12, 40, 14, 19], [51, 49, 36, 45], [42, 55, 59, 46, 4], [33, 35, 1], []],![[19, 5, 0, 20, 1, 12, 60, 31], [60, 54, 45, 19], [59, 18, 46, 19, 10, 35, 14, 10], [37, 35, 9, 33, 0, 23, 37, 37], [50, 45, 6, 51, 17, 35, 14, 23]],![[57, 4, 48, 6, 18, 40, 22, 34], [32, 8, 42, 45], [50, 38, 49, 20, 1, 7, 32, 58], [23, 13, 53, 14, 56, 5, 24, 39], [59, 52, 55, 33, 54, 34, 27, 60]],![[34, 40, 13, 24, 23, 9, 44, 58], [60, 51, 34, 5], [25, 39, 1, 54, 59, 9, 7, 42], [2, 39, 30, 24, 37, 54, 59, 56], [17, 34, 40, 36, 17, 42, 41, 27]],![[59, 23, 45, 25, 10, 34, 26, 54], [13, 0, 18, 3], [3, 34, 52, 17, 33, 5, 26, 44], [32, 58, 23, 23, 9, 28, 13, 24], [41, 50, 4, 43, 19, 13, 41, 37]]]
 h' := ![![[19, 33, 35, 55, 37], [1, 59, 54, 13, 43], [58, 13, 4, 57, 17], [2, 31, 60, 7, 2], [0, 0, 0, 1], [0, 1]],![[7, 17, 52, 45, 48], [34, 7, 6, 21, 48], [48, 60, 51, 24, 43], [6, 56, 52, 16, 56], [6, 28, 48, 21, 1], [19, 33, 35, 55, 37]],![[37, 30, 54, 44, 19], [2, 17, 37, 43, 7], [14, 16, 28, 11, 44], [26, 37, 10, 19, 18], [12, 25, 5, 33, 27], [7, 17, 52, 45, 48]],![[33, 41, 42, 39, 18], [44, 11, 47, 18, 32], [22, 39, 15, 36, 26], [26, 58, 2, 5, 50], [0, 1, 22, 10, 18], [37, 30, 54, 44, 19]],![[0, 1], [48, 28, 39, 27, 53], [1, 55, 24, 55, 53], [27, 1, 59, 14, 57], [53, 7, 47, 57, 15], [33, 41, 42, 39, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 24, 24, 11], [], [], []]
 b := ![[], [15, 20, 46, 2, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N : PrimeIdeal O 61 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I61N
  hcard := NI61N
  P := [48, 11, 59, 33, 26, 1]
  f := ofList [48, 11, 59, 33, 26, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P61P
  hneq := by decide
  hlen := by decide
  c := ![99308, -85522, 13786, 99613, -60695]
  a := ![3, 0, 1, 1, -1]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI61N
  hpmem := by
    show  _ ∈ I61N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI61N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI61N : Ideal.IsPrime I61N := PrimeIdeal_isPrime PI61N
def PBC61 : PrimesBelowPCertificate 61 ![I61N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI61N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I61N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl


lemma primes_below_63 : Set.range ![61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2] = ↑(Nat.primesBelow 63) := by
  have : Nat.primesBelow 63 =  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} := by decide
  rw [this]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
    Set.union_empty, Set.union_singleton, Set.union_insert, Finset.coe_insert, Finset.coe_singleton]



-- Better to use fin_cases than pattern matching
--set_option maxHeartbeats 300000
#count_heartbeats
/- def PB17 : PrimesBelowBoundCertificate O 63 where
  m := 18
  g := ![1,1,1,1,3,3,3,1,3,3,1,3,1,3,3,5,1,5]
  P := ![61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]
  hP := primes_below_63
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![I61N]
    · exact ![I59N]
    · exact ![I53N]
    · exact ![I47N]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I37N0, I37N1, I37N2]
    · exact  ![I31N]
    · exact  ![I29N0, I29N1, I29N2]
    · exact  ![I23N0, I23N1, I23N2]
    · exact  ![I19N]
    · exact ![I17N0, I17N1, I17N2]
    · exact  ![I13N]
    · exact  ![I11N0, I11N1, I11N2]
    · exact ![I7N0, I7N1, I7N2]
    · exact  ![I5N, I5N, I5N, I5N, I5N]
    · exact  ![I3N]
    · exact  ![I2N0, I2N1, I2N1, I2N1, I2N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
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
    · exact ![844596301]
    · exact ![714924299]
    · exact ![418195493]
    · exact ![229345007]
    · exact ![79507,43,43]
    · exact ![68921,41,41]
    · exact ![1369,1369,37]
    · exact ![28629151]
    · exact ![24389,29,29]
    · exact ![529,529,23]
    · exact ![2476099]
    · exact ![4913,17,17]
    · exact ![371293]
    · exact ![1331,11,11]
    · exact ![343,7,7]
    · exact ![5,5,5,5,5]
    · exact ![243]
    · exact ![2,2,2,2,2]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · dsimp ; intro j
      fin_cases j
      exact NI61N
    · dsimp ; intro j
      fin_cases j
      exact NI59N
    · dsimp ; intro j
      fin_cases j
      exact NI53N
    · dsimp ; intro j
      fin_cases j
      exact NI47N
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
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
      exact NI3N
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N1
      exact NI2N1
  Il := ![ [], [], [], [], [I43N1, I43N2], [I41N1, I41N2], [I37N2], [], [I29N1, I29N2], [I23N2], [], [I17N1, I17N2], [], [I11N1, I11N2], [I7N1, I7N2], [I5N, I5N, I5N, I5N, I5N], [], [I2N0,I2N1, I2N1, I2N1, I2N1 ]]
  hIl := by
    intro i
    cases i
    rename_i i h
    interval_cases i
    all_goals rfl -/

def PB17 : PrimesBelowBoundCertificate O 63 where
  m := 18
  g := ![1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 1, 3, 1, 3, 3, 5, 1, 5]
  P := ![61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]
  hP := primes_below_63
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![I61N]
    · exact ![I59N]
    · exact ![I53N]
    · exact ![I47N]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I31N]
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I23N0, I23N1, I23N2]
    · exact ![I19N]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I13N]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I5N, I5N, I5N, I5N, I5N]
    · exact ![I3N]
    · exact ![I2N0, I2N1, I2N1, I2N1, I2N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
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
    · exact ![844596301]
    · exact ![714924299]
    · exact ![418195493]
    · exact ![229345007]
    · exact ![79507, 43, 43]
    · exact ![68921, 41, 41]
    · exact ![1369, 1369, 37]
    · exact ![28629151]
    · exact ![24389, 29, 29]
    · exact ![529, 529, 23]
    · exact ![2476099]
    · exact ![4913, 17, 17]
    · exact ![371293]
    · exact ![1331, 11, 11]
    · exact ![343, 7, 7]
    · exact ![5, 5, 5, 5, 5]
    · exact ![243]
    · exact ![2, 2, 2, 2, 2]
  hN := fun i => by
     cases i
     rename_i i h
     interval_cases i
     · dsimp ; intro j
       fin_cases j
       exact NI61N
     · dsimp ; intro j
       fin_cases j
       exact NI59N
     · dsimp ; intro j
       fin_cases j
       exact NI53N
     · dsimp ; intro j
       fin_cases j
       exact NI47N
     · dsimp ; intro j
       fin_cases j
       exact NI43N0
       exact NI43N1
       exact NI43N2
     · dsimp ; intro j
       fin_cases j
       exact NI41N0
       exact NI41N1
       exact NI41N2
     · dsimp ; intro j
       fin_cases j
       exact NI37N0
       exact NI37N1
       exact NI37N2
     · dsimp ; intro j
       fin_cases j
       exact NI31N
     · dsimp ; intro j
       fin_cases j
       exact NI29N0
       exact NI29N1
       exact NI29N2
     · dsimp ; intro j
       fin_cases j
       exact NI23N0
       exact NI23N1
       exact NI23N2
     · dsimp ; intro j
       fin_cases j
       exact NI19N
     · dsimp ; intro j
       fin_cases j
       exact NI17N0
       exact NI17N1
       exact NI17N2
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
       exact NI3N
     · dsimp ; intro j
       fin_cases j
       exact NI2N0
       exact NI2N1
       exact NI2N1
       exact NI2N1
       exact NI2N1
  Il := ![[], [], [], [], [I43N1, I43N2], [I41N1, I41N2], [I37N2], [], [I29N1, I29N2], [I23N2], [], [I17N1, I17N2], [], [I11N1, I11N2], [I7N1, I7N2], [I5N, I5N, I5N, I5N, I5N], [], [I2N0, I2N1, I2N1, I2N1, I2N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
