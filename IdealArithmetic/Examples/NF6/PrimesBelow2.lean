import IdealArithmetic.Examples.NF6.PrimesBelow1

open Classical Polynomial

noncomputable section

instance hp29 : Fact (Nat.Prime 29) := by decide
def I29N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0]] i)))

def SI29N: IdealEqSpanCertificate O ℤ timesTableO I29N
 ![![29, 0, 0, 0, 0]]
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI29N : Nat.card (O ⧸ I29N) = 20511149 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI29N)

def MemCI29N : IdealMemCertificate O ℤ B I29N
  ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]] ![-184324716709494558, 5681574511013895, -85874000505250718, 164187406358543402, -142966647638628261] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI29N
 g := ![-6356024714120502, 195916362448755, -2961172431215542, 5661634702018738, -4929884401332009]
 hmem := by decide

def P29P : CertificateIrreducibleZModOfList' 29 5 2 4 [13, 17, 21, 5, 7, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 5, 7, 18, 7], [23, 12, 20, 24, 9], [17, 6, 3, 17, 27], [18, 5, 28, 28, 15], [0, 1]]
 g := ![![[5, 25, 26, 25, 24], [27, 13, 28, 16], [15, 22, 1], []],![[2, 26, 20, 5, 25, 20, 21, 16], [19, 17, 12, 25], [11, 0, 13, 0, 23, 10, 20, 25], [3, 28, 18, 21, 15, 24, 13, 24]],![[1, 8, 1, 8, 18, 15, 14, 24], [12, 7, 11, 25], [19, 2, 27, 26, 4, 4, 5, 23], [16, 12, 11, 25, 0, 6, 4, 4]],![[15, 13, 17, 15, 2, 13, 4, 17], [27, 5, 15, 28], [9, 13, 22, 2, 1, 11, 23, 27], [5, 20, 28, 23, 8, 2, 28, 21]],![[8, 27, 0, 11, 14, 4, 28, 19], [7, 18, 25, 24], [12, 3, 7, 4, 0, 1, 12, 18], [22, 7, 12, 14, 25, 26, 2, 11]]]
 h' := ![![[22, 5, 7, 18, 7], [3, 25, 12, 16, 16], [8, 10, 23, 26, 25], [0, 0, 0, 1], [0, 1]],![[23, 12, 20, 24, 9], [15, 23, 1, 27, 9], [1, 8, 28, 19, 24], [24, 1, 21, 3, 4], [22, 5, 7, 18, 7]],![[17, 6, 3, 17, 27], [13, 12, 5, 26, 15], [13, 4, 16, 7, 5], [11, 27, 16, 27, 3], [23, 12, 20, 24, 9]],![[18, 5, 28, 28, 15], [2, 26, 17, 7, 21], [18, 4, 1, 19, 17], [5, 14, 3, 27, 28], [17, 6, 3, 17, 27]],![[0, 1], [26, 1, 23, 11, 26], [1, 3, 19, 16, 16], [7, 16, 18, 0, 23], [18, 5, 28, 28, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 14, 10, 6], [], [], []]
 b := ![[], [28, 2, 15, 22, 24], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N : PrimeIdeal O 29 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I29N
  hcard := NI29N
  P := [13, 17, 21, 5, 7, 1]
  f := ofList [13, 17, 21, 5, 7, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P29P
  hneq := by decide
  hlen := by decide
  c := ![-184324716709494558, 5681574511013895, -85874000505250718, 164187406358543402, -142966647638628261]
  a := ![-247, 73, -210, -252, -969]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI29N
  hpmem := by
    show  _ ∈ I29N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI29N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI29N : Ideal.IsPrime I29N := PrimeIdeal_isPrime PI29N
def PBC29 : PrimesBelowPCertificate 29 ![I29N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI29N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I29N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp31 : Fact (Nat.Prime 31) := by decide
def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-7, -2, -3, -1, -5]] i)))

def SI31N0: IdealEqSpanCertificate O ℤ timesTableO I31N0
 ![![31, 0, 0, 0, 0], ![-7, -2, -3, -1, -5]]
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![18, 4, 1, 0, 0], ![26, 17, 0, 1, 0], ![4, 7, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-7, -2, -3, -1, -5], ![-3, -9, -4, 1, 3], ![3, -8, -7, -11, 3], ![-15, 8, -13, -27, -72], ![-2, -1, 1, 12, 10]]]
  hmulB := by decide
  f := ![![![-237559, -764878, -333474, 89980, 271124], ![88660, -2657754, 3906, 0, 0]], ![![-238138, -766744, -334289, 90196, 271786], ![88877, -2664233, 3906, 0, 0]], ![![-168300, -541880, -236251, 63746, 192078], ![62808, -1882892, 2766, 0, 0]], ![![-329838, -1061984, -463009, 124929, 376436], ![123085, -3690115, 5418, 0, 0]], ![![-84427, -271830, -118514, 31977, 96354], ![31504, -944537, 1386, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-18, -4, 31, 0, 0], ![-26, -17, 0, 31, 0], ![-4, -7, 0, 0, 31]], ![![3, 2, -3, -1, -5], ![1, -1, -4, 1, 3], ![13, 6, -7, -11, 3], ![39, 33, -13, -27, -72], ![-12, -9, 1, 12, 10]]]
  hle1 := by decide
  hle2 := by decide

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI31N0)

def MemCI31N0 : IdealMemCertificate O ℤ B I31N0
  ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![18, 4, 1, 0, 0], ![26, 17, 0, 1, 0], ![4, 7, 0, 0, 1]] ![143876, -65455, 86046, 42013, 428794] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI31N0
 g := ![-135886, -133078, 86046, 42013, 428794]
 hmem := by decide

def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [22, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 30], [0, 1]]
 g := ![![[1, 19], [20, 7], [29, 9], [9, 1]],![[17, 12], [21, 24], [17, 22], [18, 30]]]
 h' := ![![[9, 30], [25, 9], [13, 21], [19, 28], [0, 1]],![[0, 1], [13, 22], [16, 10], [23, 3], [9, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [12, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : PrimeIdeal O 31 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I31N0
  hcard := NI31N0
  P := [22, 22, 1]
  f := ofList [22, 22, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P31P0
  hneq := by decide
  hlen := by decide
  c := ![143876, -65455, 86046, 42013, 428794]
  a := ![-82, 28, -81, -81, -329]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI31N0
  hpmem := by
    show  _ ∈ I31N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI31N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := PrimeIdeal_isPrime PI31N0
def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-1, 8, -3, -1, -5]] i)))

def SI31N1: IdealEqSpanCertificate O ℤ timesTableO I31N1
 ![![31, 0, 0, 0, 0], ![-1, 8, -3, -1, -5]]
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![8, 0, 1, 0, 0], ![0, 20, 0, 1, 0], ![14, 13, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-1, 8, -3, -1, -5], ![-3, -3, 6, 1, 3], ![3, 2, -1, 9, 3], ![15, -2, 7, 9, 48], ![-2, -1, 1, -8, -14]]]
  hmulB := by decide
  f := ![![![11028, 9333, -21104, -3405, -9887], ![5828, 111941, -62, 0, 0]], ![![126989, 107559, -243063, -39185, -113891], ![66836, 1289104, -837, 0, 0]], ![![2694, 2281, -5156, -832, -2416], ![1420, 27347, -15, 0, 0]], ![![81929, 69388, -156813, -25280, -73475], ![43139, 831680, -540, 0, 0]], ![![58234, 49319, -111460, -17970, -52225], ![30665, 591146, -379, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-8, 0, 31, 0, 0], ![0, -20, 0, 31, 0], ![-14, -13, 0, 0, 31]], ![![3, 3, -3, -1, -5], ![-3, -2, 6, 1, 3], ![-1, -7, -1, 9, 3], ![-23, -26, 7, 9, 48], ![6, 11, 1, -8, -14]]]
  hle1 := by decide
  hle2 := by decide

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI31N1)

def MemCI31N1 : IdealMemCertificate O ℤ B I31N1
  ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![8, 0, 1, 0, 0], ![0, 20, 0, 1, 0], ![14, 13, 0, 0, 1]] ![624, -10, 302, -466, 554] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI31N1
 g := ![-308, 68, 302, -466, 554]
 hmem := by decide

def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [30, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 30], [0, 1]]
 g := ![![[26, 28], [15, 19], [18, 25], [26, 1]],![[10, 3], [13, 12], [17, 6], [21, 30]]]
 h' := ![![[26, 30], [15, 20], [18, 22], [26, 26], [0, 1]],![[0, 1], [8, 11], [1, 9], [20, 5], [26, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [18, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : PrimeIdeal O 31 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I31N1
  hcard := NI31N1
  P := [30, 5, 1]
  f := ofList [30, 5, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P31P1
  hneq := by decide
  hlen := by decide
  c := ![624, -10, 302, -466, 554]
  a := ![5, -3, 7, 3, 22]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI31N1
  hpmem := by
    show  _ ∈ I31N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI31N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := PrimeIdeal_isPrime PI31N1
def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))

def SI31N2: IdealEqSpanCertificate O ℤ timesTableO I31N2
 ![![31, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
 ![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-4, 1, 0, 0, 0], ![0, -4, 1, 0, 0], ![0, 1, -4, 2, 0], ![3, -1, 2, -1, 12], ![0, 0, 0, -2, -7]]]
  hmulB := by decide
  f := ![![![14579, -45687, 173495, -86924, 360], ![112282, 10943, 1346857, -930, 0]], ![![14551, -45611, 173219, -86786, 360], ![112066, 10943, 1344718, -930, 0]], ![![14467, -45326, 172118, -86234, 360], ![111418, 10851, 1336162, -930, 0]], ![![7, -19, 85, -43, 0], ![54, 33, 667, 0, 0]], ![![6113, -19159, 72756, -36452, 151], ![47080, 4588, 564811, -390, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-27, 31, 0, 0, 0], ![-15, 0, 31, 0, 0], ![-1, 0, 0, 31, 0], ![-13, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0], ![3, -4, 1, 0, 0], ![1, 1, -4, 2, 0], ![-5, -1, 2, -1, 12], ![3, 0, 0, -2, -7]]]
  hle1 := by decide
  hle2 := by decide

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulEqCertificate O ℤ timesTableO (I31N0) I31N1
  ![![31, 0, 0, 0, 0], ![-7, -2, -3, -1, -5]] ![![31, 0, 0, 0, 0], ![-1, 8, -3, -1, -5]]
  ![![31, 0, 0, 0, 0], ![14, -27, 0, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![961, 0, 0, 0, 0], ![-31, 248, -93, -31, -155]], ![![-217, -62, -93, -31, -155], ![-1, -49, 0, 9, 42]]]
 hmul := by decide
 f :=  ![![![![-377354099410248, -319666176241237, 722650640492334, 117219858911851, 338885270454222], ![-198695917521918, -3833033725784593, 57921562938, 0, 0]], ![![-888593976, -665115, 0, 0, 0], ![-31, 0, 0, 0, 0]]], ![![![-177003503251255, -149944132458247, 338969936178817, 54983702868055, 158959131925142], ![-93201249272408, -1797940975344970, 27168962971, 0, 0]], ![![-416808104, -311982, 0, 0, 0], ![-14, 0, 0, 0, 0]]]]
 g :=  ![![![![17, 27, 0, 2, -1], ![31, 0, 0, 0, 0]], ![![-1, 8, -3, -1, -5], ![0, 0, 0, 0, 0]]], ![![![-7, -2, -3, -1, -5], ![0, 0, 0, 0, 0]], ![![-5, 8, 0, 1, 1], ![11, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI31N1 : IdealMulEqCertificate O ℤ timesTableO (I31N0*I31N1) I31N2
  ![![31, 0, 0, 0, 0], ![14, -27, 0, -2, 1]] ![![31, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
  ![![31, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI31N0
 hI2 := rfl
 M :=  ![![![961, 0, 0, 0, 0], ![-124, 31, 0, 0, 0]], ![![434, -837, 0, -62, 31], ![-62, 124, -31, 0, -31]]]
 hmul := by decide
 f :=  ![![![![488908486031, -1972720881469, 7636695161757, -3826170503846, 388516836], ![3788288054434, 485021269441, 59305140986257, -1003669440, 0]], ![![11364, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![31, 0, 0, 0, 0]], ![![-4, 1, 0, 0, 0]]], ![![![14, -27, 0, -2, 1]], ![![-2, 4, -1, 0, -1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC31 : PrimesBelowPCertificate 31 ![I31N0, I31N1, I31N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI31N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp37 : Fact (Nat.Prime 37) := by decide
def I37N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N: IdealEqSpanCertificate O ℤ timesTableO I37N
 ![![37, 0, 0, 0, 0]]
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI37N : Nat.card (O ⧸ I37N) = 69343957 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI37N)

def MemCI37N : IdealMemCertificate O ℤ B I37N
  ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] ![4465017159391, -205770460563, 2097157001927, -3807370720357, 3790922499672] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI37N
 g := ![120676139443, -5561363799, 56679918971, -102901911361, 102457364856]
 hmem := by decide

def P37P : CertificateIrreducibleZModOfList' 37 5 2 5 [15, 10, 18, 15, 23, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 0, 13, 27, 35], [0, 24, 25, 31, 34], [26, 25, 36, 12, 14], [15, 24, 0, 4, 28], [0, 1]]
 g := ![![[24, 8, 5, 13, 10], [27, 5, 3, 1], [3, 12, 33, 14, 1], [], []],![[23, 21, 7, 10, 5, 19, 28, 8], [0, 32, 31, 12], [36, 27, 36, 28, 19, 25, 12, 5], [31, 21, 26, 27], [4, 0, 22, 4]],![[18, 8, 15, 6, 31, 25], [24, 15, 1, 3], [31, 18, 19, 17, 22, 13, 8, 7], [3, 5, 28, 36], [33, 21, 14, 9]],![[21, 5, 3, 10, 30, 20, 25, 13], [11, 34, 2, 34], [24, 18, 33, 27, 36, 17], [23, 32, 20, 1], [15, 3, 9, 11]],![[21, 0, 16, 31, 20, 15, 23, 27], [7, 32, 0, 4], [20, 6, 25, 33, 25, 5, 29, 27], [31, 32, 28, 9], [16, 16, 26, 7]]]
 h' := ![![[10, 0, 13, 27, 35], [29, 18, 18, 31, 26], [29, 12, 34, 13, 1], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]],![[0, 24, 25, 31, 34], [33, 10, 14, 18, 12], [12, 5, 23, 14, 7], [25, 23, 34, 26, 4], [3, 34, 6, 15, 8], [10, 0, 13, 27, 35]],![[26, 25, 36, 12, 14], [7, 23, 3, 2], [16, 6, 13, 27, 15], [3, 10, 8, 24, 11], [23, 21, 6, 15, 31], [0, 24, 25, 31, 34]],![[15, 24, 0, 4, 28], [9, 21, 18, 15, 20], [10, 8, 15, 6, 16], [0, 34, 35, 5], [7, 32, 27, 3, 1], [26, 25, 36, 12, 14]],![[0, 1], [13, 2, 21, 8, 16], [9, 6, 26, 14, 35], [19, 7, 34, 19, 21], [22, 24, 34, 4, 34], [15, 24, 0, 4, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 10, 2, 10], [], [], []]
 b := ![[], [5, 27, 32, 17, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N : PrimeIdeal O 37 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I37N
  hcard := NI37N
  P := [15, 10, 18, 15, 23, 1]
  f := ofList [15, 10, 18, 15, 23, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P37P
  hneq := by decide
  hlen := by decide
  c := ![4465017159391, -205770460563, 2097157001927, -3807370720357, 3790922499672]
  a := ![28, -9, 23, 29, 112]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI37N
  hpmem := by
    show  _ ∈ I37N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI37N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI37N : Ideal.IsPrime I37N := PrimeIdeal_isPrime PI37N
def PBC37 : PrimesBelowPCertificate 37 ![I37N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI37N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I37N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp41 : Fact (Nat.Prime 41) := by decide
def I41N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N: IdealEqSpanCertificate O ℤ timesTableO I41N
 ![![41, 0, 0, 0, 0]]
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI41N : Nat.card (O ⧸ I41N) = 115856201 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI41N)

def MemCI41N : IdealMemCertificate O ℤ B I41N
  ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] ![270058511155, -156859846392, 161488733764, 124185381996, 916486642217] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI41N
 g := ![6586792955, -3825849912, 3938749604, 3028911756, 22353332737]
 hmem := by decide

def P41P : CertificateIrreducibleZModOfList' 41 5 2 5 [17, 18, 7, 14, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 14, 36, 29, 2], [25, 21, 9, 11, 25], [26, 14, 10, 25, 8], [24, 32, 27, 17, 6], [0, 1]]
 g := ![![[19, 34, 34, 8, 23], [24, 39, 1, 21], [39, 31, 7, 4], [1], []],![[16, 6, 18, 18, 15, 16, 34, 4], [16, 23, 1, 9], [31, 27, 28, 18], [38, 18, 40, 39, 10, 37, 23, 23], [39, 16, 26, 4]],![[37, 18, 36, 1, 2, 20, 26, 33], [32, 33, 14, 32], [29, 12, 12, 4], [12, 28, 22, 14, 26, 26, 20, 40], [18, 27, 38, 10]],![[32, 3, 3, 22, 22, 6, 17, 1], [13, 7, 28, 36], [24, 28, 23, 33], [27, 31, 24, 25, 3, 14, 6, 23], [33, 1, 26, 23]],![[16, 29, 36, 29, 25, 14, 3, 7], [33, 16, 7, 39], [35, 23, 22, 21], [5, 28, 13, 15, 26, 20, 14, 29], [4, 9, 9, 36]]]
 h' := ![![[5, 14, 36, 29, 2], [27, 32, 4, 29, 8], [36, 39, 22, 17, 29], [24, 23, 34, 27, 39], [0, 0, 1], [0, 1]],![[25, 21, 9, 11, 25], [17, 16, 9, 7, 17], [24, 29, 29, 10, 3], [31, 1, 36, 36, 10], [18, 27, 4, 22, 14], [5, 14, 36, 29, 2]],![[26, 14, 10, 25, 8], [31, 6, 31, 29, 29], [1, 18, 33, 35, 14], [17, 5, 27, 5, 2], [32, 21, 2, 2, 31], [25, 21, 9, 11, 25]],![[24, 32, 27, 17, 6], [5, 25, 26, 19, 35], [12, 26, 24, 22, 6], [16, 1, 16, 25, 19], [33, 35, 25, 6, 7], [26, 14, 10, 25, 8]],![[0, 1], [5, 3, 12, 39, 34], [19, 11, 15, 39, 30], [32, 11, 10, 30, 12], [16, 40, 9, 11, 30], [24, 32, 27, 17, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 24, 33, 12], [], [], []]
 b := ![[], [37, 16, 2, 38, 35], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N : PrimeIdeal O 41 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I41N
  hcard := NI41N
  P := [17, 18, 7, 14, 2, 1]
  f := ofList [17, 18, 7, 14, 2, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P41P
  hneq := by decide
  hlen := by decide
  c := ![270058511155, -156859846392, 161488733764, 124185381996, 916486642217]
  a := ![-16, -6, -19, -30, -59]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI41N
  hpmem := by
    show  _ ∈ I41N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI41N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI41N : Ideal.IsPrime I41N := PrimeIdeal_isPrime PI41N
def PBC41 : PrimesBelowPCertificate 41 ![I41N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI41N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I41N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp43 : Fact (Nat.Prime 43) := by decide
def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 9, -1, 0, -4]] i)))

def SI43N0: IdealEqSpanCertificate O ℤ timesTableO I43N0
 ![![15, 9, -1, 0, -4]]
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![4, 9, 1, 0, 0], ![25, 5, 0, 1, 0], ![6, 17, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![15, 9, -1, 0, -4], ![0, 14, 9, 6, 12], ![18, 3, 26, 12, 36], ![18, 9, 9, 5, 12], ![-10, -2, -4, -2, -5]]]
  hmulB := by decide
  f := ![![![-1, -1, -1, 2, -4]], ![![6, -4, 3, 12, 36]], ![![2, -1, 1, 2, 8]], ![![-1, 0, -1, 1, -4]], ![![2, -2, 1, 6, 15]]]
  g := ![![![1, 2, -1, 0, -4], ![-6, -7, 9, 6, 12], ![-14, -21, 26, 12, 36], ![-5, -7, 9, 5, 12], ![2, 3, -4, -2, -5]]]
  hle1 := by decide
  hle2 := by decide

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI43N0)

def MemCI43N0 : IdealMemCertificate O ℤ B I43N0
  ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![4, 9, 1, 0, 0], ![25, 5, 0, 1, 0], ![6, 17, 0, 0, 1]] ![3548, -5595, 5821, 22318, 44974] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI43N0
 g := ![-19710, -21724, 5821, 22318, 44974]
 hmem := by decide

def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [22, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 42], [0, 1]]
 g := ![![[15, 10], [37, 35], [21], [21, 24], [1]],![[26, 33], [11, 8], [21], [13, 19], [1]]]
 h' := ![![[14, 42], [3, 15], [3, 32], [11, 35], [21, 14], [0, 1]],![[0, 1], [41, 28], [21, 11], [28, 8], [2, 29], [14, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [28, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : PrimeIdeal O 43 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I43N0
  hcard := NI43N0
  P := [22, 29, 1]
  f := ofList [22, 29, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P43P0
  hneq := by decide
  hlen := by decide
  c := ![3548, -5595, 5821, 22318, 44974]
  a := ![27, 3, 29, 44, 106]
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
def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 15, 23, 12, 31]] i)))

def SI43N1: IdealEqSpanCertificate O ℤ timesTableO I43N1
 ![![17, 15, 23, 12, 31]]
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![27, 27, 1, 0, 0], ![1, 15, 0, 1, 0], ![37, 1, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![17, 15, 23, 12, 31], ![36, 28, 39, 20, 51], ![60, 55, 68, 36, 87], ![36, 32, 44, 25, 60], ![-14, -14, -18, -10, -23]]]
  hmulB := by decide
  f := ![![![-11, 9, -3, 2, -1]], ![![6, -16, 13, 2, 27]], ![![-3, -4, 6, 2, 15]], ![![1, -5, 4, 1, 8]], ![![-9, 7, -2, 2, 1]]]
  g := ![![![-41, -19, 23, 12, 31], ![-68, -32, 39, 20, 51], ![-117, -56, 68, 36, 87], ![-79, -37, 44, 25, 60], ![31, 15, -18, -10, -23]]]
  hle1 := by decide
  hle2 := by decide

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI43N1)

def MemCI43N1 : IdealMemCertificate O ℤ B I43N1
  ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![27, 27, 1, 0, 0], ![1, 15, 0, 1, 0], ![37, 1, 0, 0, 1]] ![2051, -990, 1238, 818, 6462] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI43N1
 g := ![-6309, -1236, 1238, 818, 6462]
 hmem := by decide

def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [11, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 42], [0, 1]]
 g := ![![[1, 4], [41, 35], [17], [29, 35], [1]],![[0, 39], [0, 8], [17], [31, 8], [1]]]
 h' := ![![[32, 42], [22, 2], [8, 32], [25, 19], [32, 32], [0, 1]],![[0, 1], [0, 41], [0, 11], [31, 24], [24, 11], [32, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [6, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : PrimeIdeal O 43 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I43N1
  hcard := NI43N1
  P := [11, 11, 1]
  f := ofList [11, 11, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P43P1
  hneq := by decide
  hlen := by decide
  c := ![2051, -990, 1238, 818, 6462]
  a := ![-11, 3, -11, -11, -42]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI43N1
  hpmem := by
    show  _ ∈ I43N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI43N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := PrimeIdeal_isPrime PI43N1
def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 1, 0, 0]] i)))

def SI43N2: IdealEqSpanCertificate O ℤ timesTableO I43N2
 ![![1, 1, 1, 0, 0]]
 ![![43, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![1, 1, 1, 0, 0], ![0, 2, 1, 2, 0], ![6, -1, 6, 8, 24], ![12, 1, 7, -7, 12], ![-6, 2, -4, -2, -17]]]
  hmulB := by decide
  f := ![![![133, 55, -83, -38, -144]], ![![19, 11, -14, -6, -24]], ![![115, 44, -69, -32, -120]], ![![123, 50, -76, -35, -132]], ![![125, 53, -79, -36, -137]]]
  g := ![![![-1, 1, 1, 0, 0], ![-3, 2, 1, 2, 0], ![-35, -1, 6, 8, 24], ![-11, 1, 7, -7, 12], ![21, 2, -4, -2, -17]]]
  hle1 := by decide
  hle2 := by decide

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulEqCertificate O ℤ timesTableO (I43N0) I43N1
  ![![15, 9, -1, 0, -4]] ![![17, 15, 23, 12, 31]]
  ![![575, 478, 700, 364, 929]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![575, 478, 700, 364, 929]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI43N1 : IdealMulEqCertificate O ℤ timesTableO (I43N0*I43N1) I43N2
  ![![575, 478, 700, 364, 929]] ![![1, 1, 1, 0, 0]]
  ![![43, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI43N0
 hI2 := rfl
 M :=  ![![![3569, 3053, 4085, 2150, 5375]]]
 hmul := by decide
 f :=  ![![![![-3, 3, -1, 0, -1]]]]
 g :=  ![![![![83, 71, 95, 50, 125]]]]
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
instance hp47 : Fact (Nat.Prime 47) := by decide
def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![-19, -2, -3, -1, -5]] i)))

def SI47N0: IdealEqSpanCertificate O ℤ timesTableO I47N0
 ![![47, 0, 0, 0, 0], ![-19, -2, -3, -1, -5]]
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![3, 42, 1, 0, 0], ![31, 13, 0, 1, 0], ![24, 29, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![-19, -2, -3, -1, -5], ![-3, -21, -4, 1, 3], ![3, -8, -19, -11, 3], ![-15, 8, -13, -39, -72], ![-2, -1, 1, 12, -2]]]
  hmulB := by decide
  f := ![![![330514, 3003024, 561471, -146673, -456945], ![-245481, 6741210, 8460, 0, 0]], ![![827531, 7518986, 1405800, -367249, -1144103], ![-614666, 16878687, 21150, 0, 0]], ![![759422, 6900112, 1290092, -337021, -1049933], ![-564065, 15489432, 19410, 0, 0]], ![![446895, 4060438, 759171, -198321, -617842], ![-331915, 9114903, 11430, 0, 0]], ![![679383, 6172834, 1154118, -301497, -939268], ![-504600, 13856829, 17370, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-3, -42, 47, 0, 0], ![-31, -13, 0, 47, 0], ![-24, -29, 0, 0, 47]], ![![3, 6, -3, -1, -5], ![-2, 1, -4, 1, 3], ![7, 18, -19, -11, 3], ![63, 67, -13, -39, -72], ![-7, -3, 1, 12, -2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI47N0)

def MemCI47N0 : IdealMemCertificate O ℤ B I47N0
  ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![3, 42, 1, 0, 0], ![31, 13, 0, 1, 0], ![24, 29, 0, 0, 1]] ![142, 7, -5, 88, 357] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI47N0
 g := ![-237, -240, -5, 88, 357]
 hmem := by decide

def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [36, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 46], [0, 1]]
 g := ![![[28, 17], [11, 6], [41, 25], [6, 18], [1]],![[0, 30], [26, 41], [33, 22], [4, 29], [1]]]
 h' := ![![[26, 46], [27, 8], [28, 10], [19, 5], [11, 26], [0, 1]],![[0, 1], [0, 39], [6, 37], [8, 42], [29, 21], [26, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [8, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : PrimeIdeal O 47 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I47N0
  hcard := NI47N0
  P := [36, 21, 1]
  f := ofList [36, 21, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P47P0
  hneq := by decide
  hlen := by decide
  c := ![142, 7, -5, 88, 357]
  a := ![-1, 0, -6, -1, -3]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI47N0
  hpmem := by
    show  _ ∈ I47N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI47N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := PrimeIdeal_isPrime PI47N0
def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![-2, -5, -3, -1, -5]] i)))

def SI47N1: IdealEqSpanCertificate O ℤ timesTableO I47N1
 ![![47, 0, 0, 0, 0], ![-2, -5, -3, -1, -5]]
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![31, 34, 1, 0, 0], ![37, 2, 0, 1, 0], ![12, 46, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![-2, -5, -3, -1, -5], ![-3, -4, -7, 1, 3], ![3, -11, -2, -17, 3], ![-24, 11, -19, -31, -108], ![-2, -1, 1, 18, 24]]]
  hmulB := by decide
  f := ![![![1908563, 2521635, 4466273, -653649, -1968725], ![-411203, 30166480, -8460, 0, 0]], ![![1143164, 1510373, 2675144, -391516, -1179196], ![-246280, 18068680, -5076, 0, 0]], ![![2081755, 2750460, 4871563, -712966, -2147374], ![-448504, 32903920, -9234, 0, 0]], ![![1551131, 2049388, 3629838, -531235, -1600026], ![-334194, 24516960, -6876, 0, 0]], ![![1606134, 2122059, 3758551, -550075, -1656760], ![-346029, 25386320, -7128, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-31, -34, 47, 0, 0], ![-37, -2, 0, 47, 0], ![-12, -46, 0, 0, 47]], ![![4, 7, -3, -1, -5], ![3, 2, -7, 1, 3], ![14, -1, -2, -17, 3], ![64, 121, -19, -31, -108], ![-21, -25, 1, 18, 24]]]
  hle1 := by decide
  hle2 := by decide

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI47N1)

def MemCI47N1 : IdealMemCertificate O ℤ B I47N1
  ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![31, 34, 1, 0, 0], ![37, 2, 0, 1, 0], ![12, 46, 0, 0, 1]] ![28015, -13326, 16381, 7534, 83200] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI47N1
 g := ![-37382, -93884, 16381, 7534, 83200]
 hmem := by decide

def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [38, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 46], [0, 1]]
 g := ![![[28, 25], [30, 28], [24, 6], [2, 7], [1]],![[30, 22], [36, 19], [32, 41], [27, 40], [1]]]
 h' := ![![[17, 46], [35, 42], [28, 34], [18, 37], [9, 17], [0, 1]],![[0, 1], [44, 5], [42, 13], [36, 10], [16, 30], [17, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [31, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : PrimeIdeal O 47 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I47N1
  hcard := NI47N1
  P := [38, 30, 1]
  f := ofList [38, 30, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P47P1
  hneq := by decide
  hlen := by decide
  c := ![28015, -13326, 16381, 7534, 83200]
  a := ![-35, 12, -31, -34, -140]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI47N1
  hpmem := by
    show  _ ∈ I47N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI47N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := PrimeIdeal_isPrime PI47N1
def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![18, 1, 0, 0, 0]] i)))

def SI47N2: IdealEqSpanCertificate O ℤ timesTableO I47N2
 ![![47, 0, 0, 0, 0], ![18, 1, 0, 0, 0]]
 ![![47, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![18, 1, 0, 0, 0], ![0, 18, 1, 0, 0], ![0, 1, 18, 2, 0], ![3, -1, 2, 21, 12], ![0, 0, 0, -2, 15]]]
  hmulB := by decide
  f := ![![![134401, -4453, -385353, -35814, 4080], ![-348270, -25991, 1009419, -15980, 0]], ![![53742, -1787, -154163, -14328, 1632], ![-139260, -10387, 403824, -6392, 0]], ![![20140, -666, -57757, -5367, 612], ![-52188, -3900, 151293, -2397, 0]], ![![114215, -3784, -327551, -30442, 3468], ![-295962, -22099, 858009, -13583, 0]], ![![60027, -1991, -172179, -16002, 1823], ![-155546, -11613, 451017, -7140, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-18, 47, 0, 0, 0], ![-5, 0, 47, 0, 0], ![-40, 0, 0, 47, 0], ![-21, 0, 0, 0, 47]], ![![0, 1, 0, 0, 0], ![-7, 18, 1, 0, 0], ![-4, 1, 18, 2, 0], ![-23, -1, 2, 21, 12], ![-5, 0, 0, -2, 15]]]
  hle1 := by decide
  hle2 := by decide

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulEqCertificate O ℤ timesTableO (I47N0) I47N1
  ![![47, 0, 0, 0, 0], ![-19, -2, -3, -1, -5]] ![![47, 0, 0, 0, 0], ![-2, -5, -3, -1, -5]]
  ![![47, 0, 0, 0, 0], ![2, 93, -43, -12, -75]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![2209, 0, 0, 0, 0], ![-94, -235, -141, -47, -235]], ![![-893, -94, -141, -47, -235], ![69, 130, 91, 9, 68]]]
 hmul := by decide
 f :=  ![![![![3438413269374990872, 4547655097237477011, 8049202261471418292, -1172523099533404471, -3548800365938880953], ![-741408167662208768, 54362469212383108374, -276963255065232, 0, 0]], ![![77316759658, 5343997, 0, 0, 0], ![-1504, 0, 0, 0, 0]]], ![![![146845540573676920, 194218326529976083, 343760148845483721, -50075361772147746, -151559881636649149], ![-31663582774006208, 2321677341555669270, -11828368413810, 0, 0]], ![![3301994402, 228228, 0, 0, 0], ![-64, 0, 0, 0, 0]]]]
 g :=  ![![![![45, -93, 43, 12, 75], ![47, 0, 0, 0, 0]], ![![-4, -98, 40, 11, 70], ![47, 0, 0, 0, 0]]], ![![![-21, -95, 40, 11, 70], ![47, 0, 0, 0, 0]], ![![1, -19, 12, 3, 19], ![11, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI47N1 : IdealMulEqCertificate O ℤ timesTableO (I47N0*I47N1) I47N2
  ![![47, 0, 0, 0, 0], ![2, 93, -43, -12, -75]] ![![47, 0, 0, 0, 0], ![18, 1, 0, 0, 0]]
  ![![47, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI47N0
 hI2 := rfl
 M :=  ![![![2209, 0, 0, 0, 0], ![846, 47, 0, 0, 0]], ![![94, 4371, -2021, -564, -3525], ![0, 1645, -705, -188, -1269]]]
 hmul := by decide
 f :=  ![![![![-42911209780, -3659489941, 1663239777, 159995703, -19257303], ![112033388806, 3588358736, -4550671275, 75300293, 0]], ![![-19863, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![47, 0, 0, 0, 0]], ![![18, 1, 0, 0, 0]]], ![![![2, 93, -43, -12, -75]], ![![0, 35, -15, -4, -27]]]]
 hle1 := by decide
 hle2 := by decide

def PBC47 : PrimesBelowPCertificate 47 ![I47N0, I47N1, I47N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI47N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp53 : Fact (Nat.Prime 53) := by decide
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
  ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]] ![1033412495258155, -16429485355743, 477592330395600, -959024381155055, 727263778819078] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI53N
 g := ![19498348967135, -309990289731, 9011176045200, -18094799644435, 13721958090926]
 hmem := by decide

def P53P : CertificateIrreducibleZModOfList' 53 5 2 5 [39, 52, 37, 32, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 8, 43, 39, 9], [17, 10, 37, 52, 22], [27, 16, 27, 10, 18], [5, 18, 52, 5, 4], [0, 1]]
 g := ![![[34, 9, 29, 20, 10], [4, 38, 37, 29], [12, 45, 16, 47, 49], [48, 1], []],![[38, 48, 21, 51, 24, 29, 28, 52], [34, 40, 0, 52], [51, 19, 24, 7, 9, 2, 39, 29], [13, 21, 20, 52], [9, 44, 0, 51, 6, 35, 2, 40]],![[44, 21, 2, 24, 29, 42, 31, 39], [7, 44, 22, 49], [34, 52, 25, 16, 34, 22, 24, 23], [27, 38, 45, 52], [45, 18, 12, 35, 7, 29, 4, 48]],![[0, 40, 25, 25, 8, 42, 35, 30], [51, 0, 35, 40], [43, 6, 46, 49, 12, 15, 35, 39], [7, 9, 27, 11], [43, 28, 37, 11, 21, 43, 11, 2]],![[24, 42, 4, 4, 9, 1, 52, 46], [25, 39, 13, 24], [42, 7, 51, 4, 39, 48, 30, 16], [35, 36, 1, 1], [40, 11, 41, 23, 38, 35, 26, 11]]]
 h' := ![![[52, 8, 43, 39, 9], [31, 16, 17, 34, 40], [9, 30, 49, 14, 33], [36, 9, 27, 17, 46], [0, 0, 0, 1], [0, 1]],![[17, 10, 37, 52, 22], [12, 33, 20, 13, 43], [15, 29, 15, 31, 23], [13, 6, 22, 13, 42], [19, 13, 19, 13, 23], [52, 8, 43, 39, 9]],![[27, 16, 27, 10, 18], [3, 50, 46, 46, 50], [45, 6, 35, 38, 7], [14, 13, 48, 18, 28], [31, 10, 31, 17, 23], [17, 10, 37, 52, 22]],![[5, 18, 52, 5, 4], [40, 1, 25, 1, 14], [42, 36, 28, 30, 26], [29, 19, 48, 4, 45], [39, 23, 35, 25, 8], [27, 16, 27, 10, 18]],![[0, 1], [31, 6, 51, 12, 12], [23, 5, 32, 46, 17], [29, 6, 14, 1, 51], [49, 7, 21, 50, 52], [5, 18, 52, 5, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 27, 45, 33], [], [], []]
 b := ![[], [15, 31, 34, 22, 14], [], [], []]
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
  P := [39, 52, 37, 32, 5, 1]
  f := ofList [39, 52, 37, 32, 5, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P53P
  hneq := by decide
  hlen := by decide
  c := ![1033412495258155, -16429485355743, 477592330395600, -959024381155055, 727263778819078]
  a := ![84, -27, 70, 87, 338]
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
instance hp59 : Fact (Nat.Prime 59) := by decide
def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![23, 18, -3, -1, -5]] i)))

def SI59N0: IdealEqSpanCertificate O ℤ timesTableO I59N0
 ![![59, 0, 0, 0, 0], ![23, 18, -3, -1, -5]]
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![49, 41, 1, 0, 0], ![28, 40, 0, 1, 0], ![43, 11, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![23, 18, -3, -1, -5], ![-3, 21, 16, 1, 3], ![3, 12, 23, 29, 3], ![45, -12, 27, 63, 168], ![-2, -1, 1, -28, -20]]]
  hmulB := by decide
  f := ![![![2087823, -9706734, -7835604, -482074, -1591382], ![-1605980, 28684266, -63720, 0, 0]], ![![3478455, -16171955, -13054557, -803145, -2651337], ![-2675709, 47789646, -106200, 0, 0]], ![![4150007, -19294181, -15574921, -958212, -3163212], ![-3192264, 57016080, -126684, 0, 0]], ![![3349107, -15570622, -12569139, -773286, -2552749], ![-2576203, 46012632, -102240, 0, 0]], ![![2170160, -10089509, -8144595, -501081, -1654138], ![-1669323, 29815416, -66240, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-49, -41, 59, 0, 0], ![-28, -40, 0, 59, 0], ![-43, -11, 0, 0, 59]], ![![7, 4, -3, -1, -5], ![-16, -12, 16, 1, 3], ![-35, -36, 23, 29, 3], ![-174, -93, 27, 63, 168], ![27, 22, 1, -28, -20]]]
  hle1 := by decide
  hle2 := by decide

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI59N0)

def MemCI59N0 : IdealMemCertificate O ℤ B I59N0
  ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![49, 41, 1, 0, 0], ![28, 40, 0, 1, 0], ![43, 11, 0, 0, 1]] ![4974, -1034, 2539, -2088, 8210] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI59N0
 g := ![-7017, -1897, 2539, -2088, 8210]
 hmem := by decide

def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [45, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 58], [0, 1]]
 g := ![![[25, 21], [26, 36], [35], [2, 15], [55, 1]],![[0, 38], [0, 23], [35], [1, 44], [51, 58]]]
 h' := ![![[55, 58], [10, 32], [35, 53], [28, 34], [3, 30], [0, 1]],![[0, 1], [0, 27], [0, 6], [10, 25], [1, 29], [55, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [36, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : PrimeIdeal O 59 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I59N0
  hcard := NI59N0
  P := [45, 4, 1]
  f := ofList [45, 4, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P59P0
  hneq := by decide
  hlen := by decide
  c := ![4974, -1034, 2539, -2088, 8210]
  a := ![13, -7, 12, 8, 53]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI59N0
  hpmem := by
    show  _ ∈ I59N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI59N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := PrimeIdeal_isPrime PI59N0
def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![27, -18, -3, -1, -5]] i)))

def SI59N1: IdealEqSpanCertificate O ℤ timesTableO I59N1
 ![![59, 0, 0, 0, 0], ![27, -18, -3, -1, -5]]
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![44, 37, 1, 0, 0], ![12, 46, 0, 1, 0], ![13, 43, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![27, -18, -3, -1, -5], ![-3, 25, -20, 1, 3], ![3, -24, 27, -43, 3], ![-63, 24, -45, -41, -264], ![-2, -1, 1, 44, 92]]]
  hmulB := by decide
  f := ![![![-62819, 11866738, -10448102, 465842, 1267468], ![-3233141, -30324584, 9145, 0, 0]], ![![-591366, 111717273, -98361790, 4385492, 11932358], ![-30437923, -285485542, 85963, 0, 0]], ![![-417494, 78869470, -69440846, 3096050, 8423932], ![-21488363, -201545299, 60698, 0, 0]], ![![-473850, 89515182, -78813890, 3513945, 9560986], ![-24388832, -228749660, 68882, 0, 0]], ![![-444832, 84035765, -73989531, 3298849, 8975736], ![-22895969, -214747422, 64666, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-44, -37, 59, 0, 0], ![-12, -46, 0, 59, 0], ![-13, -43, 0, 0, 59]], ![![4, 6, -3, -1, -5], ![14, 10, -20, 1, 3], ![-12, 14, 27, -43, 3], ![99, 253, -45, -41, -264], ![-30, -102, 1, 44, 92]]]
  hle1 := by decide
  hle2 := by decide

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI59N1)

def MemCI59N1 : IdealMemCertificate O ℤ B I59N1
  ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![44, 37, 1, 0, 0], ![12, 46, 0, 1, 0], ![13, 43, 0, 0, 1]] ![165, -52, 124, 2, 399] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI59N1
 g := ![-178, -371, 124, 2, 399]
 hmem := by decide

def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [7, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 58], [0, 1]]
 g := ![![[57, 17], [56, 15], [4], [18, 26], [14, 1]],![[0, 42], [30, 44], [4], [28, 33], [28, 58]]]
 h' := ![![[14, 58], [21, 28], [36, 29], [51, 57], [20, 12], [0, 1]],![[0, 1], [0, 31], [29, 30], [23, 2], [11, 47], [14, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [5, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : PrimeIdeal O 59 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I59N1
  hcard := NI59N1
  P := [7, 45, 1]
  f := ofList [7, 45, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P59P1
  hneq := by decide
  hlen := by decide
  c := ![165, -52, 124, 2, 399]
  a := ![2, -1, 2, 1, 7]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI59N1
  hpmem := by
    show  _ ∈ I59N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI59N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := PrimeIdeal_isPrime PI59N1
def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![-19, 1, 0, 0, 0]] i)))

def SI59N2: IdealEqSpanCertificate O ℤ timesTableO I59N2
 ![![59, 0, 0, 0, 0], ![-19, 1, 0, 0, 0]]
 ![![59, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![-19, 1, 0, 0, 0], ![0, -19, 1, 0, 0], ![0, 1, -19, 2, 0], ![3, -1, 2, -16, 12], ![0, 0, 0, -2, -22]]]
  hmulB := by decide
  f := ![![![13931001, -2367951, 37896769, -4017192, 19800], ![43244050, 1124245, 117728364, -97350, 0]], ![![9751663, -1657568, 26527640, -2812024, 13860], ![30270718, 786942, 82409548, -68145, 0]], ![![12537831, -2131151, 34106895, -3615452, 17820], ![38919428, 1011792, 105954914, -87615, 0]], ![![464393, -78924, 1263231, -133907, 660], ![1441550, 37504, 3924297, -3245, 0]], ![![7555830, -1284318, 20554180, -2178816, 10739], ![23454502, 609748, 63852672, -52800, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-40, 59, 0, 0, 0], ![-52, 0, 59, 0, 0], ![-2, 0, 0, 59, 0], ![-32, 0, 0, 0, 59]], ![![-1, 1, 0, 0, 0], ![12, -19, 1, 0, 0], ![16, 1, -19, 2, 0], ![-7, -1, 2, -16, 12], ![12, 0, 0, -2, -22]]]
  hle1 := by decide
  hle2 := by decide

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulEqCertificate O ℤ timesTableO (I59N0) I59N1
  ![![59, 0, 0, 0, 0], ![23, 18, -3, -1, -5]] ![![59, 0, 0, 0, 0], ![27, -18, -3, -1, -5]]
  ![![59, 0, 0, 0, 0], ![23, 60, 4, 8, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![3481, 0, 0, 0, 0], ![1593, -1062, -177, -59, -295]], ![![1357, 1062, -177, -59, -295], ![631, 89, -470, -55, -266]]]
 hmul := by decide
 f :=  ![![![![-65278438169325209031648, 12337214693241133715599969, -10861101570791302104558200, 477616501658429790687845, 1318653727237211665473508], ![-3361355300582758802186961, -31535894563096609271460430, 112426403890281807345, 0, 0]], ![![-33774942932904, -6527720, 0, 0, 0], ![-1357, 0, 0, 0, 0]]], ![![![-25453182852958249961571, 4810491646088901468163909, -4234929817849236961209867, 186230867208689493852250, 514165708928918688925756], ![-1310650093642977478487504, -12296386268679127120089994, 43836983481393552861, 0, 0]], ![![-13169429637540, -2545270, 0, 0, 0], ![-529, 0, 0, 0, 0]]]]
 g :=  ![![![![36, -60, -4, -8, 1], ![59, 0, 0, 0, 0]], ![![27, -18, -3, -1, -5], ![0, 0, 0, 0, 0]]], ![![![0, -42, -7, -9, -4], ![59, 0, 0, 0, 0]], ![![-1, -29, -10, -5, -4], ![30, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI59N1 : IdealMulEqCertificate O ℤ timesTableO (I59N0*I59N1) I59N2
  ![![59, 0, 0, 0, 0], ![23, 60, 4, 8, -1]] ![![59, 0, 0, 0, 0], ![-19, 1, 0, 0, 0]]
  ![![59, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI59N0
 hI2 := rfl
 M :=  ![![![3481, 0, 0, 0, 0], ![-1121, 59, 0, 0, 0]], ![![1357, 3540, 236, 472, -59], ![-413, -1121, 0, -118, 118]]]
 hmul := by decide
 f :=  ![![![![37669150531, -6402855426, 102470370082, -10862241744, 53552400], ![116931051730, 3039769294, 318329737128, -263299302, 0]], ![![-24, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![59, 0, 0, 0, 0]], ![![-19, 1, 0, 0, 0]]], ![![![23, 60, 4, 8, -1]], ![![-7, -19, 0, -2, 2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC59 : PrimesBelowPCertificate 59 ![I59N0, I59N1, I59N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI59N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp61 : Fact (Nat.Prime 61) := by decide
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
  ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] ![8937633039803, -640307832981, 4255170385587, -7050292626650, 8689073606881] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI61N
 g := ![146518574423, -10496849721, 69756891567, -115578567650, 142443829621]
 hmem := by decide

def P61P : CertificateIrreducibleZModOfList' 61 5 2 5 [1, 27, 13, 32, 39, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 24, 18, 26, 52], [7, 1, 11, 14, 32], [51, 9, 7, 34, 1], [44, 26, 25, 48, 37], [0, 1]]
 g := ![![[19, 11, 29, 22, 14], [9, 29, 25, 49], [9, 42, 53, 28, 12], [25, 22, 1], []],![[51, 4, 54, 51, 11, 9, 59, 12], [60, 2, 38, 19], [30, 36, 57, 6, 23, 4, 44, 14], [41, 59, 41, 43, 55, 38, 15, 22], [14, 16, 8, 44, 24, 21, 40, 3]],![[60, 8, 27, 9, 4, 46, 32, 24], [47, 45, 41, 49], [49, 49, 55, 49, 11, 35, 0, 7], [54, 10, 20, 49, 35, 10, 11, 53], [44, 14, 53, 43, 34, 1, 1, 11]],![[11, 28, 33, 10, 53, 16, 31, 9], [9, 55, 58, 22], [16, 42, 39, 18, 11, 20, 14, 9], [20, 20, 56, 4, 30, 47, 36, 57], [12, 6, 14, 9, 35, 24, 2, 1]],![[17, 10, 17, 41, 21, 29, 53, 43], [7, 29, 9, 36], [33, 48, 49, 12, 38, 34, 36, 50], [54, 40, 60, 47, 9, 51, 27, 54], [49, 3, 5, 11, 4, 23, 2, 23]]]
 h' := ![![[42, 24, 18, 26, 52], [11, 13, 6, 1, 40], [52, 35, 57, 36, 54], [36, 35, 56, 46, 16], [0, 0, 0, 1], [0, 1]],![[7, 1, 11, 14, 32], [14, 45, 39, 40, 18], [47, 8, 46, 3, 18], [45, 22, 24, 59, 45], [20, 39, 9, 53, 17], [42, 24, 18, 26, 52]],![[51, 9, 7, 34, 1], [15, 41, 48, 60, 57], [1, 37, 29, 0, 7], [15, 19, 32, 58, 56], [55, 43, 25, 6, 36], [7, 1, 11, 14, 32]],![[44, 26, 25, 48, 37], [56, 22, 26, 33, 3], [2, 19, 11, 33, 49], [13, 49, 15, 41, 58], [25, 52, 9, 17, 22], [51, 9, 7, 34, 1]],![[0, 1], [50, 1, 3, 49, 4], [22, 23, 40, 50, 55], [13, 58, 56, 40, 8], [40, 49, 18, 45, 47], [44, 26, 25, 48, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 52, 36, 23], [], [], []]
 b := ![[], [19, 4, 6, 38, 50], [], [], []]
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
  P := [1, 27, 13, 32, 39, 1]
  f := ofList [1, 27, 13, 32, 39, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P61P
  hneq := by decide
  hlen := by decide
  c := ![8937633039803, -640307832981, 4255170385587, -7050292626650, 8689073606881]
  a := ![34, -10, 30, 35, 133]
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
