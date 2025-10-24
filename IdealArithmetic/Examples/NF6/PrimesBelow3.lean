import IdealArithmetic.Examples.NF6.PrimesBelow2

open Classical Polynomial

noncomputable section

instance hp67 : Fact (Nat.Prime 67) := by decide
def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0], ![17, 32, -3, -1, -5]] i)))

def SI67N0: IdealEqSpanCertificate O ℤ timesTableO I67N0
 ![![67, 0, 0, 0, 0], ![17, 32, -3, -1, -5]]
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![8, 36, 1, 0, 0], ![57, 60, 0, 1, 0], ![34, 27, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![0, 0, 0, 0, 67]], ![![17, 32, -3, -1, -5], ![-3, 15, 30, 1, 3], ![3, 26, 17, 57, 3], ![87, -26, 55, 99, 336], ![-2, -1, 1, -56, -68]]]
  hmulB := by decide
  f := ![![![10803, -36343, -82803, -2896, -8990], ![-10117, 183915, 0, 0, 0]], ![![-1280920, 4298938, 9804211, 340394, 1064872], ![1204727, -21777345, 3082, 0, 0]], ![![-677415, 2273447, 5184893, 180013, 563153], ![637147, -11516805, 1633, 0, 0]], ![![-1137890, 3818899, 8709444, 302366, 945965], ![1070206, -19345635, 2760, 0, 0]], ![![-510708, 1713968, 3908931, 135704, 424565], ![480347, -8682615, 1242, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-8, -36, 67, 0, 0], ![-57, -60, 0, 67, 0], ![-34, -27, 0, 0, 67]], ![![4, 5, -3, -1, -5], ![-6, -18, 30, 1, 3], ![-52, -61, 17, 57, 3], ![-260, -254, 55, 99, 336], ![82, 77, 1, -56, -68]]]
  hle1 := by decide
  hle2 := by decide

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI67N0)

def MemCI67N0 : IdealMemCertificate O ℤ B I67N0
  ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![8, 36, 1, 0, 0], ![57, 60, 0, 1, 0], ![34, 27, 0, 0, 1]] ![-248, 45, -129, 87, -444] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI67N0
 g := ![163, 171, -129, 87, -444]
 hmem := by decide

def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [19, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 66], [0, 1]]
 g := ![![[22, 60], [37, 40], [33], [16], [55], [1]],![[0, 7], [0, 27], [33], [16], [55], [1]]]
 h' := ![![[51, 66], [34, 44], [49, 24], [26, 57], [53, 63], [48, 51], [0, 1]],![[0, 1], [0, 23], [0, 43], [52, 10], [50, 4], [36, 16], [51, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [55, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : PrimeIdeal O 67 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I67N0
  hcard := NI67N0
  P := [19, 16, 1]
  f := ofList [19, 16, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P67P0
  hneq := by decide
  hlen := by decide
  c := ![-248, 45, -129, 87, -444]
  a := ![-1, -1, -1, -5, -6]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI67N0
  hpmem := by
    show  _ ∈ I67N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI67N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := PrimeIdeal_isPrime PI67N0
def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0], ![-9, -26, -3, -1, -5]] i)))

def SI67N1: IdealEqSpanCertificate O ℤ timesTableO I67N1
 ![![67, 0, 0, 0, 0], ![-9, -26, -3, -1, -5]]
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![34, 2, 1, 0, 0], ![33, 49, 0, 1, 0], ![15, 21, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![0, 0, 0, 0, 67]], ![![-9, -26, -3, -1, -5], ![-3, -11, -28, 1, 3], ![3, -32, -9, -59, 3], ![-87, 32, -61, -101, -360], ![-2, -1, 1, 60, 80]]]
  hmulB := by decide
  f := ![![![242338, 938280, 2860989, -113479, -345919], ![-497207, 6900330, -3484, 0, 0]], ![![241017, 933161, 2845429, -112879, -344039], ![-494527, 6862810, -3484, 0, 0]], ![![128377, 497044, 1515548, -60113, -183241], ![-263357, 3655300, -1846, 0, 0]], ![![295626, 1144597, 3490129, -138446, -421989], ![-606567, 8417740, -4264, 0, 0]], ![![129804, 502565, 1532373, -60785, -185274], ![-266267, 3695880, -1872, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-34, -2, 67, 0, 0], ![-33, -49, 0, 67, 0], ![-15, -21, 0, 0, 67]], ![![3, 2, -3, -1, -5], ![13, -1, -28, 1, 3], ![33, 42, -9, -59, 3], ![160, 189, -61, -101, -360], ![-48, -69, 1, 60, 80]]]
  hle1 := by decide
  hle2 := by decide

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI67N1)

def MemCI67N1 : IdealMemCertificate O ℤ B I67N1
  ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![34, 2, 1, 0, 0], ![33, 49, 0, 1, 0], ![15, 21, 0, 0, 1]] ![2930, -1575, 1898, 1877, 10564] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI67N1
 g := ![-4209, -4764, 1898, 1877, 10564]
 hmem := by decide

def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [10, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 66], [0, 1]]
 g := ![![[58, 47], [16, 62], [64], [56], [60], [1]],![[0, 20], [35, 5], [64], [56], [60], [1]]]
 h' := ![![[23, 66], [41, 39], [31, 14], [66, 59], [36, 49], [57, 23], [0, 1]],![[0, 1], [0, 28], [18, 53], [16, 8], [24, 18], [50, 44], [23, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [38, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : PrimeIdeal O 67 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I67N1
  hcard := NI67N1
  P := [10, 44, 1]
  f := ofList [10, 44, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P67P1
  hneq := by decide
  hlen := by decide
  c := ![2930, -1575, 1898, 1877, 10564]
  a := ![10, -3, 8, 11, 41]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI67N1
  hpmem := by
    show  _ ∈ I67N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI67N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := PrimeIdeal_isPrime PI67N1
def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0], ![29, 1, 0, 0, 0]] i)))

def SI67N2: IdealEqSpanCertificate O ℤ timesTableO I67N2
 ![![67, 0, 0, 0, 0], ![29, 1, 0, 0, 0]]
 ![![67, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![0, 0, 0, 0, 67]], ![![29, 1, 0, 0, 0], ![0, 29, 1, 0, 0], ![0, 1, 29, 2, 0], ![3, -1, 2, 32, 12], ![0, 0, 0, -2, 26]]]
  hmulB := by decide
  f := ![![![-56922358, -5460020, -149251905, -10245104, 19608], ![131521603, -3819737, 344962632, -109478, 0]], ![![-25151854, -2412577, -65948771, -4526924, 8664], ![58114461, -1687797, 152425938, -48374, 0]], ![![-26475200, -2539527, -69418670, -4765108, 9120], ![61172110, -1776571, 160445838, -50920, 0]], ![![-45008394, -4317219, -118013150, -8100781, 15504], ![103993867, -3020274, 272761188, -86564, 0]], ![![-29735574, -2852248, -77967413, -5351920, 10243], ![68705347, -1995389, 180204360, -57190, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-29, 67, 0, 0, 0], ![-30, 0, 67, 0, 0], ![-53, 0, 0, 67, 0], ![-35, 0, 0, 0, 67]], ![![0, 1, 0, 0, 0], ![-13, 29, 1, 0, 0], ![-15, 1, 29, 2, 0], ![-32, -1, 2, 32, 12], ![-12, 0, 0, -2, 26]]]
  hle1 := by decide
  hle2 := by decide

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulEqCertificate O ℤ timesTableO (I67N0) I67N1
  ![![67, 0, 0, 0, 0], ![17, 32, -3, -1, -5]] ![![67, 0, 0, 0, 0], ![-9, -26, -3, -1, -5]]
  ![![67, 0, 0, 0, 0], ![62, 32, -93, -41, -146]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4489, 0, 0, 0, 0], ![-603, -1742, -201, -67, -335]], ![![1139, 2144, -201, -67, -335], ![-161, -725, -864, -7, -38]]]
 hmul := by decide
 f :=  ![![![![383384025009147188, 1484380055256036719, 4526245037269649866, -179548909660846975, -547267982884193115], ![-786674387305468892, 10916722622341452550, -5531827646270640, 0, 0]], ![![-2106564237600, -64379043, 0, 0, 0], ![4154, 0, 0, 0, 0]]], ![![![354771664152227620, 1373599180156228902, 4188446517025853371, -166148982017643703, -506424786532056596], ![-727964034295994506, 10101995907951413800, -5118981417715334, 0, 0]], ![![-1949349089856, -59574366, 0, 0, 0], ![3844, 0, 0, 0, 0]]]]
 g :=  ![![![![5, -32, 93, 41, 146], ![67, 0, 0, 0, 0]], ![![-9, -26, -3, -1, -5], ![0, 0, 0, 0, 0]]], ![![![-45, 0, 90, 40, 141], ![67, 0, 0, 0, 0]], ![![-57, -39, 69, 36, 128], ![59, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI67N1 : IdealMulEqCertificate O ℤ timesTableO (I67N0*I67N1) I67N2
  ![![67, 0, 0, 0, 0], ![62, 32, -93, -41, -146]] ![![67, 0, 0, 0, 0], ![29, 1, 0, 0, 0]]
  ![![67, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI67N0
 hI2 := rfl
 M :=  ![![![4489, 0, 0, 0, 0], ![1943, 67, 0, 0, 0]], ![![4154, 2144, -6231, -2747, -9782], ![1675, 938, -2747, -1206, -4288]]]
 hmul := by decide
 f :=  ![![![![-14415683019797648, -504045089346193, -297185728057188, -20502437642342, 367449252], ![33305198913144021, -7622222929718, 686864486412864, -2051586620, 0]], ![![414, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![67, 0, 0, 0, 0]], ![![29, 1, 0, 0, 0]]], ![![![62, 32, -93, -41, -146]], ![![25, 14, -41, -18, -64]]]]
 hle1 := by decide
 hle2 := by decide

def PBC67 : PrimesBelowPCertificate 67 ![I67N0, I67N1, I67N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI67N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp71 : Fact (Nat.Prime 71) := by decide
def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0], ![-23, -30, -3, -1, -5]] i)))

def SI71N0: IdealEqSpanCertificate O ℤ timesTableO I71N0
 ![![71, 0, 0, 0, 0], ![-23, -30, -3, -1, -5]]
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![50, 40, 1, 0, 0], ![65, 42, 0, 1, 0], ![61, 2, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]], ![![-23, -30, -3, -1, -5], ![-3, -25, -32, 1, 3], ![3, -36, -23, -67, 3], ![-99, 36, -69, -127, -408], ![-2, -1, 1, 68, 78]]]
  hmulB := by decide
  f := ![![![-3762783, 437119414, 661994610, -23669836, -77362792], ![-205669534, 1487942030, 194824, 0, 0]], ![![-2687932, 312255506, 472894711, -16908518, -55263976], ![-146919661, 1062908837, 139160, 0, 0]], ![![-4163216, 483639236, 732446433, -26188870, -85596012], ![-227557569, 1646294118, 215551, 0, 0]], ![![-5034844, 584894272, 885791937, -31671790, -103516457], ![-275199227, 1990963424, 260680, 0, 0]], ![![-3308517, 384349246, 582076912, -20812352, -68023353], ![-180840536, 1308313824, 171304, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-50, -40, 71, 0, 0], ![-65, -42, 0, 71, 0], ![-61, -2, 0, 0, 71]], ![![7, 2, -3, -1, -5], ![19, 17, -32, 1, 3], ![75, 52, -23, -67, 3], ![514, 126, -69, -127, -408], ![-130, -43, 1, 68, 78]]]
  hle1 := by decide
  hle2 := by decide

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI71N0)

def MemCI71N0 : IdealMemCertificate O ℤ B I71N0
  ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![50, 40, 1, 0, 0], ![65, 42, 0, 1, 0], ![61, 2, 0, 0, 1]] ![118722, -65132, 75204, 66420, 414196] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI71N0
 g := ![-467954, -94244, 75204, 66420, 414196]
 hmem := by decide

def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [46, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 70], [0, 1]]
 g := ![![[37, 58], [55, 16], [31, 54], [20], [4], [1]],![[11, 13], [16, 55], [68, 17], [20], [4], [1]]]
 h' := ![![[2, 70], [26, 49], [65, 4], [15, 14], [15, 37], [25, 2], [0, 1]],![[0, 1], [53, 22], [2, 67], [43, 57], [18, 34], [29, 69], [2, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [56, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : PrimeIdeal O 71 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I71N0
  hcard := NI71N0
  P := [46, 69, 1]
  f := ofList [46, 69, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P71P0
  hneq := by decide
  hlen := by decide
  c := ![118722, -65132, 75204, 66420, 414196]
  a := ![71, -20, 60, 76, 284]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI71N0
  hpmem := by
    show  _ ∈ I71N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI71N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := PrimeIdeal_isPrime PI71N0
def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0], ![-12, -20, -3, -1, -5]] i)))

def SI71N1: IdealEqSpanCertificate O ℤ timesTableO I71N1
 ![![71, 0, 0, 0, 0], ![-12, -20, -3, -1, -5]]
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![61, 25, 1, 0, 0], ![54, 38, 0, 1, 0], ![26, 24, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]], ![![-12, -20, -3, -1, -5], ![-3, -14, -22, 1, 3], ![3, -26, -12, -47, 3], ![-69, 26, -49, -86, -288], ![-2, -1, 1, 48, 59]]]
  hmulB := by decide
  f := ![![![-5478041, -31267892, -53747080, 2710066, 8194422], ![11389536, -175078616, 126522, 0, 0]], ![![-2324400, -13267371, -22805591, 1149911, 3477003], ![4832757, -74288152, 53676, 0, 0]], ![![-5523772, -31528907, -54195736, 2732686, 8262824], ![11484593, -176540088, 127575, 0, 0]], ![![-5410446, -30882066, -53083871, 2676622, 8093307], ![11248989, -172918240, 124956, 0, 0]], ![![-2791754, -15934956, -27390961, 1381121, 4176100], ![5804435, -89224784, 64476, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-61, -25, 71, 0, 0], ![-54, -38, 0, 71, 0], ![-26, -24, 0, 0, 71]], ![![5, 3, -3, -1, -5], ![17, 6, -22, 1, 3], ![45, 28, -12, -47, 3], ![212, 161, -49, -86, -288], ![-59, -46, 1, 48, 59]]]
  hle1 := by decide
  hle2 := by decide

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI71N1)

def MemCI71N1 : IdealMemCertificate O ℤ B I71N1
  ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![61, 25, 1, 0, 0], ![54, 38, 0, 1, 0], ![26, 24, 0, 0, 1]] ![1313, -669, 929, 1071, 4882] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI71N1
 g := ![-3382, -2560, 929, 1071, 4882]
 hmem := by decide

def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [43, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 70], [0, 1]]
 g := ![![[70, 38], [31, 29], [61, 25], [6], [3], [1]],![[0, 33], [0, 42], [0, 46], [6], [3], [1]]]
 h' := ![![[43, 70], [16, 31], [4, 61], [69, 5], [16, 52], [28, 43], [0, 1]],![[0, 1], [0, 40], [0, 10], [0, 66], [51, 19], [31, 28], [43, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [51, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : PrimeIdeal O 71 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I71N1
  hcard := NI71N1
  P := [43, 28, 1]
  f := ofList [43, 28, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P71P1
  hneq := by decide
  hlen := by decide
  c := ![1313, -669, 929, 1071, 4882]
  a := ![8, -2, 8, 9, 31]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI71N1
  hpmem := by
    show  _ ∈ I71N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI71N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := PrimeIdeal_isPrime PI71N1
def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] i)))

def SI71N2: IdealEqSpanCertificate O ℤ timesTableO I71N2
 ![![71, 0, 0, 0, 0], ![6, 1, 0, 0, 0]]
 ![![71, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]], ![![6, 1, 0, 0, 0], ![0, 6, 1, 0, 0], ![0, 1, 6, 2, 0], ![3, -1, 2, 9, 12], ![0, 0, 0, -2, 3]]]
  hmulB := by decide
  f := ![![![-250937, -3300198, -19809944, -6594054, 17112], ![3020056, -558628, 234544524, -101246, 0]], ![![-21822, -286975, -1722604, -573396, 1488], ![262630, -48564, 20395176, -8804, 0]], ![![-130919, -1721818, -10335479, -3440328, 8928], ![1575626, -291454, 122369352, -52824, 0]], ![![-120016, -1578356, -9474324, -3153679, 8184], ![1444406, -267176, 112173504, -48422, 0]], ![![-247402, -3253718, -19530931, -6501180, 16871], ![2977512, -550739, 231241080, -99820, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 71, 0, 0, 0], ![-35, 0, 71, 0, 0], ![-34, 0, 0, 71, 0], ![-70, 0, 0, 0, 71]], ![![0, 1, 0, 0, 0], ![-1, 6, 1, 0, 0], ![-4, 1, 6, 2, 0], ![-17, -1, 2, 9, 12], ![-2, 0, 0, -2, 3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulEqCertificate O ℤ timesTableO (I71N0) I71N1
  ![![71, 0, 0, 0, 0], ![-23, -30, -3, -1, -5]] ![![71, 0, 0, 0, 0], ![-12, -20, -3, -1, -5]]
  ![![71, 0, 0, 0, 0], ![-38, 103, -7, 5, -20]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![5041, 0, 0, 0, 0], ![-852, -1420, -213, -71, -355]], ![![-1633, -2130, -213, -71, -355], ![436, 937, 809, -20, 9]]]
 hmul := by decide
 f :=  ![![![![-172161197864063644333986, -982671115496598930155973, -1689134693499031812009948, 85170335196651006174888, 257529842186112680017943], ![357942834065783427674553, -5502277467930019767256408, 3976030519903679459535, 0, 0]], ![![62530949476423130, 4167535048, 0, 0, 0], ![-497, 0, 0, 0, 0]]], ![![![92126138984586615199413, 525842622411697952843775, 903882288620281222333368, -45575973186977541131805, -137808230473916792244622], ![-191540786709201135266361, 2944354390136882812831120, -2127635871660393642801, 0, 0]], ![![-33461285201162030, -2230112928, 0, 0, 0], ![266, 0, 0, 0, 0]]]]
 g :=  ![![![![71, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-12, -20, -3, -1, -5], ![0, 0, 0, 0, 0]]], ![![![-23, -30, -3, -1, -5], ![0, 0, 0, 0, 0]], ![![42, -84, 18, -5, 19], ![67, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI71N1 : IdealMulEqCertificate O ℤ timesTableO (I71N0*I71N1) I71N2
  ![![71, 0, 0, 0, 0], ![-38, 103, -7, 5, -20]] ![![71, 0, 0, 0, 0], ![6, 1, 0, 0, 0]]
  ![![71, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI71N0
 hI2 := rfl
 M :=  ![![![5041, 0, 0, 0, 0], ![426, 71, 0, 0, 0]], ![![-2698, 7313, -497, 355, -1420], ![-213, 568, 71, 71, 0]]]
 hmul := by decide
 f :=  ![![![![-19452401217, -255840773692, -1535724921468, -511190171224, 1326903232], ![234112180576, -43308024764, 18182579857404, -7850840856, 0]], ![![1960, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![71, 0, 0, 0, 0]], ![![6, 1, 0, 0, 0]]], ![![![-38, 103, -7, 5, -20]], ![![-3, 8, 1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC71 : PrimesBelowPCertificate 71 ![I71N0, I71N1, I71N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI71N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp73 : Fact (Nat.Prime 73) := by decide
def I73N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0]] i)))

def SI73N: IdealEqSpanCertificate O ℤ timesTableO I73N
 ![![73, 0, 0, 0, 0]]
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI73N : Nat.card (O ⧸ I73N) = 2073071593 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI73N)

def MemCI73N : IdealMemCertificate O ℤ B I73N
  ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]] ![-2782055109591, -932375220024, -1042031894230, 5017711994823, 2741659904927] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI73N
 g := ![-38110343967, -12772263288, -14274409510, 68735780751, 37556984999]
 hmem := by decide

def P73P : CertificateIrreducibleZModOfList' 73 5 2 6 [59, 45, 39, 29, 27, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 59, 38, 36, 8], [60, 20, 65, 72, 13], [9, 53, 63, 8, 57], [19, 13, 53, 30, 68], [0, 1]]
 g := ![![[70, 67, 4, 47, 72], [28, 69, 12, 6], [33, 4, 61, 72], [70, 21, 43, 46, 1], [], []],![[23, 60, 21, 14, 25, 14, 49, 69], [54, 11, 50, 48], [17, 66, 71, 49], [22, 44, 29, 65, 21, 6, 54, 61], [33, 15, 47, 35], [65, 54, 16, 64]],![[52, 5, 23, 44, 20, 48, 0, 11], [26, 4], [10, 39, 55, 9], [19, 17, 46, 20, 37, 5, 11, 44], [63, 24, 1, 49], [15, 24, 10, 23]],![[68, 38, 44, 72, 37, 37, 54, 69], [17, 61, 50, 27], [66, 35, 45, 54], [63, 11, 57, 31, 37, 35, 65, 70], [18, 18, 35, 61], [29, 54, 59, 37]],![[45, 40, 53, 11, 24, 39, 72, 60], [53, 60, 59, 36], [17, 69, 59, 46], [43, 47, 12, 35, 72, 29, 37, 52], [46, 37, 5, 49], [30, 55, 47, 25]]]
 h' := ![![[31, 59, 38, 36, 8], [9, 14, 40, 51, 46], [36, 57, 56, 38, 58], [31, 64, 66, 21, 46], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]],![[60, 20, 65, 72, 13], [25, 55, 67, 24, 67], [46, 42, 53, 28, 11], [63, 46, 15, 37, 7], [23, 6, 67, 34, 20], [46, 29, 1, 54, 20], [31, 59, 38, 36, 8]],![[9, 53, 63, 8, 57], [69, 34, 67, 19, 35], [17, 8, 3, 71], [13, 64, 19, 72, 70], [56, 21, 71, 8, 3], [14, 17, 32, 32, 7], [60, 20, 65, 72, 13]],![[19, 13, 53, 30, 68], [23, 16, 56, 40, 37], [2, 0, 34, 28, 10], [10, 51, 33, 24, 45], [25, 4, 45, 29, 60], [49, 40, 40, 59, 39], [9, 53, 63, 8, 57]],![[0, 1], [67, 27, 62, 12, 34], [37, 39, 0, 54, 67], [50, 67, 13, 65, 51], [33, 42, 36, 2, 62], [51, 60, 72, 1, 7], [19, 13, 53, 30, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 55, 37, 55], [], [], []]
 b := ![[], [47, 12, 58, 46, 57], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N : PrimeIdeal O 73 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I73N
  hcard := NI73N
  P := [59, 45, 39, 29, 27, 1]
  f := ofList [59, 45, 39, 29, 27, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P73P
  hneq := by decide
  hlen := by decide
  c := ![-2782055109591, -932375220024, -1042031894230, 5017711994823, 2741659904927]
  a := ![-28, 10, -24, -27, -113]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI73N
  hpmem := by
    show  _ ∈ I73N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI73N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI73N : Ideal.IsPrime I73N := PrimeIdeal_isPrime PI73N
def PBC73 : PrimesBelowPCertificate 73 ![I73N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI73N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I73N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp79 : Fact (Nat.Prime 79) := by decide
def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0], ![12, 19, -3, -1, -5]] i)))

def SI79N0: IdealEqSpanCertificate O ℤ timesTableO I79N0
 ![![79, 0, 0, 0, 0], ![12, 19, -3, -1, -5]]
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![14, 35, 1, 0, 0], ![71, 27, 0, 1, 0], ![54, 33, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]], ![![12, 19, -3, -1, -5], ![-3, 10, 17, 1, 3], ![3, 13, 12, 31, 3], ![48, -13, 29, 55, 180], ![-2, -1, 1, -30, -34]]]
  hmulB := by decide
  f := ![![![3885937, -12012928, -20983152, -1236160, -3773184], ![-1247568, 97310304, -29072, 0, 0]], ![![9452280, -29220565, -51040026, -3006846, -9178006], ![-3034706, 236700432, -70784, 0, 0]], ![![4874234, -15068081, -26319667, -1550534, -4732798], ![-1564922, 122058640, -36496, 0, 0]], ![![6722957, -20783194, -36302337, -2138636, -6527879], ![-2158453, 168353712, -50320, 0, 0]], ![![6604638, -20417416, -35663433, -2100995, -6412992], ![-2120477, 165390768, -49440, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-14, -35, 79, 0, 0], ![-71, -27, 0, 79, 0], ![-54, -33, 0, 0, 79]], ![![5, 4, -3, -1, -5], ![-6, -9, 17, 1, 3], ![-32, -17, 12, 31, 3], ![-177, -107, 29, 55, 180], ![50, 24, 1, -30, -34]]]
  hle1 := by decide
  hle2 := by decide

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI79N0)

def MemCI79N0 : IdealMemCertificate O ℤ B I79N0
  ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![14, 35, 1, 0, 0], ![71, 27, 0, 1, 0], ![54, 33, 0, 0, 1]] ![761, 1972, -60, -5538, -8742] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI79N0
 g := ![10973, 5596, -60, -5538, -8742]
 hmem := by decide

def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [23, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 78], [0, 1]]
 g := ![![[73, 55], [20, 1], [6, 64], [46, 31], [5], [1]],![[0, 24], [0, 78], [69, 15], [58, 48], [5], [1]]]
 h' := ![![[59, 78], [14, 56], [20, 1], [48, 71], [19, 30], [56, 59], [0, 1]],![[0, 1], [0, 23], [0, 78], [50, 8], [51, 49], [61, 20], [59, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [42, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : PrimeIdeal O 79 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I79N0
  hcard := NI79N0
  P := [23, 20, 1]
  f := ofList [23, 20, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P79P0
  hneq := by decide
  hlen := by decide
  c := ![761, 1972, -60, -5538, -8742]
  a := ![6, -9, 5, -6, 27]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI79N0
  hpmem := by
    show  _ ∈ I79N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI79N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := PrimeIdeal_isPrime PI79N0
def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0], ![16, -18, -3, -1, -5]] i)))

def SI79N1: IdealEqSpanCertificate O ℤ timesTableO I79N1
 ![![79, 0, 0, 0, 0], ![16, -18, -3, -1, -5]]
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![52, 59, 1, 0, 0], ![46, 24, 0, 1, 0], ![67, 74, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]], ![![16, -18, -3, -1, -5], ![-3, 14, -20, 1, 3], ![3, -24, 16, -43, 3], ![-63, 24, -45, -52, -264], ![-2, -1, 1, 44, 81]]]
  hmulB := by decide
  f := ![![![-3940531, 21862976, -32986364, 1591032, 4612576], ![-4838908, -129552100, 22752, 0, 0]], ![![-29584635, 164142531, -247654670, 11945035, 34630245], ![-36329730, -972649975, 170640, 0, 0]], ![![-24680299, 136932107, -206600165, 9964877, 28889479], ![-30307216, -811410675, 142368, 0, 0]], ![![-11282222, 62596424, -94444112, 4555295, 13206384], ![-13854480, -370924000, 65088, 0, 0]], ![![-31054153, 172295774, -259956102, 12538376, 36350387], ![-38134294, -1020963150, 179136, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-52, -59, 79, 0, 0], ![-46, -24, 0, 79, 0], ![-67, -74, 0, 0, 79]], ![![7, 7, -3, -1, -5], ![10, 12, -20, 1, 3], ![12, -2, 16, -43, 3], ![283, 297, -45, -52, -264], ![-95, -90, 1, 44, 81]]]
  hle1 := by decide
  hle2 := by decide

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI79N1)

def MemCI79N1 : IdealMemCertificate O ℤ B I79N1
  ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![52, 59, 1, 0, 0], ![46, 24, 0, 1, 0], ![67, 74, 0, 0, 1]] ![-12036, 7728, -6542, -4050, -39816] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI79N1
 g := ![40280, 43510, -6542, -4050, -39816]
 hmem := by decide

def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [34, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 78], [0, 1]]
 g := ![![[33, 36], [59, 49], [13, 25], [19, 36], [19], [1]],![[10, 43], [65, 30], [8, 54], [75, 43], [19], [1]]]
 h' := ![![[63, 78], [48, 73], [32, 7], [65, 5], [36, 73], [45, 63], [0, 1]],![[0, 1], [65, 6], [78, 72], [64, 74], [53, 6], [64, 16], [63, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [42, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : PrimeIdeal O 79 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I79N1
  hcard := NI79N1
  P := [34, 16, 1]
  f := ofList [34, 16, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P79P1
  hneq := by decide
  hlen := by decide
  c := ![-12036, 7728, -6542, -4050, -39816]
  a := ![-2, -13, -3, -30, -12]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI79N1
  hpmem := by
    show  _ ∈ I79N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI79N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := PrimeIdeal_isPrime PI79N1
def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0], ![-15, 1, 0, 0, 0]] i)))

def SI79N2: IdealEqSpanCertificate O ℤ timesTableO I79N2
 ![![79, 0, 0, 0, 0], ![-15, 1, 0, 0, 0]]
 ![![79, 0, 0, 0, 0], ![64, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]], ![![-15, 1, 0, 0, 0], ![0, -15, 1, 0, 0], ![0, 1, -15, 2, 0], ![3, -1, 2, -12, 12], ![0, 0, 0, -2, -18]]]
  hmulB := by decide
  f := ![![![5619511, -1081137, 11290113, -1516326, 10800], ![29581866, 247428, 59468277, -71100, 0]], ![![4870126, -936966, 9784501, -1314114, 9360], ![25637002, 214406, 51537783, -61620, 0]], ![![1123788, -216193, 2257758, -303230, 2160], ![5915772, 49534, 11892265, -14220, 0]], ![![4120972, -792837, 8279421, -1111973, 7920], ![21693354, 181431, 43610094, -52140, 0]], ![![3912325, -752687, 7860205, -1055670, 7519], ![20595008, 172280, 41401965, -49500, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-64, 79, 0, 0, 0], ![-12, 0, 79, 0, 0], ![-58, 0, 0, 79, 0], ![-55, 0, 0, 0, 79]], ![![-1, 1, 0, 0, 0], ![12, -15, 1, 0, 0], ![0, 1, -15, 2, 0], ![1, -1, 2, -12, 12], ![14, 0, 0, -2, -18]]]
  hle1 := by decide
  hle2 := by decide

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulEqCertificate O ℤ timesTableO (I79N0) I79N1
  ![![79, 0, 0, 0, 0], ![12, 19, -3, -1, -5]] ![![79, 0, 0, 0, 0], ![16, -18, -3, -1, -5]]
  ![![79, 0, 0, 0, 0], ![-37, -118, 136, 52, 219]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![6241, 0, 0, 0, 0], ![1264, -1422, -237, -79, -395]], ![![948, 1501, -237, -79, -395], ![199, 103, -424, -32, -153]]]
 hmul := by decide
 f :=  ![![![![-11693856415142664090819871, 64880285815792385535650557, -97889966128698718626830995, 4721489973910618058876252, 13688226646201301765558652], ![-14359994584118563748113971, -384457408051867187023549775, 67448708903930812711470, 0, 0]], ![![-11678822850196635, -1279393193, 0, 0, 0], ![-4108, 0, 0, 0, 0]]], ![![![5474955215246363340878273, -30376348621304117522630890, 45831175067499787398535711, -2210557855227435431324551, -6408700877073302323802060], ![6723216400829247009065063, 179999395967270392329443600, -31578860511492320807100, 0, 0]], ![![5467916639443566, 599000038, 0, 0, 0], ![1924, 0, 0, 0, 0]]]]
 g :=  ![![![![79, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![16, -18, -3, -1, -5], ![0, 0, 0, 0, 0]]], ![![![12, 19, -3, -1, -5], ![0, 0, 0, 0, 0]], ![![25, 73, -88, -32, -135], ![48, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI79N1 : IdealMulEqCertificate O ℤ timesTableO (I79N0*I79N1) I79N2
  ![![79, 0, 0, 0, 0], ![-37, -118, 136, 52, 219]] ![![79, 0, 0, 0, 0], ![-15, 1, 0, 0, 0]]
  ![![79, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI79N0
 hI2 := rfl
 M :=  ![![![6241, 0, 0, 0, 0], ![-1185, 79, 0, 0, 0]], ![![-2923, -9322, 10744, 4108, 17301], ![711, 1817, -2054, -790, -3318]]]
 hmul := by decide
 f :=  ![![![![-5747412669202949, 395419324418718, -108018353735350, 14458080473526, -103025213820], ![-30269571073727826, 26723510464423, -567024663348825, 678251938518, 0]], ![![-143244, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![79, 0, 0, 0, 0]], ![![-15, 1, 0, 0, 0]]], ![![![-37, -118, 136, 52, 219]], ![![9, 23, -26, -10, -42]]]]
 hle1 := by decide
 hle2 := by decide

def PBC79 : PrimesBelowPCertificate 79 ![I79N0, I79N1, I79N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI79N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp83 : Fact (Nat.Prime 83) := by decide
def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0], ![31, 3, -3, -1, -5]] i)))

def SI83N0: IdealEqSpanCertificate O ℤ timesTableO I83N0
 ![![83, 0, 0, 0, 0], ![31, 3, -3, -1, -5]]
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![16, 43, 1, 0, 0], ![71, 80, 0, 1, 0], ![53, 24, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]], ![![31, 3, -3, -1, -5], ![-3, 29, 1, 1, 3], ![3, -3, 31, -1, 3], ![0, 3, -3, 26, -12], ![-2, -1, 1, 2, 33]]]
  hmulB := by decide
  f := ![![![-14734172, 147283207, 5013161, 5061443, 15149151], ![-1334391, -421392328, 41832, 0, 0]], ![![-50784213, 507640592, 17278881, 17445259, 52214535], ![-4599279, -1452411688, 144088, 0, 0]], ![![-29140345, 291287820, 9914744, 10010215, 29961075], ![-2639103, -833404264, 82684, 0, 0]], ![![-61552551, 615281388, 20942708, 21144375, 63286172], ![-5574556, -1760383016, 174664, 0, 0]], ![![-24093159, 240835954, 8197478, 8276418, 24771733], ![-2181994, -689056312, 68376, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-16, -43, 83, 0, 0], ![-71, -80, 0, 83, 0], ![-53, -24, 0, 0, 83]], ![![5, 4, -3, -1, -5], ![-3, -2, 1, 1, 3], ![-7, -16, 31, -1, 3], ![-14, -20, -3, 26, -12], ![-23, -12, 1, 2, 33]]]
  hle1 := by decide
  hle2 := by decide

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI83N0)

def MemCI83N0 : IdealMemCertificate O ℤ B I83N0
  ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![16, 43, 1, 0, 0], ![71, 80, 0, 1, 0], ![53, 24, 0, 0, 1]] ![-120, 143, -31, 577, 144] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI83N0
 g := ![-581, -580, -31, 577, 144]
 hmem := by decide

def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [49, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 82], [0, 1]]
 g := ![![[22, 61], [68, 51], [75], [30], [69, 1], [1]],![[0, 22], [36, 32], [75], [30], [70, 82], [1]]]
 h' := ![![[1, 82], [71, 12], [77, 47], [10, 65], [22, 14], [34, 1], [0, 1]],![[0, 1], [0, 71], [41, 36], [75, 18], [36, 69], [35, 82], [1, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [20, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : PrimeIdeal O 83 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I83N0
  hcard := NI83N0
  P := [49, 82, 1]
  f := ofList [49, 82, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P83P0
  hneq := by decide
  hlen := by decide
  c := ![-120, 143, -31, 577, 144]
  a := ![1, 1, 1, 5, 6]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI83N0
  hpmem := by
    show  _ ∈ I83N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI83N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := PrimeIdeal_isPrime PI83N0
def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0], ![37, 2, -3, -1, -5]] i)))

def SI83N1: IdealEqSpanCertificate O ℤ timesTableO I83N1
 ![![83, 0, 0, 0, 0], ![37, 2, -3, -1, -5]]
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![41, 17, 1, 0, 0], ![25, 1, 0, 1, 0], ![46, 39, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]], ![![37, 2, -3, -1, -5], ![-3, 35, 0, 1, 3], ![3, -4, 37, -3, 3], ![-3, 4, -5, 29, -24], ![-2, -1, 1, 4, 42]]]
  hmulB := by decide
  f := ![![![-546181, 6962962, -5948, 197642, 589594], ![-113378, -16505214, 4150, 0, 0]], ![![-307969, 3926028, -3346, 111439, 332441], ![-63910, -9306375, 2324, 0, 0]], ![![-332771, 4241972, -3620, 120408, 359196], ![-69012, -10055301, 2525, 0, 0]], ![![-168246, 2144578, -1830, 60874, 181597], ![-34868, -5083575, 1278, 0, 0]], ![![-447432, 5703750, -4867, 161900, 482973], ![-92819, -13520343, 3392, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-41, -17, 83, 0, 0], ![-25, -1, 0, 83, 0], ![-46, -39, 0, 0, 83]], ![![5, 3, -3, -1, -5], ![-2, -1, 0, 1, 3], ![-19, -9, 37, -3, 3], ![7, 12, -5, 29, -24], ![-25, -20, 1, 4, 42]]]
  hle1 := by decide
  hle2 := by decide

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI83N1)

def MemCI83N1 : IdealMemCertificate O ℤ B I83N1
  ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![41, 17, 1, 0, 0], ![25, 1, 0, 1, 0], ![46, 39, 0, 0, 1]] ![220, -77, 85, 33, 456] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI83N1
 g := ![-302, -233, 85, 33, 456]
 hmem := by decide

def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [61, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 82], [0, 1]]
 g := ![![[75, 49], [56, 33], [28], [30], [54, 17], [1]],![[0, 34], [58, 50], [28], [30], [50, 66], [1]]]
 h' := ![![[73, 82], [70, 7], [16, 38], [8, 51], [26, 69], [22, 73], [0, 1]],![[0, 1], [0, 76], [51, 45], [79, 32], [0, 14], [39, 10], [73, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [75, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : PrimeIdeal O 83 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I83N1
  hcard := NI83N1
  P := [61, 10, 1]
  f := ofList [61, 10, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P83P1
  hneq := by decide
  hlen := by decide
  c := ![220, -77, 85, 33, 456]
  a := ![-3, 1, -3, -3, -12]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI83N1
  hpmem := by
    show  _ ∈ I83N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI83N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := PrimeIdeal_isPrime PI83N1
def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0], ![23, 1, 0, 0, 0]] i)))

def SI83N2: IdealEqSpanCertificate O ℤ timesTableO I83N2
 ![![83, 0, 0, 0, 0], ![23, 1, 0, 0, 0]]
 ![![83, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![76, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]], ![![23, 1, 0, 0, 0], ![0, 23, 1, 0, 0], ![0, 1, 23, 2, 0], ![3, -1, 2, 26, 12], ![0, 0, 0, -2, 20]]]
  hmulB := by decide
  f := ![![![1443142, 98748, 823343, 82336, 4992], ![-5203353, -2573, -2968080, -34528, 0]], ![![405864, 27754, 231530, 23154, 1404], ![-1463372, -664, -834648, -9711, 0]], ![![947046, 64795, 540330, 54034, 3276], ![-3414643, -1659, -1947844, -22659, 0]], ![![225476, 15424, 128647, 12865, 780], ![-812970, -385, -463762, -5395, 0]], ![![1321434, 90410, 753904, 75392, 4571], ![-4764526, -2320, -2717760, -31616, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-23, 83, 0, 0, 0], ![-52, 0, 83, 0, 0], ![-13, 0, 0, 83, 0], ![-76, 0, 0, 0, 83]], ![![0, 1, 0, 0, 0], ![-7, 23, 1, 0, 0], ![-15, 1, 23, 2, 0], ![-16, -1, 2, 26, 12], ![-18, 0, 0, -2, 20]]]
  hle1 := by decide
  hle2 := by decide

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulEqCertificate O ℤ timesTableO (I83N0) I83N1
  ![![83, 0, 0, 0, 0], ![31, 3, -3, -1, -5]] ![![83, 0, 0, 0, 0], ![37, 2, -3, -1, -5]]
  ![![83, 0, 0, 0, 0], ![-20, -69, 45, 15, 74]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![6889, 0, 0, 0, 0], ![3071, 166, -249, -83, -415]], ![![2573, 249, -249, -83, -415], ![1142, 180, -204, -68, -341]]]
 hmul := by decide
 f :=  ![![![![-30567898057591353553760, 389791369481867019183444, -230478625858829715364, 11056127176399989999843, 33015084826238147436383], ![-6347826561411569652502, -923999391032610158715625, 2330864608593032339, 0, 0]], ![![-1423852508520324, -27310350825, 0, 0, 0], ![-4482, 0, 0, 0, 0]]], ![![![7365603886356488014721, -93923658751892813704698, 55535851995760854067, -2664071083497985075680, -7955275061647148811873], ![1529564640086155129057, 222645779986518857588125, -561642327754361501, 0, 0]], ![![343089784930476, 6580669230, 0, 0, 0], ![1080, 0, 0, 0, 0]]]]
 g :=  ![![![![83, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![37, 2, -3, -1, -5], ![0, 0, 0, 0, 0]]], ![![![31, 3, -3, -1, -5], ![0, 0, 0, 0, 0]], ![![14, 3, -3, -1, -5], ![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI83N1 : IdealMulEqCertificate O ℤ timesTableO (I83N0*I83N1) I83N2
  ![![83, 0, 0, 0, 0], ![-20, -69, 45, 15, 74]] ![![83, 0, 0, 0, 0], ![23, 1, 0, 0, 0]]
  ![![83, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI83N0
 hI2 := rfl
 M :=  ![![![6889, 0, 0, 0, 0], ![1909, 83, 0, 0, 0]], ![![-1660, -5727, 3735, 1245, 6142], ![-415, -1577, 996, 332, 1660]]]
 hmul := by decide
 f :=  ![![![![-59837953892472, -2853419662073, -334810977676, -32430476456, -1959244016], ![215935197282727, 858368923420, 1169731454208, 13548435992, 0]], ![![486776, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![83, 0, 0, 0, 0]], ![![23, 1, 0, 0, 0]]], ![![![-20, -69, 45, 15, 74]], ![![-5, -19, 12, 4, 20]]]]
 hle1 := by decide
 hle2 := by decide

def PBC83 : PrimesBelowPCertificate 83 ![I83N0, I83N1, I83N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI83N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp89 : Fact (Nat.Prime 89) := by decide
def I89N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0]] i)))

def SI89N: IdealEqSpanCertificate O ℤ timesTableO I89N
 ![![89, 0, 0, 0, 0]]
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI89N : Nat.card (O ⧸ I89N) = 5584059449 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI89N)

def MemCI89N : IdealMemCertificate O ℤ B I89N
  ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]] ![-109723067406, 124681331404, -81383727278, -204805251934, -668792918130] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI89N
 g := ![-1232843454, 1400913836, -914423902, -2301182606, -7514527170]
 hmem := by decide

def P89P : CertificateIrreducibleZModOfList' 89 5 2 6 [6, 63, 8, 51, 83, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 2, 35, 14, 67], [69, 6, 4, 62, 1], [50, 79, 7, 49, 59], [79, 1, 43, 53, 51], [0, 1]]
 g := ![![[32, 85, 17, 0, 36], [20, 75, 22, 45], [13, 46, 25, 40], [7, 25, 73, 49, 36], [1], []],![[54, 34, 64, 16, 52, 47, 80, 34], [76, 86, 25, 25], [71, 57, 36, 36], [29, 11, 36, 0, 87, 48, 35, 40], [12, 0, 32, 65, 70, 69, 70, 5], [18, 71, 63, 39]],![[38, 35, 45, 27, 13, 23, 3, 18], [81, 39, 74, 44], [51, 71, 62, 44], [17, 46, 24, 57, 5, 13, 29, 64], [9, 55, 78, 31, 52, 65, 76, 45], [85, 42, 41, 1]],![[7, 32, 9, 16, 0, 55, 27, 14], [39, 22, 26, 80], [57, 2, 86, 68], [36, 8, 40, 55, 9, 45, 59, 6], [17, 21, 41, 53, 16, 72, 37, 7], [10, 33, 57, 10]],![[59, 21, 65, 5, 16, 80, 29, 27], [51, 86, 61, 40], [4, 68, 39, 20], [16, 67, 23, 35, 43, 76, 67, 26], [24, 88, 54, 42, 51, 16, 63, 82], [45, 82, 8, 20]]]
 h' := ![![[75, 2, 35, 14, 67], [83, 55, 58, 18, 83], [84, 46, 69, 74, 32], [47, 68, 22, 39, 60], [83, 26, 81, 38, 6], [0, 0, 1], [0, 1]],![[69, 6, 4, 62, 1], [76, 31, 79, 50, 15], [40, 50, 8, 57, 84], [56, 49, 32, 74, 6], [3, 11, 39, 63, 58], [88, 75, 81, 22, 51], [75, 2, 35, 14, 67]],![[50, 79, 7, 49, 59], [66, 40, 33, 15, 75], [75, 40, 50, 62, 20], [84, 86, 58, 35, 20], [26, 43, 85, 31, 81], [68, 27, 42, 9, 32], [69, 6, 4, 62, 1]],![[79, 1, 43, 53, 51], [72, 4, 26, 58, 15], [22, 65, 62, 51, 13], [50, 26, 44, 58, 54], [85, 20, 24, 61, 31], [37, 41, 79, 68, 35], [50, 79, 7, 49, 59]],![[0, 1], [14, 48, 71, 37, 79], [63, 66, 78, 23, 29], [40, 38, 22, 61, 38], [17, 78, 38, 74, 2], [8, 35, 64, 79, 60], [79, 1, 43, 53, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 46, 73, 22], [], [], []]
 b := ![[], [71, 5, 32, 2, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N : PrimeIdeal O 89 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I89N
  hcard := NI89N
  P := [6, 63, 8, 51, 83, 1]
  f := ofList [6, 63, 8, 51, 83, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P89P
  hneq := by decide
  hlen := by decide
  c := ![-109723067406, 124681331404, -81383727278, -204805251934, -668792918130]
  a := ![-21, 0, -22, -26, -74]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI89N
  hpmem := by
    show  _ ∈ I89N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI89N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI89N : Ideal.IsPrime I89N := PrimeIdeal_isPrime PI89N
def PBC89 : PrimesBelowPCertificate 89 ![I89N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI89N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I89N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp97 : Fact (Nat.Prime 97) := by decide
def I97N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0]] i)))

def SI97N: IdealEqSpanCertificate O ℤ timesTableO I97N
 ![![97, 0, 0, 0, 0]]
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI97N : Nat.card (O ⧸ I97N) = 8587340257 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI97N)

def MemCI97N : IdealMemCertificate O ℤ B I97N
  ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]] ![-3139773241003, -274015443463, -1370202835516, 3721792867789, -650742615720] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI97N
 g := ![-32368796299, -2824901479, -14125802428, 38368998637, -6708686760]
 hmem := by decide

def P97P : CertificateIrreducibleZModOfList' 97 5 2 6 [2, 4, 18, 26, 16, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 13, 70, 43, 35], [65, 79, 69, 51, 96], [83, 59, 89, 77, 88], [48, 42, 63, 23, 72], [0, 1]]
 g := ![![[9, 78, 80, 15, 94], [29, 28, 77, 1], [58, 2], [20, 6, 63, 35], [81, 1], []],![[91, 39, 52, 2, 49, 47, 6, 96], [27, 29, 94, 44], [45, 7, 94, 16], [32, 20, 34, 36], [18, 31, 70, 64], [82, 67, 8, 13, 38, 92, 93, 1]],![[68, 33, 55, 3, 47, 68, 90, 3], [86, 73, 69, 70], [47, 83, 87, 70], [8, 34, 5, 6], [52, 8, 48, 8], [68, 64, 78, 63, 85, 8, 72, 96]],![[17, 73, 2, 19, 21, 75, 52, 50], [5, 19, 44, 48], [72, 49, 41, 43], [33, 60, 82, 95], [84, 86, 96, 25], [78, 65, 96, 57, 39, 69, 14, 47]],![[9, 58, 50, 32, 78, 81, 23, 35], [28, 3, 27, 2], [79, 71, 88, 73], [7, 64, 22, 27], [78, 73, 58, 31], [54, 49, 96, 60, 19, 38, 88, 89]]]
 h' := ![![[79, 13, 70, 43, 35], [37, 20, 5, 46, 26], [80, 40, 38, 2, 96], [14, 93, 73, 83], [32, 62, 90, 10, 36], [0, 0, 0, 1], [0, 1]],![[65, 79, 69, 51, 96], [86, 14, 68, 79, 91], [25, 23, 90, 67, 74], [42, 43, 34, 29, 93], [94, 78, 47, 30, 91], [18, 49, 21, 32, 8], [79, 13, 70, 43, 35]],![[83, 59, 89, 77, 88], [47, 96, 42, 0, 26], [92, 19, 96, 7, 78], [63, 53, 30, 78, 78], [46, 47, 48, 18, 54], [76, 79, 69, 80, 69], [65, 79, 69, 51, 96]],![[48, 42, 63, 23, 72], [69, 70, 25, 54, 93], [51, 45, 0, 82, 57], [96, 27, 14, 96, 72], [29, 60, 39, 67, 80], [10, 9, 13, 69, 5], [83, 59, 89, 77, 88]],![[0, 1], [35, 91, 54, 15, 55], [24, 67, 67, 36, 83], [52, 75, 43, 5, 48], [39, 44, 67, 69, 30], [1, 57, 91, 12, 15], [48, 42, 63, 23, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 30, 19, 53], [], [], []]
 b := ![[], [53, 37, 65, 9, 65], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N : PrimeIdeal O 97 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I97N
  hcard := NI97N
  P := [2, 4, 18, 26, 16, 1]
  f := ofList [2, 4, 18, 26, 16, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P97P
  hneq := by decide
  hlen := by decide
  c := ![-3139773241003, -274015443463, -1370202835516, 3721792867789, -650742615720]
  a := ![-27, 9, -22, -27, -108]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI97N
  hpmem := by
    show  _ ∈ I97N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI97N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI97N : Ideal.IsPrime I97N := PrimeIdeal_isPrime PI97N
def PBC97 : PrimesBelowPCertificate 97 ![I97N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI97N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I97N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp101 : Fact (Nat.Prime 101) := by decide
def I101N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0]] i)))

def SI101N: IdealEqSpanCertificate O ℤ timesTableO I101N
 ![![101, 0, 0, 0, 0]]
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI101N : Nat.card (O ⧸ I101N) = 10510100501 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI101N)

def MemCI101N : IdealMemCertificate O ℤ B I101N
  ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]] ![-290132643430, 11271793011, -135742944247, 252653965208, -236204272665] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI101N
 g := ![-2872600430, 111601911, -1343989547, 2501524408, -2338656165]
 hmem := by decide

def P101P : CertificateIrreducibleZModOfList' 101 5 2 6 [10, 81, 52, 25, 29, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 76, 51, 66, 59], [40, 13, 5, 88, 21], [40, 35, 82, 73, 4], [70, 77, 64, 76, 17], [0, 1]]
 g := ![![[28, 98, 22, 23, 78], [0, 64, 4, 24], [77, 50, 52, 43, 76], [50, 78, 24, 64], [72, 1], []],![[56, 42, 95, 41, 20, 50, 99, 94], [46, 88, 11, 87], [84, 75, 49, 24, 6, 32, 30, 40], [54, 53, 62, 37], [33, 22, 13, 87], [7, 32, 40, 47, 80, 61, 94, 46]],![[64, 7, 42, 28, 77, 98, 92, 77], [9, 0, 13, 19], [87, 87, 34, 83, 13, 88, 75, 92], [48, 2, 7, 30], [30, 81, 52, 47], [23, 90, 64, 30, 38, 79, 62, 70]],![[15, 69, 10, 78, 5, 83, 30, 20], [74, 24, 49, 20], [43, 92, 20, 17, 50, 6, 63, 65], [12, 24, 43, 45], [98, 79, 69, 1], [82, 22, 21, 37, 25, 9, 32, 64]],![[98, 9, 20, 67, 50, 63, 5, 43], [5, 60, 90, 16], [7, 98, 63, 57, 76, 15, 4, 17], [55, 41, 96, 79], [17, 93, 32, 71], [73, 27, 60, 20, 100, 65, 74, 65]]]
 h' := ![![[23, 76, 51, 66, 59], [30, 18, 8, 80, 49], [38, 6, 79, 77, 78], [73, 6, 52, 76, 50], [88, 16, 13, 67, 8], [0, 0, 0, 1], [0, 1]],![[40, 13, 5, 88, 21], [75, 98, 58, 57, 57], [63, 71, 97, 74, 84], [75, 62, 3, 58, 50], [98, 14, 92, 15, 21], [78, 40, 11, 33, 17], [23, 76, 51, 66, 59]],![[40, 35, 82, 73, 4], [44, 19, 10, 8, 77], [29, 93, 86, 84, 25], [5, 23, 90, 52, 32], [9, 22, 96, 74, 38], [39, 47, 6, 6, 59], [40, 13, 5, 88, 21]],![[70, 77, 64, 76, 17], [37, 17, 32, 40, 56], [75, 41, 76, 24, 11], [0, 80, 55, 67, 71], [25, 42, 48, 99, 67], [55, 43, 54, 49, 1], [40, 35, 82, 73, 4]],![[0, 1], [32, 50, 94, 17, 64], [48, 92, 66, 44, 4], [76, 31, 2, 50, 100], [90, 7, 54, 48, 68], [82, 72, 30, 12, 24], [70, 77, 64, 76, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92, 37, 96, 55], [], [], []]
 b := ![[], [83, 26, 23, 54, 47], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N : PrimeIdeal O 101 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I101N
  hcard := NI101N
  P := [10, 81, 52, 25, 29, 1]
  f := ofList [10, 81, 52, 25, 29, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P101P
  hneq := by decide
  hlen := by decide
  c := ![-290132643430, 11271793011, -135742944247, 252653965208, -236204272665]
  a := ![11, -11, 11, 2, 51]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI101N
  hpmem := by
    show  _ ∈ I101N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI101N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI101N : Ideal.IsPrime I101N := PrimeIdeal_isPrime PI101N
def PBC101 : PrimesBelowPCertificate 101 ![I101N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI101N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I101N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp103 : Fact (Nat.Prime 103) := by decide
def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0], ![29, 13, -3, -1, -5]] i)))

def SI103N0: IdealEqSpanCertificate O ℤ timesTableO I103N0
 ![![103, 0, 0, 0, 0], ![29, 13, -3, -1, -5]]
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![50, 94, 1, 0, 0], ![19, 88, 0, 1, 0], ![84, 47, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]], ![![29, 13, -3, -1, -5], ![-3, 27, 11, 1, 3], ![3, 7, 29, 19, 3], ![30, -7, 17, 54, 108], ![-2, -1, 1, -18, 1]]]
  hmulB := by decide
  f := ![![![-275960, 2101005, 879047, 87889, 243723], ![149247, -8075509, -43569, 0, 0]], ![![-1560601, 11882300, 4971577, 497143, 1378375], ![843776, -45671024, -246891, 0, 0]], ![![-1557895, 11861687, 4962942, 496273, 1375983], ![842313, -45591807, -246421, 0, 0]], ![![-1384232, 10539433, 4409715, 440956, 1222599], ![748419, -40509561, -218973, 0, 0]], ![![-937170, 7135463, 2985476, 298528, 827731], ![506727, -27426028, -148191, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-50, -94, 103, 0, 0], ![-19, -88, 0, 103, 0], ![-84, -47, 0, 0, 103]], ![![6, 6, -3, -1, -5], ![-8, -12, 11, 1, 3], ![-20, -44, 29, 19, 3], ![-106, -111, 17, 54, 108], ![2, 14, 1, -18, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI103N0)

def MemCI103N0 : IdealMemCertificate O ℤ B I103N0
  ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![50, 94, 1, 0, 0], ![19, 88, 0, 1, 0], ![84, 47, 0, 0, 1]] ![18850, -10548, 11194, 7840, 61801] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI103N0
 g := ![-57098, -45217, 11194, 7840, 61801]
 hmem := by decide

def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [48, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 102], [0, 1]]
 g := ![![[42, 58], [7, 61], [84, 82], [26], [23], [44, 1]],![[19, 45], [13, 42], [87, 21], [26], [23], [88, 102]]]
 h' := ![![[44, 102], [76, 77], [88, 24], [26, 59], [55, 51], [51, 34], [0, 1]],![[0, 1], [65, 26], [11, 79], [47, 44], [33, 52], [2, 69], [44, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [82, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : PrimeIdeal O 103 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I103N0
  hcard := NI103N0
  P := [48, 59, 1]
  f := ofList [48, 59, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P103P0
  hneq := by decide
  hlen := by decide
  c := ![18850, -10548, 11194, 7840, 61801]
  a := ![-30, 9, -25, -31, -119]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI103N0
  hpmem := by
    show  _ ∈ I103N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI103N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := PrimeIdeal_isPrime PI103N0
def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0], ![-4, 35, -3, -1, -5]] i)))

def SI103N1: IdealEqSpanCertificate O ℤ timesTableO I103N1
 ![![103, 0, 0, 0, 0], ![-4, 35, -3, -1, -5]]
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![67, 78, 1, 0, 0], ![65, 82, 0, 1, 0], ![30, 74, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]], ![![-4, 35, -3, -1, -5], ![-3, -6, 33, 1, 3], ![3, 29, -4, 63, 3], ![96, -29, 61, 87, 372], ![-2, -1, 1, -62, -98]]]
  hmulB := by decide
  f := ![![![-4655853, -7597564, 49383186, 1510025, 4305547], ![-4062835, -154514523, -80649, 0, 0]], ![![-2886717, -4710647, 30618549, 936279, 2669529], ![-2518968, -95802051, -50058, 0, 0]], ![![-5214106, -8508518, 55304398, 1691107, 4821797], ![-4550006, -173041347, -90360, 0, 0]], ![![-5236325, -8544783, 55540077, 1698315, 4842346], ![-4569376, -173778759, -90747, 0, 0]], ![![-3430028, -5597211, 36381243, 1112479, 3171954], ![-2993153, -113832888, -59454, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-67, -78, 103, 0, 0], ![-65, -82, 0, 103, 0], ![-30, -74, 0, 0, 103]], ![![4, 7, -3, -1, -5], ![-23, -28, 33, 1, 3], ![-38, -49, -4, 63, 3], ![-202, -383, 61, 87, 372], ![67, 119, 1, -62, -98]]]
  hle1 := by decide
  hle2 := by decide

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI103N1)

def MemCI103N1 : IdealMemCertificate O ℤ B I103N1
  ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![67, 78, 1, 0, 0], ![65, 82, 0, 1, 0], ![30, 74, 0, 0, 1]] ![3537, -2184, 1836, 1080, 11136] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI103N1
 g := ![-5085, -10272, 1836, 1080, 11136]
 hmem := by decide

def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [89, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 102], [0, 1]]
 g := ![![[97, 64], [58, 13], [101, 97], [82], [30], [19, 1]],![[77, 39], [99, 90], [90, 6], [82], [30], [38, 102]]]
 h' := ![![[19, 102], [91, 8], [75, 42], [24, 71], [3, 44], [60, 66], [0, 1]],![[0, 1], [37, 95], [49, 61], [34, 32], [15, 59], [78, 37], [19, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [45, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : PrimeIdeal O 103 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I103N1
  hcard := NI103N1
  P := [89, 84, 1]
  f := ofList [89, 84, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P103P1
  hneq := by decide
  hlen := by decide
  c := ![3537, -2184, 1836, 1080, 11136]
  a := ![-16, 4, -14, -16, -60]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI103N1
  hpmem := by
    show  _ ∈ I103N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI103N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := PrimeIdeal_isPrime PI103N1
def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0], ![34, 1, 0, 0, 0]] i)))

def SI103N2: IdealEqSpanCertificate O ℤ timesTableO I103N2
 ![![103, 0, 0, 0, 0], ![34, 1, 0, 0, 0]]
 ![![103, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![65, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]], ![![34, 1, 0, 0, 0], ![0, 34, 1, 0, 0], ![0, 1, 34, 2, 0], ![3, -1, 2, 37, 12], ![0, 0, 0, -2, 31]]]
  hmulB := by decide
  f := ![![![-56063747, -3979210, -98890369, -5808788, 3024], ![169842468, -1754193, 299632768, -25956, 0]], ![![-18688766, -1326471, -32964907, -1936348, 1008], ![56616732, -584731, 99881984, -8652, 0]], ![![-44049046, -3126454, -77697711, -4563938, 2376], ![133444500, -1378242, 235420096, -20394, 0]], ![![-35373568, -2510679, -62395137, -3665070, 1908], ![107162550, -1106855, 189054080, -16377, 0]], ![![-34835756, -2472524, -61446443, -3609344, 1879], ![105533274, -1089971, 186179584, -16128, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-34, 103, 0, 0, 0], ![-80, 0, 103, 0, 0], ![-65, 0, 0, 103, 0], ![-64, 0, 0, 0, 103]], ![![0, 1, 0, 0, 0], ![-12, 34, 1, 0, 0], ![-28, 1, 34, 2, 0], ![-32, -1, 2, 37, 12], ![-18, 0, 0, -2, 31]]]
  hle1 := by decide
  hle2 := by decide

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulEqCertificate O ℤ timesTableO (I103N0) I103N1
  ![![103, 0, 0, 0, 0], ![29, 13, -3, -1, -5]] ![![103, 0, 0, 0, 0], ![-4, 35, -3, -1, -5]]
  ![![103, 0, 0, 0, 0], ![-32, 53, -34, -15, -54]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![10609, 0, 0, 0, 0], ![-412, 3605, -309, -103, -515]], ![![2987, 1339, -309, -103, -515], ![-250, 884, 288, 18, 3]]]
 hmul := by decide
 f :=  ![![![![19690128003536182481209, 32199224720821506131526, -208743846024177257645582, -6175481590688396154245, -18187415475970143561320], ![17199577186967756034743, 653097759808899659306679, 2800338339102227199, 0, 0]], ![![96390549258444, 9560080, 0, 0, 0], ![721, 0, 0, 0, 0]]], ![![![-6118758985158769766681, -10005993640076385039388, 64867698332263219200112, 1919047121680524131841, 5651787120958392378892], ![-5344813778498063504233, -202951843954498116882261, -870212492818183224, 0, 0]], ![![-29953616312376, -2970820, 0, 0, 0], ![-224, 0, 0, 0, 0]]]]
 g :=  ![![![![103, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![28, -18, 31, 14, 49], ![103, 0, 0, 0, 0]]], ![![![61, -40, 31, 14, 49], ![103, 0, 0, 0, 0]], ![![10, -12, 16, 6, 21], ![40, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI103N1 : IdealMulEqCertificate O ℤ timesTableO (I103N0*I103N1) I103N2
  ![![103, 0, 0, 0, 0], ![-32, 53, -34, -15, -54]] ![![103, 0, 0, 0, 0], ![34, 1, 0, 0, 0]]
  ![![103, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI103N0
 hI2 := rfl
 M :=  ![![![10609, 0, 0, 0, 0], ![3502, 103, 0, 0, 0]], ![![-3296, 5459, -3502, -1545, -5562], ![-1133, 1751, -1133, -515, -1854]]]
 hmul := by decide
 f :=  ![![![![-29250703835599, -871570532192, -477178930236, -28073888480, 88668], ![88612426392680, -8425931548, 1445819331460, -760770, 0]], ![![66, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![103, 0, 0, 0, 0]], ![![34, 1, 0, 0, 0]]], ![![![-32, 53, -34, -15, -54]], ![![-11, 17, -11, -5, -18]]]]
 hle1 := by decide
 hle2 := by decide

def PBC103 : PrimesBelowPCertificate 103 ![I103N0, I103N1, I103N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI103N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp107 : Fact (Nat.Prime 107) := by decide
def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -10, 10, 4, 18]] i)))

def SI107N0: IdealEqSpanCertificate O ℤ timesTableO I107N0
 ![![-7, -10, 10, 4, 18]]
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![46, 23, 1, 0, 0], ![6, 80, 0, 1, 0], ![50, 64, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![-7, -10, 10, 4, 18], ![12, -1, -2, -4, -6], ![-12, 14, -9, -4, -30], ![-12, -8, 4, 17, 24], ![12, 0, 0, -4, 5]]]
  hmulB := by decide
  f := ![![![43, 46, 50, 28, 66]], ![![84, 65, 102, 52, 138]], ![![38, 35, 45, 24, 60]], ![![66, 52, 80, 41, 108]], ![![70, 60, 84, 44, 113]]]
  g := ![![![-13, -16, 10, 4, 18], ![4, 7, -2, -4, -6], ![18, 23, -9, -4, -30], ![-14, -28, 4, 17, 24], ![-2, 0, 0, -4, 5]]]
  hle1 := by decide
  hle2 := by decide

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI107N0)

def MemCI107N0 : IdealMemCertificate O ℤ B I107N0
  ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![46, 23, 1, 0, 0], ![6, 80, 0, 1, 0], ![50, 64, 0, 0, 1]] ![-525, 685, -423, -2023, -4414] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI107N0
 g := ![2353, 4250, -423, -2023, -4414]
 hmem := by decide

def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [15, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 106], [0, 1]]
 g := ![![[83, 47], [98, 83], [34], [80, 42], [64], [39, 1]],![[97, 60], [18, 24], [34], [6, 65], [64], [78, 106]]]
 h' := ![![[39, 106], [28, 49], [19, 61], [84, 81], [42, 91], [57, 8], [0, 1]],![[0, 1], [13, 58], [44, 46], [33, 26], [60, 16], [48, 99], [39, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [51, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : PrimeIdeal O 107 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I107N0
  hcard := NI107N0
  P := [15, 68, 1]
  f := ofList [15, 68, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P107P0
  hneq := by decide
  hlen := by decide
  c := ![-525, 685, -423, -2023, -4414]
  a := ![2, -5, 1, -7, 7]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI107N0
  hpmem := by
    show  _ ∈ I107N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI107N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := PrimeIdeal_isPrime PI107N0
def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, -50, -86, -44, -116]] i)))

def SI107N1: IdealEqSpanCertificate O ℤ timesTableO I107N1
 ![![-61, -50, -86, -44, -116]]
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![27, 53, 1, 0, 0], ![87, 54, 0, 1, 0], ![13, 103, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![-61, -50, -86, -44, -116], ![-132, -103, -138, -72, -180], ![-216, -198, -247, -132, -324], ![-132, -114, -162, -85, -216], ![52, 48, 68, 36, 91]]]
  hmulB := by decide
  f := ![![![17, -10, 10, -4, 28]], ![![-12, 31, -18, -48, -132]], ![![-3, 13, -7, -24, -60]], ![![9, 6, 0, -25, -36]], ![![-9, 29, -16, -48, -125]]]
  g := ![![![71, 176, -86, -44, -116], ![114, 277, -138, -72, -180], ![207, 499, -247, -132, -324], ![135, 330, -162, -85, -216], ![-57, -139, 68, 36, 91]]]
  hle1 := by decide
  hle2 := by decide

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI107N1)

def MemCI107N1 : IdealMemCertificate O ℤ B I107N1
  ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![27, 53, 1, 0, 0], ![87, 54, 0, 1, 0], ![13, 103, 0, 0, 1]] ![8502, -9039, 6309, 14325, 48710] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI107N1
 g := ![-19078, -57328, 6309, 14325, 48710]
 hmem := by decide

def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [42, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 106], [0, 1]]
 g := ![![[7, 79], [33, 11], [25], [6, 42], [99], [27, 1]],![[0, 28], [9, 96], [25], [70, 65], [99], [54, 106]]]
 h' := ![![[27, 106], [5, 87], [73, 92], [69, 102], [45, 16], [43, 45], [0, 1]],![[0, 1], [0, 20], [96, 15], [41, 5], [49, 91], [81, 62], [27, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [71, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : PrimeIdeal O 107 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I107N1
  hcard := NI107N1
  P := [42, 80, 1]
  f := ofList [42, 80, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P107P1
  hneq := by decide
  hlen := by decide
  c := ![8502, -9039, 6309, 14325, 48710]
  a := ![-28, 3, -25, -37, -109]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI107N1
  hpmem := by
    show  _ ∈ I107N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI107N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := PrimeIdeal_isPrime PI107N1
def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 0, 0, 0, 2]] i)))

def SI107N2: IdealEqSpanCertificate O ℤ timesTableO I107N2
 ![![1, 0, 0, 0, 2]]
 ![![107, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![1, 0, 0, 0, 2], ![0, 1, 0, -4, -6], ![-12, 4, -7, 0, -30], ![0, -10, 2, 25, 48], ![8, 0, 4, -8, 5]]]
  hmulB := by decide
  f := ![![![-5, -192, 88, 16, 146]], ![![-1, -55, 24, 4, 40]], ![![-2, -4, 1, 0, 2]], ![![-1, -14, 6, 1, 10]], ![![-2, -96, 44, 8, 73]]]
  g := ![![![-1, 0, 0, 0, 2], ![3, 1, 0, -4, -6], ![14, 4, -7, 0, -30], ![-23, -10, 2, 25, 48], ![-2, 0, 4, -8, 5]]]
  hle1 := by decide
  hle2 := by decide

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulEqCertificate O ℤ timesTableO (I107N0) I107N1
  ![![-7, -10, 10, 4, 18]] ![![-61, -50, -86, -44, -116]]
  ![![-5, -192, 88, 16, 146]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-5, -192, 88, 16, 146]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI107N1 : IdealMulEqCertificate O ℤ timesTableO (I107N0*I107N1) I107N2
  ![![-5, -192, 88, 16, 146]] ![![1, 0, 0, 0, 2]]
  ![![107, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI107N0
 hI2 := rfl
 M :=  ![![![107, 0, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC107 : PrimesBelowPCertificate 107 ![I107N0, I107N1, I107N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI107N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
