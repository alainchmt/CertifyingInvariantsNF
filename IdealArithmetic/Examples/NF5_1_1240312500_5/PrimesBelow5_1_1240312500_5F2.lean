
import IdealArithmetic.Examples.NF5_1_1240312500_5.PrimesBelow5_1_1240312500_5F1

open Classical Polynomial

noncomputable section 
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}
def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0], ![-287, -199, -113, -137, 354]] i)))

def SI67N0: IdealEqSpanCertificate O ℤ timesTableO I67N0
 ![![67, 0, 0, 0, 0], ![-287, -199, -113, -137, 354]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![66, 53, 54, 21, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![0, 0, 0, 0, 67]], ![![-287, -199, -113, -137, 354], ![-993, -368, -246, -319, 792], ![-2409, -293, 39, -63, 198], ![321, -1469, -316, -175, 684], ![-1176, -920, -280, -295, 841]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![258, 179, 102, 123, -317], ![60, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-66, -53, -54, -21, 67]], ![![-353, -283, -287, -113, 354], ![-795, -632, -642, -253, 792], ![-231, -161, -159, -63, 198], ![-669, -563, -556, -217, 684], ![-846, -679, -682, -268, 841]]]
  hle1 := by decide
  hle2 := by decide

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI67N0)

def MemCI67N0 : IdealMemCertificate O ℤ B I67N0
  ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![66, 53, 54, 21, 1]] ![-105760753911, -89371531234, -62634157334, -115255766448, 240332114568] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI67N0
 g := ![-238323586797, -191447367214, -194635348418, -77048211528, 240332114568]
 hmem := by decide

def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [29, 49, 53, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 49, 42, 30], [65, 52, 43, 26], [64, 32, 49, 11], [0, 1]]
 g := ![![[3, 60, 52, 17], [47, 29, 10, 21], [11, 24, 35], [34, 23, 22], [1], []],![[42, 64, 3, 49, 58, 43], [28, 60, 24, 9, 54, 31], [37, 14, 14], [42, 41, 60], [15, 7, 25], [33, 53, 29]],![[0, 56, 29, 52, 4, 10], [35, 44, 31, 40, 20, 65], [39, 66, 10], [16, 38, 15], [50, 48, 47], [57, 9, 6]],![[15, 39, 18, 46, 13, 32], [21, 30, 51, 41, 65, 57], [4, 38, 33], [12, 15, 40], [8, 52, 17], [8, 63, 54]]]
 h' := ![![[47, 49, 42, 30], [44, 14, 59, 33], [3, 29, 65, 17], [56, 40, 32, 13], [38, 18, 14, 42], [0, 0, 1], [0, 1]],![[65, 52, 43, 26], [57, 65, 26, 48], [39, 21, 21, 21], [24, 2, 50, 9], [6, 53, 0, 23], [46, 45, 23, 5], [47, 49, 42, 30]],![[64, 32, 49, 11], [13, 65, 19, 50], [25, 5, 22, 6], [34, 11, 65, 55], [30, 64, 50, 45], [26, 21, 35, 28], [65, 52, 43, 26]],![[0, 1], [18, 57, 30, 3], [40, 12, 26, 23], [42, 14, 54, 57], [51, 66, 3, 24], [45, 1, 8, 34], [64, 32, 49, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [42, 37, 16], []]
 b := ![[], [], [39, 14, 30, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : PrimeIdeal O 67 where 
  r := 5
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I67N0
  hcard := NI67N0
  P := [29, 49, 53, 25, 1]
  f := ofList [29, 49, 53, 25, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P67P0
  hneq := by decide
  hlen := by decide
  c := ![-105760753911, -89371531234, -62634157334, -115255766448, 240332114568]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI67N0
  hpmem := by 
    show  _ ∈ I67N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI67N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := PrimeIdeal_isPrime PI67N0
def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0], ![-17, 1, 0, 0, 0]] i)))

def SI67N1: IdealEqSpanCertificate O ℤ timesTableO I67N1
 ![![67, 0, 0, 0, 0], ![-17, 1, 0, 0, 0]] 
 ![![67, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![0, 0, 0, 0, 67]], ![![-17, 1, 0, 0, 0], ![0, -17, 1, 0, 0], ![0, 1, -17, 2, 0], ![15, -70, -41, -68, 126], ![3, -27, -16, -20, 34]]]
  hmulB := by decide
  f := ![![![-27185898, 50558562, -945840599, 111353196, -54054], ![-107119064, -26533072, -3729354804, 28743, 0]], ![![-20912246, 38891189, -727569550, 85656288, -41580], ![-82399346, -20410076, -2868733908, 22110, 0]], ![![-18820985, 35002068, -654812534, 77090652, -37422], ![-74159268, -18369054, -2581860276, 19899, 0]], ![![-12547335, 23334727, -436541851, 51393787, -24948], ![-49439558, -12246017, -1721240820, 13266, 0]], ![![-23534064, 43767110, -818787384, 96395304, -46793], ![-92729948, -22968942, -3228396696, 24882, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-50, 67, 0, 0, 0], ![-46, 0, 67, 0, 0], ![-31, 0, 0, 67, 0], ![-58, 0, 0, 0, 67]], ![![-1, 1, 0, 0, 0], ![12, -17, 1, 0, 0], ![10, 1, -17, 2, 0], ![3, -70, -41, -68, 126], ![11, -27, -16, -20, 34]]]
  hle1 := by decide
  hle2 := by decide

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulEqCertificate O ℤ timesTableO (I67N0) I67N1
  ![![67, 0, 0, 0, 0], ![-287, -199, -113, -137, 354]] ![![67, 0, 0, 0, 0], ![-17, 1, 0, 0, 0]]
  ![![67, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4489, 0, 0, 0, 0], ![-1139, 67, 0, 0, 0]], ![![-19229, -13333, -7571, -9179, 23718], ![3886, 3015, 1675, 2010, -5226]]]
 hmul := by decide
 f :=  ![![![![-7118584805739944, 13544013304776225, -253721722248005526, 29862179283857688, -117092393730], ![-28055544006449478, -7117170593261535, -1000380889059362838, 62262764421, 0]], ![![231816, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![67, 0, 0, 0, 0]], ![![-17, 1, 0, 0, 0]]], ![![![-287, -199, -113, -137, 354]], ![![58, 45, 25, 30, -78]]]]
 hle1 := by decide
 hle2 := by decide

def PBC67 : PrimesBelowPCertificate 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI67N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}
def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0], ![-180, -71, -54, -68, 177]] i)))

def SI71N0: IdealEqSpanCertificate O ℤ timesTableO I71N0
 ![![71, 0, 0, 0, 0], ![-180, -71, -54, -68, 177]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![11, 53, 52, 1, 0], ![0, 34, 65, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]], ![![-180, -71, -54, -68, 177], ![-489, -253, -115, -180, 459], ![-1323, -397, -217, -230, 729], ![-387, -2435, -1258, -1552, 3870], ![-930, -1227, -643, -801, 2052]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1875, 4047, -1181, 448, -642], ![-9869, 3905, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![1486, 3055, -855, 367, -564], ![-7333, 2915, 0, 0, 0]], ![![1050, 1998, -519, 272, -457], ![-4666, 1870, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-11, -53, -52, 71, 0], ![0, -34, -65, 0, 71]], ![![8, -35, -113, -68, 177], ![21, -89, -290, -180, 459], ![17, -183, -502, -230, 729], ![235, -729, -2424, -1552, 3870], ![111, -402, -1301, -801, 2052]]]
  hle1 := by decide
  hle2 := by decide

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI71N0)

def MemCI71N0 : IdealMemCertificate O ℤ B I71N0
  ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![11, 53, 52, 1, 0], ![0, 34, 65, 0, 1]] ![38569189, 184135403, 126157147, 176003972, -398803482] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI71N0
 g := ![-26724993, 62186525, 237974323, 176003972, -398803482]
 hmem := by decide

def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [42, 32, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 9, 10], [21, 61, 61], [0, 1]]
 g := ![![[54, 46, 37], [21, 2, 58], [39, 62, 49], [8, 57], [25, 1], []],![[16, 17, 25, 48], [57, 70, 52, 5], [27, 50, 15, 40], [37, 64], [55, 29], [53, 29]],![[60, 54, 5, 26], [45, 28, 37, 41], [22, 3, 24, 42], [50, 5], [2, 10], [2, 29]]]
 h' := ![![[4, 9, 10], [41, 50, 26], [66, 20, 49], [31, 64, 7], [15, 10, 25], [0, 0, 1], [0, 1]],![[21, 61, 61], [7, 43, 27], [60, 11, 65], [11, 65, 2], [43, 40, 63], [62, 69, 61], [4, 9, 10]],![[0, 1], [7, 49, 18], [16, 40, 28], [40, 13, 62], [62, 21, 54], [2, 2, 9], [21, 61, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 5], []]
 b := ![[], [50, 46, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : PrimeIdeal O 71 where 
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I71N0
  hcard := NI71N0
  P := [42, 32, 46, 1]
  f := ofList [42, 32, 46, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P71P0
  hneq := by decide
  hlen := by decide
  c := ![38569189, 184135403, 126157147, 176003972, -398803482]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI71N0
  hpmem := by 
    show  _ ∈ I71N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI71N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := PrimeIdeal_isPrime PI71N0
def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0], ![15, 1, 0, 0, 0]] i)))

def SI71N1: IdealEqSpanCertificate O ℤ timesTableO I71N1
 ![![71, 0, 0, 0, 0], ![15, 1, 0, 0, 0]] 
 ![![71, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![59, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![67, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]], ![![15, 1, 0, 0, 0], ![0, 15, 1, 0, 0], ![0, 1, 15, 2, 0], ![15, -70, -41, -36, 126], ![3, -27, -16, -20, 66]]]
  hmulB := by decide
  f := ![![![-38465684, -17864716, -253463359, -33716196, -376992], ![181858477, -6622809, 1200748734, 212432, 0]], ![![-8485080, -3940744, -55910944, -7437384, -83160], ![40115853, -1460896, 264870612, 46860, 0]], ![![-32243276, -14974822, -212461802, -28262088, -316008], ![152440109, -5551489, 1006509348, 178068, 0]], ![![-25455248, -11822242, -167733109, -22312189, -249480], ![120347597, -4382731, 794613150, 140580, 0]], ![![-36298588, -16858250, -239183733, -31816692, -355753], ![171612857, -6249703, 1133100918, 200464, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-15, 71, 0, 0, 0], ![-59, 0, 71, 0, 0], ![-47, 0, 0, 71, 0], ![-67, 0, 0, 0, 71]], ![![0, 1, 0, 0, 0], ![-4, 15, 1, 0, 0], ![-14, 1, 15, 2, 0], ![-46, -70, -41, -36, 126], ![-30, -27, -16, -20, 66]]]
  hle1 := by decide
  hle2 := by decide

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0], ![23, 1, 0, 0, 0]] i)))

def SI71N2: IdealEqSpanCertificate O ℤ timesTableO I71N2
 ![![71, 0, 0, 0, 0], ![23, 1, 0, 0, 0]] 
 ![![71, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]], ![![23, 1, 0, 0, 0], ![0, 23, 1, 0, 0], ![0, 1, 23, 2, 0], ![15, -70, -41, -28, 126], ![3, -27, -16, -20, 74]]]
  hmulB := by decide
  f := ![![![-3725, -710, -15244, -1326, 0], ![11502, -355, 47073, 0, 0]], ![![-1265, -253, -5082, -442, 0], ![3906, -71, 15691, 0, 0]], ![![-2039, -384, -8369, -728, 0], ![6296, -212, 25844, 0, 0]], ![![-1971, -370, -7944, -691, 0], ![6086, -189, 24531, 0, 0]], ![![78822, 12746, 265024, 23040, 71], ![-243294, 6696, -818480, -40, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-23, 71, 0, 0, 0], ![-39, 0, 71, 0, 0], ![-37, 0, 0, 71, 0], ![0, 0, 0, 0, 71]], ![![0, 1, 0, 0, 0], ![-8, 23, 1, 0, 0], ![-14, 1, 23, 2, 0], ![60, -70, -41, -28, 126], ![28, -27, -16, -20, 74]]]
  hle1 := by decide
  hle2 := by decide

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulEqCertificate O ℤ timesTableO (I71N0) I71N1
  ![![71, 0, 0, 0, 0], ![-180, -71, -54, -68, 177]] ![![71, 0, 0, 0, 0], ![15, 1, 0, 0, 0]]
  ![![71, 0, 0, 0, 0], ![-231, -93, -65, -92, 243]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![5041, 0, 0, 0, 0], ![1065, 71, 0, 0, 0]], ![![-12780, -5041, -3834, -4828, 12567], ![-3189, -1318, -925, -1200, 3114]]]
 hmul := by decide
 f :=  ![![![![-437857449419668636, -203350513532997907, -2885115505889444608, -383783684877105180, -4291508864059866], ![2070107029775762035, -75386224096120710, 13667848974716243670, 2418231146043524, 0]], ![![27947622, 0, 0, 0, 0], ![852, 0, 0, 0, 0]]], ![![![1424599571622361536, 661614995593319184, 9386923345071921969, 1248666829344152920, 13962721651661421], ![-6735236757395949175, 245274307188107364, -44469294333548100714, -7867882707724708, 0]], ![![-90929526, 0, 0, 0, 0], ![-2772, 0, 0, 0, 0]]]]
 g :=  ![![![![71, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![15, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![51, 22, 11, 24, -66], ![71, 0, 0, 0, 0]], ![![108, 43, 30, 44, -117], ![47, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI71N1 : IdealMulEqCertificate O ℤ timesTableO (I71N0*I71N1) I71N2
  ![![71, 0, 0, 0, 0], ![-231, -93, -65, -92, 243]] ![![71, 0, 0, 0, 0], ![23, 1, 0, 0, 0]]
  ![![71, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI71N0
 hI2 := rfl
 M :=  ![![![5041, 0, 0, 0, 0], ![1633, 71, 0, 0, 0]], ![![-16401, -6603, -4615, -6532, 17253], ![-5964, -2556, -1704, -2414, 6390]]]
 hmul := by decide
 f :=  ![![![![-115188456239, -18638531294, -387181505004, -33659766114, -103704624], ![355543645846, -9732920301, 1195739812215, 58436640, 0]], ![![48, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![71, 0, 0, 0, 0]], ![![23, 1, 0, 0, 0]]], ![![![-231, -93, -65, -92, 243]], ![![-84, -36, -24, -34, 90]]]]
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
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}
def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0], ![8, -3, -4, -5, 13]] i)))

def SI73N0: IdealEqSpanCertificate O ℤ timesTableO I73N0
 ![![73, 0, 0, 0, 0], ![8, -3, -4, -5, 13]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![64, 38, 1, 0, 0], ![25, 4, 0, 1, 0], ![58, 13, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]], ![![8, -3, -4, -5, 13], ![-36, 3, -6, -13, 33], ![-96, -23, 8, -9, 45], ![18, -338, -184, -206, 564], ![-56, -150, -82, -102, 282]]]
  hmulB := by decide
  f := ![![![1504759065, -129167976, 242063588, 530484028, -1346136788], ![-119107822, 3024624330, 84096, 0, 0]], ![![4138049184, -355208654, 665668704, 1458817579, -3701841915], ![-327543627, 8317640002, 231264, 0, 0]], ![![3472005520, -298035706, 558525361, 1224012200, -3106008408], ![-274823532, 6978866300, 194040, 0, 0]], ![![742070865, -63699095, 119373488, 261607824, -663846407], ![-58737919, 1491591346, 41472, 0, 0]], ![![1932474866, -165882947, 310868236, 681269892, -1728765459], ![-152963306, 3884349742, 108000, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-64, -38, 73, 0, 0], ![-25, -4, 0, 73, 0], ![-58, -13, 0, 0, 73]], ![![-5, 0, -4, -5, 13], ![-17, -2, -6, -13, 33], ![-41, -12, 8, -9, 45], ![-216, 2, -184, -206, 564], ![-118, -4, -82, -102, 282]]]
  hle1 := by decide
  hle2 := by decide

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI73N0)

def MemCI73N0 : IdealMemCertificate O ℤ B I73N0
  ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![64, 38, 1, 0, 0], ![25, 4, 0, 1, 0], ![58, 13, 0, 0, 1]] ![5929, -310487, -193135, -245304, 587454] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI73N0
 g := ![-213331, 5109, -193135, -245304, 587454]
 hmem := by decide

def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [21, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 72], [0, 1]]
 g := ![![[32, 50], [71], [65], [34, 38], [6], [1]],![[12, 23], [71], [65], [48, 35], [6], [1]]]
 h' := ![![[58, 72], [19, 59], [59, 12], [16, 24], [23, 29], [52, 58], [0, 1]],![[0, 1], [10, 14], [25, 61], [21, 49], [26, 44], [58, 15], [58, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [3, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : PrimeIdeal O 73 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I73N0
  hcard := NI73N0
  P := [21, 15, 1]
  f := ofList [21, 15, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P73P0
  hneq := by decide
  hlen := by decide
  c := ![5929, -310487, -193135, -245304, 587454]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI73N0
  hpmem := by 
    show  _ ∈ I73N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI73N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := PrimeIdeal_isPrime PI73N0
def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] i)))

def SI73N1: IdealEqSpanCertificate O ℤ timesTableO I73N1
 ![![73, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] 
 ![![73, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![68, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]], ![![4, 1, 0, 0, 0], ![0, 4, 1, 0, 0], ![0, 1, 4, 2, 0], ![15, -70, -41, -47, 126], ![3, -27, -16, -20, 55]]]
  hmulB := by decide
  f := ![![![-254895923, -802728768, -2973614412, -1487264478, -465696], ![4650838833, -81061536, 54291493935, 269808, 0]], ![![-18206860, -57337778, -212401048, -106233186, -33264], ![332202926, -5790068, 3877964181, 19272, 0]], ![![-200275371, -630715449, -2336411270, -1168564920, -365904], ![3654230565, -63691185, 42657601392, 211992, 0]], ![![-104689404, -329692176, -1221305922, -610840769, -191268], ![1910166078, -33293112, 22298292198, 110814, 0]], ![![-237437300, -747747346, -2769942192, -1385397048, -433799], ![4332288262, -75509376, 50572898460, 251328, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 73, 0, 0, 0], ![-57, 0, 73, 0, 0], ![-30, 0, 0, 73, 0], ![-68, 0, 0, 0, 73]], ![![0, 1, 0, 0, 0], ![-1, 4, 1, 0, 0], ![-4, 1, 4, 2, 0], ![-62, -70, -41, -47, 126], ![-29, -27, -16, -20, 55]]]
  hle1 := by decide
  hle2 := by decide

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-721, -328, -230, -304, 816]] i)))

def SI73N2: IdealEqSpanCertificate O ℤ timesTableO I73N2
 ![![-721, -328, -230, -304, 816]] 
 ![![73, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![70, 0, 0, 1, 0], ![65, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-721, -328, -230, -304, 816], ![-2112, -1703, -920, -1276, 3312], ![-9204, -3136, -2379, -3004, 8136], ![-9270, -9636, -4614, -6499, 16560], ![-8214, -5876, -3190, -4352, 11297]]]
  hmulB := by decide
  f := ![![![-26065, 14872, 5378, 3592, -11616]], ![![-4381, 3217, 1690, 1460, -3984]], ![![-11294, 5472, 1265, 396, -2280]], ![![-32092, 11668, -658, -3507, 4512]], ![![-24215, 11356, 2300, 400, -3823]]]
  g := ![![![-229, -328, -230, -304, 816], ![-821, -1703, -920, -1276, 3312], ![-2302, -3136, -2379, -3004, 8136], ![-3764, -9636, -4614, -6499, 16560], ![-2767, -5876, -3190, -4352, 11297]]]
  hle1 := by decide
  hle2 := by decide

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def I73N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 265, 321, 356, -836]] i)))

def SI73N3: IdealEqSpanCertificate O ℤ timesTableO I73N3
 ![![73, 265, 321, 356, -836]] 
 ![![73, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![73, 265, 321, 356, -836], ![2832, -1954, -955, -794, 2220], ![-5250, -2483, -4920, -5816, 13176], ![-25272, 21576, 13056, 12025, -31530], ![-9692, 6787, 3377, 2836, -7879]]]
  hmulB := by decide
  f := ![![![-24601, -13127, -7437, -9706, 25316]], ![![-7020, -3732, -2111, -2752, 7176]], ![![-16397, -8702, -4903, -6384, 16636]], ![![-23112, -12186, -6858, -8915, 23226]], ![![-7946, -4155, -2323, -3010, 7833]]]
  g := ![![![-354, 265, 321, 356, -836], ![1223, -1954, -955, -794, 2220], ![5196, -2483, -4920, -5816, 13176], ![-15972, 21576, 13056, 12025, -31530], ![-4307, 6787, 3377, 2836, -7879]]]
  hle1 := by decide
  hle2 := by decide

lemma NI73N3 : Nat.card (O ⧸ I73N3) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI73N3)

lemma isPrimeI73N3 : Ideal.IsPrime I73N3 := prime_ideal_of_norm_prime hp73.out _ NI73N3
def MulI73N0 : IdealMulEqCertificate O ℤ timesTableO (I73N0) I73N1
  ![![73, 0, 0, 0, 0], ![8, -3, -4, -5, 13]] ![![73, 0, 0, 0, 0], ![4, 1, 0, 0, 0]]
  ![![-23, -15, -7, -10, 28]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![5329, 0, 0, 0, 0], ![292, 73, 0, 0, 0]], ![![584, -219, -292, -365, 949], ![-4, -9, -22, -33, 85]]]
 hmul := by decide
 f :=  ![![![![-41026769516979096710037461, -11538887011089250813564655, -5157683913956277343524359, -2579802814975044021183667, -9566711676624186013], ![748738522900058443857391853, -140579026334403048850344, 94162932998127382214862360, 5542619305597291026, 0]], ![![-6162444058200, 0, 0, 0, 0], ![68430065, -5184, 0, 0, 0]]]]
 g :=  ![![![![-949, 1825, 511, 876, -2044]], ![![44, 10, 9, 10, -28]]], ![![![108, 97, 46, 61, -157]], ![![12, 7, 4, 5, -13]]]]
 hle1 := by decide
 hle2 := by decide

def MulI73N1 : IdealMulEqCertificate O ℤ timesTableO (I73N0*I73N1) I73N2
  ![![-23, -15, -7, -10, 28]] ![![-721, -328, -230, -304, 816]]
  ![![-24601, -13127, -7437, -9706, 25316]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI73N0
 hI2 := rfl
 M :=  ![![![-24601, -13127, -7437, -9706, 25316]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI73N2 : IdealMulEqCertificate O ℤ timesTableO (I73N0*I73N1*I73N2) I73N3
  ![![-24601, -13127, -7437, -9706, 25316]] ![![73, 265, 321, 356, -836]]
  ![![73, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI73N1
 hI2 := rfl
 M :=  ![![![73, 0, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC73 : PrimesBelowPCertificate 73 ![I73N0, I73N1, I73N2, I73N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
    exact isPrimeI73N3
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI73N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}
def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0], ![53, 89, 30, 37, -96]] i)))

def SI79N0: IdealEqSpanCertificate O ℤ timesTableO I79N0
 ![![79, 0, 0, 0, 0], ![53, 89, 30, 37, -96]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![49, 4, 44, 1, 0], ![71, 36, 15, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]], ![![53, 89, 30, 37, -96], ![267, 85, 108, 93, -234], ![693, 183, 16, 153, -216], ![690, -2127, -1371, -1772, 4248], ![537, -696, -473, -599, 1478]]]
  hmulB := by decide
  f := ![![![310047, -133402, 97860, 48334, -112272], ![254222, -142200, 0, 0, 0]], ![![-10349, 4424, -3270, -1621, 3768], ![-8453, 4740, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![191789, -82510, 60536, 29901, -69456], ![157246, -87960, 0, 0, 0]], ![![273960, -117833, 86475, 42719, -99233], ![224587, -125640, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-49, -4, -44, 79, 0], ![-71, -36, -15, 0, 79]], ![![64, 43, -2, 37, -96], ![156, 103, -6, 93, -234], ![108, 93, -44, 153, -216], ![-2710, -1873, 163, -1772, 4248], ![-950, -652, 47, -599, 1478]]]
  hle1 := by decide
  hle2 := by decide

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI79N0)

def MemCI79N0 : IdealMemCertificate O ℤ B I79N0
  ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![49, 4, 44, 1, 0], ![71, 36, 15, 0, 1]] ![38475395, 188250734, 128713702, 179250124, -406583184] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI79N0
 g := ![254716777, 178585378, -21006886, 179250124, -406583184]
 hmem := by decide

def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [52, 37, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 71, 57], [75, 7, 22], [0, 1]]
 g := ![![[75, 14, 67], [55, 58, 22], [72, 16, 38], [22, 63, 72], [46, 1], []],![[34, 34, 55, 78], [51, 70, 63, 27], [36, 31, 72, 39], [15, 40, 35, 59], [28, 49], [22, 10]],![[69, 20, 73, 19], [49, 60, 24, 25], [55, 62, 77, 38], [12, 57, 35, 22], [5, 64], [57, 10]]]
 h' := ![![[50, 71, 57], [63, 18, 64], [48, 2, 38], [41, 28, 65], [57, 63, 25], [0, 0, 1], [0, 1]],![[75, 7, 22], [57, 29, 52], [10, 25, 64], [74, 27, 76], [56, 24, 53], [13, 78, 7], [50, 71, 57]],![[0, 1], [50, 32, 42], [38, 52, 56], [42, 24, 17], [49, 71, 1], [54, 1, 71], [75, 7, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 2], []]
 b := ![[], [5, 25, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : PrimeIdeal O 79 where 
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I79N0
  hcard := NI79N0
  P := [52, 37, 33, 1]
  f := ofList [52, 37, 33, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P79P0
  hneq := by decide
  hlen := by decide
  c := ![38475395, 188250734, 128713702, 179250124, -406583184]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI79N0
  hpmem := by 
    show  _ ∈ I79N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI79N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := PrimeIdeal_isPrime PI79N0
def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1670, 936, 553, 735, -1930]] i)))

def SI79N1: IdealEqSpanCertificate O ℤ timesTableO I79N1
 ![![1670, 936, 553, 735, -1930]] 
 ![![79, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![65, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![1670, 936, 553, 735, -1930], ![5235, 2883, 1681, 2221, -5820], ![15855, 8586, 4942, 6491, -16974], ![20604, 10921, 6179, 8051, -20994], ![16667, 8943, 5110, 6689, -17471]]]
  hmulB := by decide
  f := ![![![982, -1055, -198, -405, 922]], ![![157, -160, -30, -59, 136]], ![![939, -1075, -229, -447, 1014]], ![![254, -194, 43, -6, 2]], ![![71, -61, 11, -6, 9]]]
  g := ![![![-729, 936, 553, 735, -1930], ![-2222, 2883, 1681, 2221, -5820], ![-6550, 8586, 4942, 6491, -16974], ![-8219, 10921, 6179, 8051, -20994], ![-6783, 8943, 5110, 6689, -17471]]]
  hle1 := by decide
  hle2 := by decide

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0], ![-25, 1, 0, 0, 0]] i)))

def SI79N2: IdealEqSpanCertificate O ℤ timesTableO I79N2
 ![![79, 0, 0, 0, 0], ![-25, 1, 0, 0, 0]] 
 ![![79, 0, 0, 0, 0], ![54, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]], ![![-25, 1, 0, 0, 0], ![0, -25, 1, 0, 0], ![0, 1, -25, 2, 0], ![15, -70, -41, -76, 126], ![3, -27, -16, -20, 26]]]
  hmulB := by decide
  f := ![![![-769313764, 202516280, -5235352995, 419300084, -556416], ![-2430822179, -120222121, -16549096486, 348864, 0]], ![![-528903214, 139229946, -3599305387, 288268824, -382536], ![-1671190252, -82652723, -11377504476, 239844, 0]], ![![-72123152, 18985915, -490814283, 39309378, -52164], ![-227889537, -11270771, -1551477603, 32706, 0]], ![![-204348946, 53793399, -1390640642, 111376585, -147798], ![-645687070, -31933960, -4395853761, 92667, 0]], ![![-243453700, 64087432, -1656757277, 132689900, -176081], ![-769247453, -38044967, -5237055850, 110400, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-54, 79, 0, 0, 0], ![-7, 0, 79, 0, 0], ![-21, 0, 0, 79, 0], ![-25, 0, 0, 0, 79]], ![![-1, 1, 0, 0, 0], ![17, -25, 1, 0, 0], ![1, 1, -25, 2, 0], ![32, -70, -41, -76, 126], ![17, -27, -16, -20, 26]]]
  hle1 := by decide
  hle2 := by decide

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulEqCertificate O ℤ timesTableO (I79N0) I79N1
  ![![79, 0, 0, 0, 0], ![53, 89, 30, 37, -96]] ![![1670, 936, 553, 735, -1930]]
  ![![79, 0, 0, 0, 0], ![119, 97, 59, 60, -151]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![131930, 73944, 43687, 58065, -152470]], ![![192391, 109324, 65241, 87097, -229052]]]
 hmul := by decide
 f :=  ![![![![21152336, -9095391, 6676998, 3298967, -7663478]], ![![17337556, -9700090, 0, 0, 0]]], ![![![30238984, -13002609, 9545312, 4716139, -10955559]], ![![24785463, -13867074, 0, 0, 0]]]]
 g :=  ![![![![242, -228, -155, 15, -118], ![948, 0, 0, 0, 0]]], ![![![453, -232, -157, 103, -384], ![1316, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI79N1 : IdealMulEqCertificate O ℤ timesTableO (I79N0*I79N1) I79N2
  ![![79, 0, 0, 0, 0], ![119, 97, 59, 60, -151]] ![![79, 0, 0, 0, 0], ![-25, 1, 0, 0, 0]]
  ![![79, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI79N0
 hI2 := rfl
 M :=  ![![![6241, 0, 0, 0, 0], ![-1975, 79, 0, 0, 0]], ![![9401, 7663, 4661, 4740, -11929], ![-2528, -2370, -1422, -1422, 3634]]]
 hmul := by decide
 f :=  ![![![![-80629975571194, 21225238612080, -548704531281971, 43945815436532, -58316720644], ![-254768784612979, -12600187243149, -1734470290740382, 36563657544, 0]], ![![-532, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![79, 0, 0, 0, 0]], ![![-25, 1, 0, 0, 0]]], ![![![119, 97, 59, 60, -151]], ![![-32, -30, -18, -18, 46]]]]
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
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}
def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0], ![-457, -299, -153, -197, 514]] i)))

def SI83N0: IdealEqSpanCertificate O ℤ timesTableO I83N0
 ![![83, 0, 0, 0, 0], ![-457, -299, -153, -197, 514]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![70, 28, 6, 24, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]], ![![-457, -299, -153, -197, 514], ![-1413, -698, -446, -539, 1392], ![-3909, -1713, -871, -1243, 3078], ![-3999, -89, 224, 315, -516], ![-3596, -1040, -460, -595, 1611]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![144, 94, 48, 62, -161], ![26, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-70, -28, -6, -24, 83]], ![![-439, -177, -39, -151, 514], ![-1191, -478, -106, -409, 1392], ![-2643, -1059, -233, -905, 3078], ![387, 173, 40, 153, -516], ![-1402, -556, -122, -473, 1611]]]
  hle1 := by decide
  hle2 := by decide

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI83N0)

def MemCI83N0 : IdealMemCertificate O ℤ B I83N0
  ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![70, 28, 6, 24, 1]] ![-105263671680, -86786193593, -60875090557, -112816582684, 234785486082] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI83N0
 g := ![-199280092740, -80250359083, -17705879603, -69249015044, 234785486082]
 hmem := by decide

def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [37, 39, 45, 38, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 39, 74, 45], [32, 29, 23, 21], [71, 14, 69, 17], [0, 1]]
 g := ![![[24, 33, 29, 16], [16, 77, 0, 17], [42, 45, 9], [56, 74, 61], [45, 1], []],![[72, 10, 16, 42, 16, 2], [14, 49, 46, 79, 0, 50], [36, 82, 41], [31, 61, 12], [52, 32, 8, 6, 29, 79], [28, 11, 33]],![[2, 3, 41, 25, 17, 70], [40, 68, 32, 44, 76, 10], [14, 2, 70], [3, 36, 9], [64, 66, 43, 4, 74, 27], [2, 61, 26]],![[72, 35, 5, 62, 72, 41], [38, 36, 22, 78, 50, 23], [41, 65, 3], [9, 9, 38], [34, 59, 32, 69, 69, 75], [20, 79, 40]]]
 h' := ![![[25, 39, 74, 45], [72, 44, 76, 79], [60, 78, 59, 73], [28, 50, 23, 3], [78, 34, 11, 71], [0, 0, 1], [0, 1]],![[32, 29, 23, 21], [63, 48, 6, 52], [0, 49, 14, 72], [2, 22, 76, 37], [53, 47, 69, 26], [4, 36, 70, 30], [25, 39, 74, 45]],![[71, 14, 69, 17], [68, 78, 12, 23], [72, 15, 4, 17], [3, 9, 25, 30], [23, 75, 20, 80], [37, 19, 44, 5], [32, 29, 23, 21]],![[0, 1], [44, 79, 72, 12], [15, 24, 6, 4], [11, 2, 42, 13], [26, 10, 66, 72], [68, 28, 51, 48], [71, 14, 69, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [37, 77, 33], []]
 b := ![[], [], [61, 20, 14, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : PrimeIdeal O 83 where 
  r := 5
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I83N0
  hcard := NI83N0
  P := [37, 39, 45, 38, 1]
  f := ofList [37, 39, 45, 38, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P83P0
  hneq := by decide
  hlen := by decide
  c := ![-105263671680, -86786193593, -60875090557, -112816582684, 234785486082]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI83N0
  hpmem := by 
    show  _ ∈ I83N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI83N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := PrimeIdeal_isPrime PI83N0
def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))

def SI83N1: IdealEqSpanCertificate O ℤ timesTableO I83N1
 ![![83, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] 
 ![![83, 0, 0, 0, 0], ![79, 1, 0, 0, 0], ![67, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]], ![![-4, 1, 0, 0, 0], ![0, -4, 1, 0, 0], ![0, 1, -4, 2, 0], ![15, -70, -41, -55, 126], ![3, -27, -16, -20, 47]]]
  hmulB := by decide
  f := ![![![36888849, -436295628, 1716737920, -858376538, -402696], ![766438351, 41313416, 35629921197, 265268, 0]], ![![35319109, -417729873, 1643685309, -821849910, -385560], ![733823917, 39555393, 34113755715, 253980, 0]], ![![29825029, -352749653, 1388000858, -694006556, -325584], ![619673605, 33402355, 28807170054, 214472, 0]], ![![23546075, -278486572, 1095790164, -547899919, -257040], ![489215993, 26370264, 22742502939, 169320, 0]], ![![12888879, -152440640, 599824092, -299914694, -140701], ![267791797, 14434852, 12449008611, 92684, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-79, 83, 0, 0, 0], ![-67, 0, 83, 0, 0], ![-53, 0, 0, 83, 0], ![-29, 0, 0, 0, 83]], ![![-1, 1, 0, 0, 0], ![3, -4, 1, 0, 0], ![1, 1, -4, 2, 0], ![91, -70, -41, -55, 126], ![35, -27, -16, -20, 47]]]
  hle1 := by decide
  hle2 := by decide

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulEqCertificate O ℤ timesTableO (I83N0) I83N1
  ![![83, 0, 0, 0, 0], ![-457, -299, -153, -197, 514]] ![![83, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
  ![![83, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![6889, 0, 0, 0, 0], ![-332, 83, 0, 0, 0]], ![![-37931, -24817, -12699, -16351, 42662], ![415, 498, 166, 249, -664]]]
 hmul := by decide
 f :=  ![![![![11822237488405751, -139825636151870708, 550186553272728497, -275095704797693534, -129058174192248], ![245630232246839331, 13240265998090209, 11418809648166574875, 85014509808578, 0]], ![![432054, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![83, 0, 0, 0, 0]], ![![-4, 1, 0, 0, 0]]], ![![![-457, -299, -153, -197, 514]], ![![5, 6, 2, 3, -8]]]]
 hle1 := by decide
 hle2 := by decide

def PBC83 : PrimesBelowPCertificate 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI83N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}
def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0], ![-54, -10, -4, -5, 13]] i)))

def SI89N0: IdealEqSpanCertificate O ℤ timesTableO I89N0
 ![![89, 0, 0, 0, 0], ![-54, -10, -4, -5, 13]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![25, 43, 1, 0, 0], ![41, 23, 0, 1, 0], ![33, 35, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]], ![![-54, -10, -4, -5, 13], ![-36, -59, -13, -13, 33], ![-96, -30, -54, -23, 45], ![-87, 152, 103, 89, -318], ![-77, 39, 30, 38, -137]]]
  hmulB := by decide
  f := ![![![31266466429, 83413833716, 17643255432, 17233251278, -43619769766], ![-36475548358, 132009700696, 478108, 0, 0]], ![![3218599788, 8586699325, 1816213484, 1774007267, -4490260561], ![-3754827586, 13589204054, 49217, 0, 0]], ![![10332602837, 27565699353, 5830551759, 5695058032, -14414988568], ![-12054043702, 43625134566, 158000, 0, 0]], ![![15235426039, 40645632209, 8597150368, 8397364825, -21254905090], ![-17773691227, 64325274402, 232971, 0, 0]], ![![12858925707, 34305516737, 7256122488, 7087500526, -17939455311], ![-15001259057, 54291486122, 196631, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-25, -43, 89, 0, 0], ![-41, -23, 0, 89, 0], ![-33, -35, 0, 0, 89]], ![![-2, -2, -4, -5, 13], ![-3, -4, -13, -13, 33], ![8, 14, -54, -23, 45], ![47, 54, 103, 89, -318], ![24, 30, 30, 38, -137]]]
  hle1 := by decide
  hle2 := by decide

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI89N0)

def MemCI89N0 : IdealMemCertificate O ℤ B I89N0
  ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![25, 43, 1, 0, 0], ![41, 23, 0, 1, 0], ![33, 35, 0, 0, 1]] ![2896, -296267, -184891, -235008, 561750] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI89N0
 g := ![-48059, -74180, -184891, -235008, 561750]
 hmem := by decide

def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [48, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 88], [0, 1]]
 g := ![![[40, 73], [21], [36], [0, 4], [49, 20], [1]],![[55, 16], [21], [36], [63, 85], [8, 69], [1]]]
 h' := ![![[38, 88], [5, 47], [52, 33], [0, 6], [51, 2], [41, 38], [0, 1]],![[0, 1], [11, 42], [60, 56], [50, 83], [38, 87], [61, 51], [38, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [36, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : PrimeIdeal O 89 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I89N0
  hcard := NI89N0
  P := [48, 51, 1]
  f := ofList [48, 51, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P89P0
  hneq := by decide
  hlen := by decide
  c := ![2896, -296267, -184891, -235008, 561750]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI89N0
  hpmem := by 
    show  _ ∈ I89N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI89N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := PrimeIdeal_isPrime PI89N0
def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0], ![-19, -7, -4, -5, 13]] i)))

def SI89N1: IdealEqSpanCertificate O ℤ timesTableO I89N1
 ![![89, 0, 0, 0, 0], ![-19, -7, -4, -5, 13]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![57, 73, 1, 0, 0], ![11, 79, 0, 1, 0], ![34, 66, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]], ![![-19, -7, -4, -5, 13], ![-36, -24, -10, -13, 33], ![-96, -27, -19, -17, 45], ![-42, -58, -20, -29, 60], ![-68, -42, -18, -22, 51]]]
  hmulB := by decide
  f := ![![![207863054, 144379414, 59048543, 76967475, -195063811], ![-91201237, 561999845, 6675, 0, 0]], ![![7482026369, 5196934182, 2125451130, 2770442732, -7021317992], ![-3282788585, 20229173921, 240300, 0, 0]], ![![6267733534, 4353499578, 1780501787, 2320814704, -5881795660], ![-2750009557, 16946087257, 201300, 0, 0]], ![![6667040189, 4630853640, 1893934531, 2468669866, -6256514869], ![-2925207994, 18025693686, 214125, 0, 0]], ![![5627877337, 3909062423, 1598735110, 2083888923, -5281338834], ![-2469268475, 15216106444, 180750, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-57, -73, 89, 0, 0], ![-11, -79, 0, 89, 0], ![-34, -66, 0, 0, 89]], ![![-2, -2, -4, -5, 13], ![-5, -5, -10, -13, 33], ![-4, -3, -19, -17, 45], ![-7, -3, -20, -29, 60], ![-6, -4, -18, -22, 51]]]
  hle1 := by decide
  hle2 := by decide

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI89N1)

def MemCI89N1 : IdealMemCertificate O ℤ B I89N1
  ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![57, 73, 1, 0, 0], ![11, 79, 0, 1, 0], ![34, 66, 0, 0, 1]] ![327939, -13535891, -8530138, -9845521, 24808653] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI89N1
 g := ![-2793794, -2813604, -8530138, -9845521, 24808653]
 hmem := by decide

def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [35, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 88], [0, 1]]
 g := ![![[48, 84], [68], [42], [60, 69], [27, 32], [1]],![[82, 5], [68], [42], [18, 20], [23, 57], [1]]]
 h' := ![![[11, 88], [39, 23], [4, 54], [36, 24], [34, 46], [54, 11], [0, 1]],![[0, 1], [25, 66], [64, 35], [33, 65], [6, 43], [86, 78], [11, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [65, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : PrimeIdeal O 89 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I89N1
  hcard := NI89N1
  P := [35, 78, 1]
  f := ofList [35, 78, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P89P1
  hneq := by decide
  hlen := by decide
  c := ![327939, -13535891, -8530138, -9845521, 24808653]
  a := ![-526, 2412, 1421, 1723, -4419]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI89N1
  hpmem := by 
    show  _ ∈ I89N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI89N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := PrimeIdeal_isPrime PI89N1
def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12, 15, 4, 7, -16]] i)))

def SI89N2: IdealEqSpanCertificate O ℤ timesTableO I89N2
 ![![-12, 15, 4, 7, -16]] 
 ![![89, 0, 0, 0, 0], ![62, 1, 0, 0, 0], ![72, 0, 1, 0, 0], ![51, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-12, 15, 4, 7, -16], ![57, -66, -16, -29, 66], ![-237, 289, 67, 127, -288], ![492, -609, -147, -277, 624], ![137, -168, -41, -77, 173]]]
  hmulB := by decide
  f := ![![![-448, -222, -123, -159, 412]], ![![-325, -161, -89, -115, 298]], ![![-393, -196, -108, -139, 360]], ![![-288, -141, -78, -100, 258]], ![![-221, -109, -60, -77, 199]]]
  g := ![![![-11, 15, 4, 7, -16], ![48, -66, -16, -29, 66], ![-208, 289, 67, 127, -288], ![441, -609, -147, -277, 624], ![122, -168, -41, -77, 173]]]
  hle1 := by decide
  hle2 := by decide

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulEqCertificate O ℤ timesTableO (I89N0) I89N1
  ![![89, 0, 0, 0, 0], ![-54, -10, -4, -5, 13]] ![![89, 0, 0, 0, 0], ![-19, -7, -4, -5, 13]]
  ![![448, 222, 123, 159, -412]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![7921, 0, 0, 0, 0], ![-1691, -623, -356, -445, 1157]], ![![-4806, -890, -356, -445, 1157], ![1096, 470, 258, 327, -849]]]
 hmul := by decide
 f :=  ![![![![724242663850415210442966842814, 503051081863797016652560274721, 205738701434128059474689254366, 268172380949033907908525496163, -679647170280974539536889826208], ![-317766270902683358498935327802, 1958136756222848175767517181171, 23260473207836987707837325, 0, 0]], ![![7175015783224960116, 282197255254, 0, 0, 0], ![-24192, 0, 0, 0, 0]]]]
 g :=  ![![![![1068, -1335, -356, -623, 1424]], ![![-98, 118, 30, 54, -123]]], ![![![-347, 445, 122, 212, -485]], ![![33, -39, -10, -18, 41]]]]
 hle1 := by decide
 hle2 := by decide

def MulI89N1 : IdealMulEqCertificate O ℤ timesTableO (I89N0*I89N1) I89N2
  ![![448, 222, 123, 159, -412]] ![![-12, 15, 4, 7, -16]]
  ![![89, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI89N0
 hI2 := rfl
 M :=  ![![![-89, 0, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![-1, 0, 0, 0, 0]]]]
 g :=  ![![![![-1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC89 : PrimesBelowPCertificate 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI89N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}
def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0], ![376, 224, 122, 152, -395]] i)))

def SI97N0: IdealEqSpanCertificate O ℤ timesTableO I97N0
 ![![97, 0, 0, 0, 0], ![376, 224, 122, 152, -395]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![52, 47, 63, 1, 0], ![50, 74, 48, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]], ![![376, 224, 122, 152, -395], ![1095, 523, 312, 392, -993], ![2901, 778, 339, 492, -1251], ![1266, 1027, 155, 107, -408], ![2023, 972, 357, 427, -1135]]]
  hmulB := by decide
  f := ![![![304947, -133662, -6602, -232, 63221], ![610033, -236486, 0, 0, 0]], ![![-6899, 2746, 56, -104, -1091], ![-13192, 5141, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![160351, -70194, -3441, -87, 33135], ![320580, -124285, 0, 0, 0]], ![![152240, -66616, -3258, -72, 31426], ![304305, -117978, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-52, -47, -63, 97, 0], ![-50, -74, -48, 0, 97]], ![![126, 230, 98, 152, -395], ![313, 573, 240, 392, -993], ![411, 724, 303, 492, -1251], ![166, 270, 134, 107, -408], ![377, 669, 288, 427, -1135]]]
  hle1 := by decide
  hle2 := by decide

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI97N0)

def MemCI97N0 : IdealMemCertificate O ℤ B I97N0
  ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![52, 47, 63, 1, 0], ![50, 74, 48, 0, 1]] ![38523247, 186046910, 127344124, 177510974, -402416028] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI97N0
 g := ![112667567, 222905332, 85155898, 177510974, -402416028]
 hmem := by decide

def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [3, 65, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 58, 24], [96, 38, 73], [0, 1]]
 g := ![![[13, 15, 24], [76, 25], [82, 94], [18, 8], [79, 48], [1]],![[23, 34, 59, 4], [10, 11], [38, 49], [34, 88], [0, 91], [50, 95, 60, 50]],![[61, 22, 39, 3], [30, 18], [25, 70], [30, 86], [51, 62], [76, 17, 55, 47]]]
 h' := ![![[58, 58, 24], [47, 84, 11], [9, 30, 5], [35, 3, 26], [63, 58, 28], [94, 32, 57], [0, 1]],![[96, 38, 73], [40, 90, 9], [78, 69, 37], [17, 79, 90], [64, 1, 31], [89, 92, 24], [58, 58, 24]],![[0, 1], [60, 20, 77], [76, 95, 55], [32, 15, 78], [5, 38, 38], [62, 70, 16], [96, 38, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49], []]
 b := ![[], [51, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : PrimeIdeal O 97 where 
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I97N0
  hcard := NI97N0
  P := [3, 65, 40, 1]
  f := ofList [3, 65, 40, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P97P0
  hneq := by decide
  hlen := by decide
  c := ![38523247, 186046910, 127344124, 177510974, -402416028]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI97N0
  hpmem := by 
    show  _ ∈ I97N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI97N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := PrimeIdeal_isPrime PI97N0
def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0], ![3, -3, -4, -5, 13]] i)))

def SI97N1: IdealEqSpanCertificate O ℤ timesTableO I97N1
 ![![97, 0, 0, 0, 0], ![3, -3, -4, -5, 13]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![69, 68, 1, 0, 0], ![79, 51, 0, 1, 0], ![22, 3, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]], ![![3, -3, -4, -5, 13], ![-36, -2, -6, -13, 33], ![-96, -23, 3, -9, 45], ![18, -338, -184, -211, 564], ![-56, -150, -82, -102, 277]]]
  hmulB := by decide
  f := ![![![8433846727, 436657482, 1360275688, 2984228438, -7572273094], ![-977424962, 22642793808, 107088, 0, 0]], ![![54819484368, 2838246735, 8841708190, 19397301057, -49219308757], ![-6353202404, 147176765377, 696072, 0, 0]], ![![44422242756, 2299935633, 7164761073, 15718345883, -39884214659], ![-5148233365, 119262741616, 564052, 0, 0]], ![![35691418498, 1847902314, 5756586566, 12629035055, -32045302274], ![-4136390701, 95822636547, 453192, 0, 0]], ![![3608279185, 186816546, 581971030, 1276751846, -3239669433], ![-418174757, 9687337731, 45816, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-69, -68, 97, 0, 0], ![-79, -51, 0, 97, 0], ![-22, -3, 0, 0, 97]], ![![4, 5, -4, -5, 13], ![7, 10, -6, -13, 33], ![-6, 1, 3, -9, 45], ![175, 219, -184, -211, 564], ![78, 101, -82, -102, 277]]]
  hle1 := by decide
  hle2 := by decide

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI97N1)

def MemCI97N1 : IdealMemCertificate O ℤ B I97N1
  ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![69, 68, 1, 0, 0], ![79, 51, 0, 1, 0], ![22, 3, 0, 0, 1]] ![365831, -13709555, -8632450, -9969577, 25126821] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI97N1
 g := ![8565066, 10374897, -8632450, -9969577, 25126821]
 hmem := by decide

def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [55, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 96], [0, 1]]
 g := ![![[83, 11], [72], [3], [86], [70], [91, 1]],![[17, 86], [72], [3], [86], [70], [85, 96]]]
 h' := ![![[91, 96], [61, 37], [23, 84], [24, 87], [96, 38], [39, 78], [0, 1]],![[0, 1], [33, 60], [4, 13], [84, 10], [62, 59], [56, 19], [91, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [77, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : PrimeIdeal O 97 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I97N1
  hcard := NI97N1
  P := [55, 6, 1]
  f := ofList [55, 6, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P97P1
  hneq := by decide
  hlen := by decide
  c := ![365831, -13709555, -8632450, -9969577, 25126821]
  a := ![-526, 2412, 1421, 1723, -4419]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI97N1
  hpmem := by 
    show  _ ∈ I97N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI97N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := PrimeIdeal_isPrime PI97N1
def MulI97N0 : IdealMulEqCertificate O ℤ timesTableO (I97N0) I97N1
  ![![97, 0, 0, 0, 0], ![376, 224, 122, 152, -395]] ![![97, 0, 0, 0, 0], ![3, -3, -4, -5, 13]]
  ![![97, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![9409, 0, 0, 0, 0], ![291, -291, -388, -485, 1261]], ![![36472, 21728, 11834, 14744, -38315], ![6208, 3492, 1940, 2328, -5917]]]
 hmul := by decide
 f :=  ![![![![1803713925612855966840566, 93386233271673791470959, 290916858622723062203190, 638225303149249961656441, -1619452528978166517826320], ![-209038079896183095491984, 4842526052350550481063725, 22902709341415087688, 0, 0]], ![![-111399623596, -65639, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![97, 0, 0, 0, 0]], ![![3, -3, -4, -5, 13]]], ![![![376, 224, 122, 152, -395]], ![![64, 36, 20, 24, -61]]]]
 hle1 := by decide
 hle2 := by decide

def PBC97 : PrimesBelowPCertificate 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI97N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}
def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate O ℤ timesTableO I101N0
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

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10510100501 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI101N0)

def MemCI101N0 : IdealMemCertificate O ℤ B I101N0
  ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]] ![142097093366520, 6350760591336, -10787282838984, 39423240626716, -54578874455196] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI101N0
 g := ![1406901914520, 62878817736, -106804780584, 390329115116, -540384895596]
 hmem := by decide

def P101P0 : CertificateIrreducibleZModOfList' 101 5 2 6 [46, 50, 35, 49, 43, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 39, 56, 38, 25], [5, 5, 69, 2, 62], [89, 21, 26, 14, 81], [44, 35, 51, 47, 34], [0, 1]]
 g := ![![[72, 2, 42, 34, 97], [87, 25, 72, 70], [24, 88, 33, 20, 52], [84, 41, 53, 21], [58, 1], []],![[87, 91, 11, 11, 94, 9, 44, 100], [77, 84, 54, 70], [58, 84, 11, 15, 91, 12, 45, 22], [51, 14, 45, 65], [80, 48, 67, 68], [39, 30, 27, 56, 44, 7, 22, 71]],![[93, 39, 37, 69, 6, 5, 42, 10], [36, 43, 90, 52], [15, 20, 9, 87, 4, 51, 7, 90], [54, 76, 91, 33], [10, 23, 100, 45], [93, 81, 49, 33, 61, 4, 99, 69]],![[22, 7, 92, 17, 61, 94, 98, 43], [34, 68, 88, 70], [100, 98, 82, 68, 10, 69, 0, 79], [8, 68, 29, 78], [83, 7, 13, 21], [36, 92, 75, 92, 97, 75, 28, 80]],![[81, 86, 61, 37, 25, 82, 90, 53], [28, 98, 60, 64], [70, 81, 51, 90, 94, 20, 47, 18], [41, 31, 93, 58], [88, 32, 87, 33], [3, 57, 84, 14, 38, 3, 44, 15]]]
 h' := ![![[21, 39, 56, 38, 25], [87, 23, 72, 59, 81], [7, 41, 10, 100, 75], [21, 89, 22, 19, 70], [59, 84, 41, 52, 83], [0, 0, 0, 1], [0, 1]],![[5, 5, 69, 2, 62], [40, 28, 6, 51, 99], [42, 8, 28, 11, 75], [2, 98, 92, 12, 35], [5, 6, 47, 91, 60], [94, 90, 63, 49, 13], [21, 39, 56, 38, 25]],![[89, 21, 26, 14, 81], [5, 46, 93, 19, 6], [34, 80, 97, 70, 70], [8, 81, 41, 71, 83], [88, 81, 3, 33, 29], [89, 79, 31, 73, 34], [5, 5, 69, 2, 62]],![[44, 35, 51, 47, 34], [35, 64, 100, 90, 35], [36, 96, 13, 22, 75], [61, 84, 66, 100, 30], [96, 63, 0, 17, 49], [50, 10, 85, 98, 83], [89, 21, 26, 14, 81]],![[0, 1], [5, 41, 32, 84, 82], [9, 78, 54, 100, 8], [97, 52, 82, 0, 85], [8, 69, 10, 9, 82], [4, 23, 23, 82, 72], [44, 35, 51, 47, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 12, 96, 29], [], [], []]
 b := ![[], [65, 76, 39, 77, 15], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : PrimeIdeal O 101 where 
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I101N0
  hcard := NI101N0
  P := [46, 50, 35, 49, 43, 1]
  f := ofList [46, 50, 35, 49, 43, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P101P0
  hneq := by decide
  hlen := by decide
  c := ![142097093366520, 6350760591336, -10787282838984, 39423240626716, -54578874455196]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI101N0
  hpmem := by 
    show  _ ∈ I101N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI101N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := PrimeIdeal_isPrime PI101N0
def PBC101 : PrimesBelowPCertificate 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    #unfold I101N
    unfold I101N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}
def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0], ![183, 88, 62, 77, -200]] i)))

def SI103N0: IdealEqSpanCertificate O ℤ timesTableO I103N0
 ![![103, 0, 0, 0, 0], ![183, 88, 62, 77, -200]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![81, 93, 97, 1, 0], ![21, 40, 53, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]], ![![183, 88, 62, 77, -200], ![555, 255, 131, 197, -498], ![1461, 342, 146, 175, -576], ![171, 2327, 1126, 1345, -3414], ![910, 1179, 583, 717, -1859]]]
  hmulB := by decide
  f := ![![![218878, 81672, -38998, 19631, -23832], ![496563, -204352, 0, 0, 0]], ![![-6960, -2609, 1178, -664, 876], ![-15450, 6386, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![165987, 61941, -29555, 14899, -18108], ![376470, -154938, 0, 0, 0]], ![![41976, 15664, -7475, 3767, -4577], ![95211, -39184, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-81, -93, -97, 103, 0], ![-21, -40, -53, 0, 103]], ![![-18, 9, 31, 77, -200], ![-48, 18, 72, 197, -498], ![-6, 69, 133, 175, -576], ![-360, 134, 501, 1345, -3414], ![-176, 86, 287, 717, -1859]]]
  hle1 := by decide
  hle2 := by decide

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI103N0)

def MemCI103N0 : IdealMemCertificate O ℤ B I103N0
  ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![81, 93, 97, 1, 0], ![21, 40, 53, 0, 1]] ![38621164, 181629782, 124599472, 174025810, -394064580] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI103N0
 g := ![-56137022, -2331916, 40092414, 174025810, -394064580]
 hmem := by decide

def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [78, 97, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 89, 95], [30, 13, 8], [0, 1]]
 g := ![![[9, 18, 23], [21, 45, 82], [9, 79, 14], [47, 23], [96, 32], [1]],![[40, 47, 78, 73], [5, 68, 76, 85], [100, 63, 65, 21], [34, 38], [48, 17], [81, 10, 34, 3]],![[20, 18, 48, 63], [64, 49, 53, 82], [86, 99, 9, 33], [75, 29], [30, 91], [16, 63, 83, 100]]]
 h' := ![![[19, 89, 95], [10, 67, 34], [19, 51, 59], [44, 101, 23], [38, 28, 69], [25, 6, 49], [0, 1]],![[30, 13, 8], [80, 20, 9], [91, 82, 50], [98, 52, 6], [22, 92, 55], [26, 97, 74], [19, 89, 95]],![[0, 1], [84, 16, 60], [98, 73, 97], [80, 53, 74], [33, 86, 82], [2, 0, 83], [30, 13, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 51], []]
 b := ![[], [34, 88, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : PrimeIdeal O 103 where 
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I103N0
  hcard := NI103N0
  P := [78, 97, 54, 1]
  f := ofList [78, 97, 54, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P103P0
  hneq := by decide
  hlen := by decide
  c := ![38621164, 181629782, 124599472, 174025810, -394064580]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI103N0
  hpmem := by 
    show  _ ∈ I103N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI103N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := PrimeIdeal_isPrime PI103N0
def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0], ![-22, 11, -4, -5, 13]] i)))

def SI103N1: IdealEqSpanCertificate O ℤ timesTableO I103N1
 ![![103, 0, 0, 0, 0], ![-22, 11, -4, -5, 13]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![62, 12, 1, 0, 0], ![40, 11, 0, 1, 0], ![9, 88, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]], ![![-22, 11, -4, -5, 13], ![-36, -27, 8, -13, 33], ![-96, -9, -22, 19, 45], ![228, -1318, -758, -950, 2328], ![-14, -528, -306, -382, 966]]]
  hmulB := by decide
  f := ![![![37773446191, 30877530432, -9217456230, 13913045904, -35289469680], ![-9541956153, 113904507618, 267903, 0, 0]], ![![5925219720, 4843512322, -1445868960, 2182428723, -5535578103], ![-1496770662, 17867293095, 42024, 0, 0]], ![![23420540272, 19144889273, -5715067767, 8626458127, -21880408835], ![-5916266323, 70623821133, 166107, 0, 0]], ![![15302089960, 12508542254, -3734007840, 5636199538, -14295826671], ![-3865463274, 46142917755, 108528, 0, 0]], ![![8362916041, 6836183084, -2040714314, 3080302340, -7812971853], ![-2112557459, 25218081174, 59313, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-62, -12, 103, 0, 0], ![-40, -11, 0, 103, 0], ![-9, -88, 0, 0, 103]], ![![3, -10, -4, -5, 13], ![-3, -28, 8, -13, 33], ![1, -38, -22, 19, 45], ![624, -1812, -758, -950, 2328], ![248, -754, -306, -382, 966]]]
  hle1 := by decide
  hle2 := by decide

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI103N1)

def MemCI103N1 : IdealMemCertificate O ℤ B I103N1
  ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![62, 12, 1, 0, 0], ![40, 11, 0, 1, 0], ![9, 88, 0, 0, 1]] ![333237, -13560011, -8544348, -9862751, 24852843] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI103N1
 g := ![6805022, -19316386, -8544348, -9862751, 24852843]
 hmem := by decide

def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [73, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 102], [0, 1]]
 g := ![![[87, 59], [17, 19], [24, 72], [25], [52], [35, 1]],![[92, 44], [64, 84], [72, 31], [25], [52], [70, 102]]]
 h' := ![![[35, 102], [98, 33], [102, 15], [38, 81], [3, 5], [20, 19], [0, 1]],![[0, 1], [17, 70], [9, 88], [92, 22], [75, 98], [67, 84], [35, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [23, 34]]
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
  P := [73, 68, 1]
  f := ofList [73, 68, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P103P1
  hneq := by decide
  hlen := by decide
  c := ![333237, -13560011, -8544348, -9862751, 24852843]
  a := ![-526, 2412, 1421, 1723, -4419]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI103N1
  hpmem := by 
    show  _ ∈ I103N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI103N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := PrimeIdeal_isPrime PI103N1
def MulI103N0 : IdealMulEqCertificate O ℤ timesTableO (I103N0) I103N1
  ![![103, 0, 0, 0, 0], ![183, 88, 62, 77, -200]] ![![103, 0, 0, 0, 0], ![-22, 11, -4, -5, 13]]
  ![![103, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![10609, 0, 0, 0, 0], ![-2266, 1133, -412, -515, 1339]], ![![18849, 9064, 6386, 7931, -20600], ![7210, 3193, 1442, 2369, -5871]]]
 hmul := by decide
 f :=  ![![![![2978691145940746298218151, 2434914448450581630723628, -726867436645009339442256, 1097148476623141824436432, -2782821577345085115076078], ![-752447567182153387215881, 8982194940363112618989762, 173508018480776949, 0, 0]], ![![-341062568136, -625282, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![103, 0, 0, 0, 0]], ![![-22, 11, -4, -5, 13]]], ![![![183, 88, 62, 77, -200]], ![![70, 31, 14, 23, -57]]]]
 hle1 := by decide
 hle2 := by decide

def PBC103 : PrimesBelowPCertificate 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI103N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl

