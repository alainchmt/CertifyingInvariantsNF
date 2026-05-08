
import IdealArithmetic.Examples.NF4_4_54381317_1.RI4_4_54381317_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic

set_option linter.all false

open Classical Polynomial

noncomputable section 
instance hp661 : Fact (Nat.Prime 661) := {out := by norm_num}
def I661N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![661, 0, 0, 0], ![-209, -67, -4, 1]] i)))

def SI661N0: IdealEqSpanCertificate timesTableO I661N0
 ![![661, 0, 0, 0], ![-209, -67, -4, 1]] 
 ![![661, 0, 0, 0], ![0, 661, 0, 0], ![417, 583, 1, 0], ![137, 282, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![661, 0, 0, 0], ![0, 661, 0, 0], ![0, 0, 661, 0], ![0, 0, 0, 661]], ![![-209, -67, -4, 1], ![383, 123, 13, -3], ![-1149, -613, -117, 10], ![3830, 2171, 187, -107]]]
  hmulB := by decide
  f := ![![![80560672, 25877073, 2866026, -658119], ![-28112991, -154376550, 0, 0]], ![![-155212, -49855, -5522, 1268], ![54202, 297450, 0, 0]], ![![50685773, 16280891, 1803197, -414064], ![-17687696, -97128000, 0, 0]], ![![16630944, 5342063, 591662, -135862], ![-5803567, -31869450, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-417, -583, 661, 0], ![-137, -282, 0, 661]], ![![2, 3, -4, 1], ![-7, -10, 13, -3], ![70, 98, -117, 10], ![-90, -116, 187, -107]]]
  hle1 := by decide
  hle2 := by decide

lemma NI661N0 : Nat.card (O ⧸ I661N0) = 436921 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI661N0)

def MemCI661N0 : IdealMemCertificate B I661N0
  ![![661, 0, 0, 0], ![0, 661, 0, 0], ![417, 583, 1, 0], ![137, 282, 0, 1]] ![33191, 29457, 8016, 416] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI661N0
 g := ![-5093, -7203, 8016, 416]
 hmem := by decide

def P661P0 : CertificateIrreducibleZModOfList' 661 2 2 9 [253, 244, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [417, 660], [0, 1]]
 g := ![![[628, 423], [126], [244, 646], [188], [412, 205], [85], [245], [531, 46], [1]],![[532, 238], [126], [599, 15], [188], [628, 456], [85], [245], [544, 615], [1]]]
 h' := ![![[417, 660], [170, 111], [402, 470], [511, 549], [202, 74], [547, 463], [631, 561], [501, 144], [408, 417], [0, 1]],![[0, 1], [187, 550], [75, 191], [77, 112], [654, 587], [606, 198], [574, 100], [398, 517], [454, 244], [417, 660]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [609]]
 b := ![[], [133, 635]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI661N0 : CertifiedPrimeIdeal O 661 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I661N0
  hcard := NI661N0
  P := [253, 244, 1]
  f := ofList [253, 244, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P661P0
  hneq := by decide
  hlen := by decide
  c := ![33191, 29457, 8016, 416]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI661N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI661N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI661N0 : Ideal.IsPrime I661N0 := CertifiedPrimeIdeal.isPrime PI661N0
def I661N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![661, 0, 0, 0], ![14, 1, 0, 0]] i)))

def SI661N1: IdealEqSpanCertificate timesTableO I661N1
 ![![661, 0, 0, 0], ![14, 1, 0, 0]] 
 ![![661, 0, 0, 0], ![14, 1, 0, 0], ![465, 0, 1, 0], ![100, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![661, 0, 0, 0], ![0, 661, 0, 0], ![0, 0, 661, 0], ![0, 0, 0, 661]], ![![14, 1, 0, 0], ![0, 14, 1, 0], ![0, 0, 14, 1], ![383, 332, 80, 15]]]
  hmulB := by decide
  f := ![![![11649, -2528114, -180723, -6], ![-549952, 119402379, 3966, 0]], ![![210, -53563, -3841, -1], ![-9914, 2529647, 661, 0]], ![![8163, -1778481, -127146, -5], ![-385377, 83997237, 3305, 0]], ![![1746, -382495, -27344, -1], ![-82429, 18065116, 662, 0]]]
  g := ![![![1, 0, 0, 0], ![-14, 661, 0, 0], ![-465, 0, 661, 0], ![-100, 0, 0, 661]], ![![0, 1, 0, 0], ![-1, 14, 1, 0], ![-10, 0, 14, 1], ![-65, 332, 80, 15]]]
  hle1 := by decide
  hle2 := by decide

lemma NI661N1 : Nat.card (O ⧸ I661N1) = 661 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI661N1)

lemma isPrimeI661N1 : Ideal.IsPrime I661N1 := prime_ideal_of_norm_prime hp661.out _ NI661N1
def I661N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![661, 0, 0, 0], ![63, 1, 0, 0]] i)))

def SI661N2: IdealEqSpanCertificate timesTableO I661N2
 ![![661, 0, 0, 0], ![63, 1, 0, 0]] 
 ![![661, 0, 0, 0], ![63, 1, 0, 0], ![658, 0, 1, 0], ![189, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![661, 0, 0, 0], ![0, 661, 0, 0], ![0, 0, 661, 0], ![0, 0, 0, 661]], ![![63, 1, 0, 0], ![0, 63, 1, 0], ![0, 0, 63, 1], ![383, 332, 80, 64]]]
  hmulB := by decide
  f := ![![![2458, -27870, -506, -1], ![-25779, 292823, 661, 0]], ![![63, -2771, -107, -1], ![-660, 29084, 661, 0]], ![![2464, -27744, -504, -1], ![-25842, 291502, 661, 0]], ![![567, -8049, -191, -1], ![-5946, 84545, 662, 0]]]
  g := ![![![1, 0, 0, 0], ![-63, 661, 0, 0], ![-658, 0, 661, 0], ![-189, 0, 0, 661]], ![![0, 1, 0, 0], ![-7, 63, 1, 0], ![-63, 0, 63, 1], ![-129, 332, 80, 64]]]
  hle1 := by decide
  hle2 := by decide

lemma NI661N2 : Nat.card (O ⧸ I661N2) = 661 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI661N2)

lemma isPrimeI661N2 : Ideal.IsPrime I661N2 := prime_ideal_of_norm_prime hp661.out _ NI661N2
def MulI661N0 : IdealMulEqCertificate timesTableO (I661N0) I661N1
  ![![661, 0, 0, 0], ![-209, -67, -4, 1]] ![![661, 0, 0, 0], ![14, 1, 0, 0]]
  ![![661, 0, 0, 0], ![-1221, -815, -43, 11]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![436921, 0, 0, 0], ![9254, 661, 0, 0]], ![![-138149, -44287, -2644, 661], ![-2543, -815, -43, 11]]]
 hmul := by decide
 f :=  ![![![![16131966983406663, -3495977115709930353, -249906952467479011, -7999677383632], ![-761659234698296305, 165114466643168230079, 5287782490984396, 0]], ![![4259595564, 0, 0, 0], ![47592, 0, 0, 0]]], ![![![-29799089239612935, 6457794896173594069, 461629978900779419, 14777063484455], ![1406942595921234966, -305000669249560493778, -9767631094866726, 0]], ![![-7868356566, 0, 0, 0], ![-87912, 0, 0, 0]]]]
 g :=  ![![![![661, 0, 0, 0], ![0, 0, 0, 0]], ![![14, 1, 0, 0], ![0, 0, 0, 0]]], ![![![1012, 748, 39, -10], ![661, 0, 0, 0]], ![![1219, 815, 43, -11], ![662, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI661N1 : IdealMulEqCertificate timesTableO (I661N0*I661N1) I661N2
  ![![661, 0, 0, 0], ![-1221, -815, -43, 11]] ![![661, 0, 0, 0], ![63, 1, 0, 0]]
  ![![661, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI661N0
 hI2 := rfl
 M :=  ![![![436921, 0, 0, 0], ![41643, 661, 0, 0]], ![![-807081, -538715, -28423, 7271], ![-72710, -48914, -2644, 661]]]
 hmul := by decide
 f :=  ![![![![9405268, -96163176, -1542405, -250], ![-98643225, 1010540907, 143998, 0]], ![![1932, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![661, 0, 0, 0]], ![![63, 1, 0, 0]]], ![![![-1221, -815, -43, 11]], ![![-110, -74, -4, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC661 : IsPrimesAboveP 661 ![I661N0, I661N1, I661N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI661N0
    exact isPrimeI661N1
    exact isPrimeI661N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI661N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp673 : Fact (Nat.Prime 673) := {out := by norm_num}
def I673N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![673, 0, 0, 0], ![27, 1, 0, 0]] i)))

def SI673N0: IdealEqSpanCertificate timesTableO I673N0
 ![![673, 0, 0, 0], ![27, 1, 0, 0]] 
 ![![673, 0, 0, 0], ![27, 1, 0, 0], ![617, 0, 1, 0], ![166, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![673, 0, 0, 0], ![0, 673, 0, 0], ![0, 0, 673, 0], ![0, 0, 0, 673]], ![![27, 1, 0, 0], ![0, 27, 1, 0], ![0, 0, 27, 1], ![383, 332, 80, 28]]]
  hmulB := by decide
  f := ![![![8992, 306, 113075, 4188], ![-224109, 673, -2818524, 0]], ![![324, -15, 9422, 349], ![-8075, 673, -234877, 0]], ![![8264, 279, 103652, 3839], ![-205965, 674, -2583647, 0]], ![![2212, 56, 27890, 1033], ![-55130, 646, -695208, 0]]]
  g := ![![![1, 0, 0, 0], ![-27, 673, 0, 0], ![-617, 0, 673, 0], ![-166, 0, 0, 673]], ![![0, 1, 0, 0], ![-2, 27, 1, 0], ![-25, 0, 27, 1], ![-93, 332, 80, 28]]]
  hle1 := by decide
  hle2 := by decide

lemma NI673N0 : Nat.card (O ⧸ I673N0) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI673N0)

lemma isPrimeI673N0 : Ideal.IsPrime I673N0 := prime_ideal_of_norm_prime hp673.out _ NI673N0
def I673N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![673, 0, 0, 0], ![31, 1, 0, 0]] i)))

def SI673N1: IdealEqSpanCertificate timesTableO I673N1
 ![![673, 0, 0, 0], ![31, 1, 0, 0]] 
 ![![673, 0, 0, 0], ![31, 1, 0, 0], ![385, 0, 1, 0], ![179, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![673, 0, 0, 0], ![0, 673, 0, 0], ![0, 0, 673, 0], ![0, 0, 0, 673]], ![![31, 1, 0, 0], ![0, 31, 1, 0], ![0, 0, 31, 1], ![383, 332, 80, 32]]]
  hmulB := by decide
  f := ![![![9239, -716236, -23176, -2], ![-200554, 15555722, 1346, 0]], ![![341, -33035, -1097, -1], ![-7402, 717418, 673, 0]], ![![5303, -409742, -13254, -1], ![-115114, 8899080, 673, 0]], ![![2467, -190538, -6180, -1], ![-53552, 4138246, 674, 0]]]
  g := ![![![1, 0, 0, 0], ![-31, 673, 0, 0], ![-385, 0, 673, 0], ![-179, 0, 0, 673]], ![![0, 1, 0, 0], ![-2, 31, 1, 0], ![-18, 0, 31, 1], ![-69, 332, 80, 32]]]
  hle1 := by decide
  hle2 := by decide

lemma NI673N1 : Nat.card (O ⧸ I673N1) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI673N1)

lemma isPrimeI673N1 : Ideal.IsPrime I673N1 := prime_ideal_of_norm_prime hp673.out _ NI673N1
def I673N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![673, 0, 0, 0], ![37, 1, 0, 0]] i)))

def SI673N2: IdealEqSpanCertificate timesTableO I673N2
 ![![673, 0, 0, 0], ![37, 1, 0, 0]] 
 ![![673, 0, 0, 0], ![37, 1, 0, 0], ![650, 0, 1, 0], ![178, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![673, 0, 0, 0], ![0, 673, 0, 0], ![0, 0, 673, 0], ![0, 0, 0, 673]], ![![37, 1, 0, 0], ![0, 37, 1, 0], ![0, 0, 37, 1], ![383, 332, 80, 38]]]
  hmulB := by decide
  f := ![![![13247, 210, 1653674, 44694], ![-240934, 2692, -30079062, 0]], ![![703, -18, 98937, 2674], ![-12786, 673, -1799602, 0]], ![![12768, 197, 1597138, 43166], ![-232222, 2693, -29050718, 0]], ![![3440, 21, 437375, 11821], ![-62566, 1309, -7955532, 0]]]
  g := ![![![1, 0, 0, 0], ![-37, 673, 0, 0], ![-650, 0, 673, 0], ![-178, 0, 0, 673]], ![![0, 1, 0, 0], ![-3, 37, 1, 0], ![-36, 0, 37, 1], ![-105, 332, 80, 38]]]
  hle1 := by decide
  hle2 := by decide

lemma NI673N2 : Nat.card (O ⧸ I673N2) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI673N2)

lemma isPrimeI673N2 : Ideal.IsPrime I673N2 := prime_ideal_of_norm_prime hp673.out _ NI673N2
def I673N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![673, 0, 0, 0], ![-96, 1, 0, 0]] i)))

def SI673N3: IdealEqSpanCertificate timesTableO I673N3
 ![![673, 0, 0, 0], ![-96, 1, 0, 0]] 
 ![![673, 0, 0, 0], ![577, 1, 0, 0], ![206, 0, 1, 0], ![259, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![673, 0, 0, 0], ![0, 673, 0, 0], ![0, 0, 673, 0], ![0, 0, 0, 673]], ![![-96, 1, 0, 0], ![0, -96, 1, 0], ![0, 0, -96, 1], ![383, 332, 80, -95]]]
  hmulB := by decide
  f := ![![![128161, -432183, 4584, -1], ![898455, -3020424, 673, 0]], ![![109921, -370553, 3944, -1], ![770586, -2589704, 673, 0]], ![![39470, -132219, 1469, -1], ![276699, -924028, 673, 0]], ![![49411, -166197, 1822, -1], ![346389, -1161502, 674, 0]]]
  g := ![![![1, 0, 0, 0], ![-577, 673, 0, 0], ![-206, 0, 673, 0], ![-259, 0, 0, 673]], ![![-1, 1, 0, 0], ![82, -96, 1, 0], ![29, 0, -96, 1], ![-272, 332, 80, -95]]]
  hle1 := by decide
  hle2 := by decide

lemma NI673N3 : Nat.card (O ⧸ I673N3) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI673N3)

lemma isPrimeI673N3 : Ideal.IsPrime I673N3 := prime_ideal_of_norm_prime hp673.out _ NI673N3
def MulI673N0 : IdealMulEqCertificate timesTableO (I673N0) I673N1
  ![![673, 0, 0, 0], ![27, 1, 0, 0]] ![![673, 0, 0, 0], ![31, 1, 0, 0]]
  ![![673, 0, 0, 0], ![-73, -67, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![452929, 0, 0, 0], ![20863, 673, 0, 0]], ![![18171, 673, 0, 0], ![837, 58, 1, 0]]]
 hmul := by decide
 f :=  ![![![![-1825037121541588, 140845721719588321, 4554929120048039, 310309986125], ![39616696894155776, -3058993300553413966, -208838620721744, 0]], ![![4902928842936, 0, 0, 0], ![-80087, 40123587, 0, 0]]], ![![![197598080410180, -15249467486053733, -493165448473775, -33597485151], ![-4289328236712656, 331199402490319534, 22611107513078, 0]], ![![-530843628504, 0, 0, 0], ![8687, -4344214, 0, 0]]]]
 g :=  ![![![![2687516318, 1805044205, 90154085, -20750865], ![-471779730, -4812370625, 0, 0]], ![![123784130, 83138422, 4152402, -955763], ![-21729151, -221652550, 0, 0]]], ![![![107810744, 72410044, 3616566, -832429], ![-18925433, -193050050, 0, 0]], ![![4965662, 3335143, 166576, -38341], ![-871532, -8891675, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI673N1 : IdealMulEqCertificate timesTableO (I673N0*I673N1) I673N2
  ![![673, 0, 0, 0], ![-73, -67, -4, 1]] ![![673, 0, 0, 0], ![37, 1, 0, 0]]
  ![![673, 0, 0, 0], ![-4337, -2220, -135, 34]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI673N0
 hI2 := rfl
 M :=  ![![![452929, 0, 0, 0], ![24901, 673, 0, 0]], ![![-49129, -45091, -2692, 673], ![-2318, -2220, -135, 34]]]
 hmul := by decide
 f :=  ![![![![17389482617494109316, -3475423268458619374239, -94226095675488174387, -7649595579360509], ![-316300579327462867146, 63223680015900430382030, 5148172804945109040, 0]], ![![5019964513211, 0, 0, 0], ![6057, 0, 0, 0]]], ![![![-112063409424607438980, 22396743435326509024497, 607223214769002634106, 49296450055399943], ![2038342491383556678202, -407433693963070047585412, -33176478537021019864, 0]], ![![-32350263139803, 0, 0, 0], ![-39033, 0, 0, 0]]]]
 g :=  ![![![![673, 0, 0, 0], ![0, 0, 0, 0]], ![![37, 1, 0, 0], ![0, 0, 0, 0]]], ![![![4264, 2153, 131, -33], ![673, 0, 0, 0]], ![![3, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI673N2 : IdealMulEqCertificate timesTableO (I673N0*I673N1*I673N2) I673N3
  ![![673, 0, 0, 0], ![-4337, -2220, -135, 34]] ![![673, 0, 0, 0], ![-96, 1, 0, 0]]
  ![![673, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI673N1
 hI2 := rfl
 M :=  ![![![452929, 0, 0, 0], ![-64608, 673, 0, 0]], ![![-2918801, -1494060, -90855, 22882], ![429374, 220071, 13460, -3365]]]
 hmul := by decide
 f :=  ![![![![52774094431455, -164552020489440, 1743848762622, -369708388], ![369968386924680, -1149724391782380, 248810549736, 0]], ![![93982, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![673, 0, 0, 0]], ![![-96, 1, 0, 0]]], ![![![-4337, -2220, -135, 34]], ![![638, 327, 20, -5]]]]
 hle1 := by decide
 hle2 := by decide

def PBC673 : IsPrimesAboveP 673 ![I673N0, I673N1, I673N2, I673N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI673N0
    exact isPrimeI673N1
    exact isPrimeI673N2
    exact isPrimeI673N3
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI673N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp677 : Fact (Nat.Prime 677) := {out := by norm_num}
def I677N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![677, 0, 0, 0], ![-316, 250, -4, 1]] i)))

def SI677N0: IdealEqSpanCertificate timesTableO I677N0
 ![![677, 0, 0, 0], ![-316, 250, -4, 1]] 
 ![![677, 0, 0, 0], ![0, 677, 0, 0], ![622, 458, 1, 0], ![141, 51, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![677, 0, 0, 0], ![0, 677, 0, 0], ![0, 0, 677, 0], ![0, 0, 0, 677]], ![![-316, 250, -4, 1], ![383, 16, 330, -3], ![-1149, -613, -224, 327], ![125241, 107415, 25547, 103]]]
  hmulB := by decide
  f := ![![![25980001, 5124936, 26502288, -226140], ![-10390596, -54495792, 0, 0]], ![![-83014, -16627, -84940, 724], ![33850, 174666, 0, 0]], ![![23813074, 4697438, 24291757, -207278], ![-9523838, -49950348, 0, 0]], ![![5404635, 1066137, 5513280, -47044], ![-2161545, -11336778, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-622, -458, 677, 0], ![-141, -51, 0, 677]], ![![3, 3, -4, 1], ![-302, -223, 330, -3], ![136, 126, -224, 327], ![-23308, -17132, 25547, 103]]]
  hle1 := by decide
  hle2 := by decide

lemma NI677N0 : Nat.card (O ⧸ I677N0) = 458329 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI677N0)

def MemCI677N0 : IdealMemCertificate B I677N0
  ![![677, 0, 0, 0], ![0, 677, 0, 0], ![622, 458, 1, 0], ![141, 51, 0, 1]] ![1552787, 1298273, 268676, -5939] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI677N0
 g := ![-243318, -179398, 268676, -5939]
 hmem := by decide

def P677P0 : CertificateIrreducibleZModOfList' 677 2 2 9 [162, 222, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [455, 676], [0, 1]]
 g := ![![[553, 631], [383], [460, 459], [60], [668], [383, 542], [591], [115, 540], [1]],![[610, 46], [383], [112, 218], [60], [668], [565, 135], [591], [64, 137], [1]]]
 h' := ![![[455, 676], [30, 595], [627, 315], [618, 62], [557, 74], [238, 599], [379, 178], [326, 567], [515, 455], [0, 1]],![[0, 1], [632, 82], [428, 362], [394, 615], [377, 603], [629, 78], [129, 499], [374, 110], [378, 222], [455, 676]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [326]]
 b := ![[], [491, 163]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI677N0 : CertifiedPrimeIdeal O 677 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I677N0
  hcard := NI677N0
  P := [162, 222, 1]
  f := ofList [162, 222, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P677P0
  hneq := by decide
  hlen := by decide
  c := ![1552787, 1298273, 268676, -5939]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI677N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI677N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI677N0 : Ideal.IsPrime I677N0 := CertifiedPrimeIdeal.isPrime PI677N0
def I677N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![677, 0, 0, 0], ![-155, -2, -4, 1]] i)))

def SI677N1: IdealEqSpanCertificate timesTableO I677N1
 ![![677, 0, 0, 0], ![-155, -2, -4, 1]] 
 ![![677, 0, 0, 0], ![0, 677, 0, 0], ![327, 218, 1, 0], ![476, 193, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![677, 0, 0, 0], ![0, 677, 0, 0], ![0, 0, 677, 0], ![0, 0, 0, 677]], ![![-155, -2, -4, 1], ![383, 177, 78, -3], ![-1149, -613, -63, 75], ![28725, 23751, 5387, 12]]]
  hmulB := by decide
  f := ![![![8392338, 4078356, 1788288, -66351], ![-1943667, -15621098, 0, 0]], ![![-101049, -49135, -21544, 799], ![23695, 188206, 0, 0]], ![![4021052, 1954078, 856829, -31791], ![-931275, -7484594, 0, 0]], ![![5871903, 2853493, 1251208, -46424], ![-1359661, -10929570, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-327, -218, 677, 0], ![-476, -193, 0, 677]], ![![1, 1, -4, 1], ![-35, -24, 78, -3], ![-24, -2, -63, 75], ![-2568, -1703, 5387, 12]]]
  hle1 := by decide
  hle2 := by decide

lemma NI677N1 : Nat.card (O ⧸ I677N1) = 458329 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI677N1)

def MemCI677N1 : IdealMemCertificate B I677N1
  ![![677, 0, 0, 0], ![0, 677, 0, 0], ![327, 218, 1, 0], ![476, 193, 0, 1]] ![275025, 239738, 62097, 3309] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI677N1
 g := ![-31914, -20585, 62097, 3309]
 hmem := by decide

def P677P1 : CertificateIrreducibleZModOfList' 677 2 2 9 [245, 215, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [462, 676], [0, 1]]
 g := ![![[443, 85], [401], [362, 441], [637], [508], [503, 384], [232], [400, 189], [1]],![[447, 592], [401], [327, 236], [637], [508], [537, 293], [232], [385, 488], [1]]]
 h' := ![![[462, 676], [606, 631], [674, 194], [458, 656], [549, 433], [656, 339], [173, 559], [165, 159], [432, 462], [0, 1]],![[0, 1], [341, 46], [261, 483], [234, 21], [203, 244], [210, 338], [494, 118], [507, 518], [621, 215], [462, 676]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [487]]
 b := ![[], [281, 582]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI677N1 : CertifiedPrimeIdeal O 677 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I677N1
  hcard := NI677N1
  P := [245, 215, 1]
  f := ofList [245, 215, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P677P1
  hneq := by decide
  hlen := by decide
  c := ![275025, 239738, 62097, 3309]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI677N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI677N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI677N1 : Ideal.IsPrime I677N1 := CertifiedPrimeIdeal.isPrime PI677N1
def MulI677N0 : IdealMulEqCertificate timesTableO (I677N0) I677N1
  ![![677, 0, 0, 0], ![-316, 250, -4, 1]] ![![677, 0, 0, 0], ![-155, -2, -4, 1]]
  ![![677, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![458329, 0, 0, 0], ![-104935, -1354, -2708, 677]], ![![-213932, 169250, -2708, 677], ![178051, 71085, 26403, -1354]]]
 hmul := by decide
 f :=  ![![![![84122457108130662297892948, 40880792856080768487736268, 17925497322971182885000528, -665085491166422594737303], ![-19487606369653567721245929, -156583487538982096365889546, 0, 0]], ![![21272375374633863206, -208956072, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![677, 0, 0, 0]], ![![-155, -2, -4, 1]]], ![![![-316, 250, -4, 1]], ![![263, 105, 39, -2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC677 : IsPrimesAboveP 677 ![I677N0, I677N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI677N0
    exact isPrimeI677N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI677N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp683 : Fact (Nat.Prime 683) := {out := by norm_num}
def I683N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![683, 0, 0, 0], ![-30, -67, -4, 1]] i)))

def SI683N0: IdealEqSpanCertificate timesTableO I683N0
 ![![683, 0, 0, 0], ![-30, -67, -4, 1]] 
 ![![683, 0, 0, 0], ![0, 683, 0, 0], ![293, 101, 1, 0], ![459, 337, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![683, 0, 0, 0], ![0, 683, 0, 0], ![0, 0, 683, 0], ![0, 0, 0, 683]], ![![-30, -67, -4, 1], ![383, 302, 13, -3], ![-1149, -613, 62, 10], ![3830, 2171, 187, 72]]]
  hmulB := by decide
  f := ![![![247661, 193419, 8278, -1907], ![-29369, -443950, 0, 0]], ![![-9898, -7717, -330, 76], ![1366, 17758, 0, 0]], ![![104785, 81844, 3503, -807], ![-12291, -187824, 0, 0]], ![![161551, 126172, 5400, -1244], ![-19111, -289588, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-293, -101, 683, 0], ![-459, -337, 0, 683]], ![![1, 0, -4, 1], ![-3, 0, 13, -3], ![-35, -15, 62, 10], ![-123, -60, 187, 72]]]
  hle1 := by decide
  hle2 := by decide

lemma NI683N0 : Nat.card (O ⧸ I683N0) = 466489 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI683N0)

def MemCI683N0 : IdealMemCertificate B I683N0
  ![![683, 0, 0, 0], ![0, 683, 0, 0], ![293, 101, 1, 0], ![459, 337, 0, 1]] ![30211, 25213, 5992, 632] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI683N0
 g := ![-2951, -1161, 5992, 632]
 hmem := by decide

def P683P0 : CertificateIrreducibleZModOfList' 683 2 2 9 [337, 300, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [383, 682], [0, 1]]
 g := ![![[161, 531], [475, 400], [311], [472, 27], [108], [151, 623], [264], [388, 527], [1]],![[0, 152], [0, 283], [311], [568, 656], [108], [393, 60], [264], [61, 156], [1]]]
 h' := ![![[383, 682], [430, 434], [536, 20], [75, 440], [669, 572], [338, 461], [109, 504], [380, 565], [346, 383], [0, 1]],![[0, 1], [0, 249], [0, 663], [577, 243], [502, 111], [4, 222], [535, 179], [264, 118], [190, 300], [383, 682]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [198]]
 b := ![[], [507, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI683N0 : CertifiedPrimeIdeal O 683 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I683N0
  hcard := NI683N0
  P := [337, 300, 1]
  f := ofList [337, 300, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P683P0
  hneq := by decide
  hlen := by decide
  c := ![30211, 25213, 5992, 632]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI683N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI683N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI683N0 : Ideal.IsPrime I683N0 := CertifiedPrimeIdeal.isPrime PI683N0
def I683N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![683, 0, 0, 0], ![9, 1, 0, 0]] i)))

def SI683N1: IdealEqSpanCertificate timesTableO I683N1
 ![![683, 0, 0, 0], ![9, 1, 0, 0]] 
 ![![683, 0, 0, 0], ![9, 1, 0, 0], ![602, 0, 1, 0], ![46, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![683, 0, 0, 0], ![0, 683, 0, 0], ![0, 0, 683, 0], ![0, 0, 0, 683]], ![![9, 1, 0, 0], ![0, 9, 1, 0], ![0, 0, 9, 1], ![383, 332, 80, 10]]]
  hmulB := by decide
  f := ![![![1342, -51853, -5787, -1], ![-101767, 3946374, 683, 0]], ![![-9, -703, -87, -1], ![684, 53274, 683, 0]], ![![1180, -45706, -5102, -1], ![-89482, 3478520, 683, 0]], ![![89, -3509, -400, -1], ![-6749, 267044, 684, 0]]]
  g := ![![![1, 0, 0, 0], ![-9, 683, 0, 0], ![-602, 0, 683, 0], ![-46, 0, 0, 683]], ![![0, 1, 0, 0], ![-1, 9, 1, 0], ![-8, 0, 9, 1], ![-75, 332, 80, 10]]]
  hle1 := by decide
  hle2 := by decide

lemma NI683N1 : Nat.card (O ⧸ I683N1) = 683 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI683N1)

lemma isPrimeI683N1 : Ideal.IsPrime I683N1 := prime_ideal_of_norm_prime hp683.out _ NI683N1
def I683N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![683, 0, 0, 0], ![-111, 1, 0, 0]] i)))

def SI683N2: IdealEqSpanCertificate timesTableO I683N2
 ![![683, 0, 0, 0], ![-111, 1, 0, 0]] 
 ![![683, 0, 0, 0], ![572, 1, 0, 0], ![656, 0, 1, 0], ![418, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![683, 0, 0, 0], ![0, 683, 0, 0], ![0, 0, 683, 0], ![0, 0, 0, 683]], ![![-111, 1, 0, 0], ![0, -111, 1, 0], ![0, 0, -111, 1], ![383, 332, 80, -110]]]
  hmulB := by decide
  f := ![![![11545, 784, 3818392, -34400], ![71032, 5464, 23495200, 0]], ![![9658, 690, 3205673, -28880], ![59422, 4781, 19725040, 0]], ![![11008, 789, 3667432, -33040], ![67728, 5465, 22566320, 0]], ![![6998, 510, 2336878, -21053], ![43056, 3526, 14379200, 0]]]
  g := ![![![1, 0, 0, 0], ![-572, 683, 0, 0], ![-656, 0, 683, 0], ![-418, 0, 0, 683]], ![![-1, 1, 0, 0], ![92, -111, 1, 0], ![106, 0, -111, 1], ![-287, 332, 80, -110]]]
  hle1 := by decide
  hle2 := by decide

lemma NI683N2 : Nat.card (O ⧸ I683N2) = 683 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI683N2)

lemma isPrimeI683N2 : Ideal.IsPrime I683N2 := prime_ideal_of_norm_prime hp683.out _ NI683N2
def MulI683N0 : IdealMulEqCertificate timesTableO (I683N0) I683N1
  ![![683, 0, 0, 0], ![-30, -67, -4, 1]] ![![683, 0, 0, 0], ![9, 1, 0, 0]]
  ![![683, 0, 0, 0], ![-570, -301, -23, 6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![466489, 0, 0, 0], ![6147, 683, 0, 0]], ![![-20490, -45761, -2732, 683], ![113, -301, -23, 6]]]
 hmul := by decide
 f :=  ![![![![441858795753882, -16274960851621615, -1814131991356376, -45761377274], ![-33507626773029849, 1238866585412143324, 23891135921060, 0]], ![![7363884755450, 0, 0, 0], ![185776, 0, 0, 0]]], ![![![-368759425054116, 13582495729619506, 1514009173368230, 38190796098], ![27964257591995292, -1033913399813316838, -19938680932597, 0]], ![![-6145632800975, 0, 0, 0], ![-155040, 0, 0, 0]]]]
 g :=  ![![![![683, 0, 0, 0], ![0, 0, 0, 0]], ![![9, 1, 0, 0], ![0, 0, 0, 0]]], ![![![540, 234, 19, -5], ![683, 0, 0, 0]], ![![1, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI683N1 : IdealMulEqCertificate timesTableO (I683N0*I683N1) I683N2
  ![![683, 0, 0, 0], ![-570, -301, -23, 6]] ![![683, 0, 0, 0], ![-111, 1, 0, 0]]
  ![![683, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI683N0
 hI2 := rfl
 M :=  ![![![466489, 0, 0, 0], ![-75813, 683, 0, 0]], ![![-389310, -205583, -15709, 4098], ![65568, 34833, 2732, -683]]]
 hmul := by decide
 f :=  ![![![![501973157, -124947567402, 1154595623, -261341], ![3088573930, -768793769276, 178327903, 0]], ![![28000, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![683, 0, 0, 0]], ![![-111, 1, 0, 0]]], ![![![-570, -301, -23, 6]], ![![96, 51, 4, -1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC683 : IsPrimesAboveP 683 ![I683N0, I683N1, I683N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI683N0
    exact isPrimeI683N1
    exact isPrimeI683N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI683N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp691 : Fact (Nat.Prime 691) := {out := by norm_num}
def I691N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![541, 268, 16, -4]] i)))

def SI691N0: IdealEqSpanCertificate timesTableO I691N0
 ![![541, 268, 16, -4]] 
 ![![691, 0, 0, 0], ![0, 691, 0, 0], ![150, 514, 1, 0], ![292, 607, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![541, 268, 16, -4], ![-1532, -787, -52, 12], ![4596, 2452, 173, -40], ![-15320, -8684, -748, 133]]]
  hmulB := by decide
  f := ![![![511, 268, 16, -4]], ![![-1532, -817, -52, 12]], ![![-1022, -546, -35, 8]], ![![-1152, -617, -40, 9]]]
  g := ![![![-1, -8, 16, -4], ![4, 27, -52, 12], ![-14, -90, 173, -40], ![84, 427, -748, 133]]]
  hle1 := by decide
  hle2 := by decide

lemma NI691N0 : Nat.card (O ⧸ I691N0) = 477481 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI691N0)

def MemCI691N0 : IdealMemCertificate B I691N0
  ![![691, 0, 0, 0], ![0, 691, 0, 0], ![150, 514, 1, 0], ![292, 607, 0, 1]] ![288053, 243947, 62406, 5270] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI691N0
 g := ![-15357, -50697, 62406, 5270]
 hmem := by decide

def P691P0 : CertificateIrreducibleZModOfList' 691 2 2 9 [502, 400, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [291, 690], [0, 1]]
 g := ![![[188, 574], [138, 143], [139], [210], [186, 54], [548, 193], [351], [549, 379], [1]],![[0, 117], [291, 548], [139], [210], [7, 637], [49, 498], [351], [278, 312], [1]]]
 h' := ![![[291, 690], [515, 580], [208, 88], [271, 39], [604, 625], [613, 259], [577, 350], [111, 385], [189, 291], [0, 1]],![[0, 1], [0, 111], [249, 603], [564, 652], [55, 66], [663, 432], [159, 341], [204, 306], [568, 400], [291, 690]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [249]]
 b := ![[], [24, 470]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI691N0 : CertifiedPrimeIdeal O 691 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I691N0
  hcard := NI691N0
  P := [502, 400, 1]
  f := ofList [502, 400, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P691P0
  hneq := by decide
  hlen := by decide
  c := ![288053, 243947, 62406, 5270]
  a := ![19, 1, -1, 3]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI691N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI691N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI691N0 : Ideal.IsPrime I691N0 := CertifiedPrimeIdeal.isPrime PI691N0
def I691N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![691, 0, 0, 0], ![218, 1, 0, 0]] i)))

def SI691N1: IdealEqSpanCertificate timesTableO I691N1
 ![![691, 0, 0, 0], ![218, 1, 0, 0]] 
 ![![691, 0, 0, 0], ![218, 1, 0, 0], ![155, 0, 1, 0], ![69, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![691, 0, 0, 0], ![0, 691, 0, 0], ![0, 0, 691, 0], ![0, 0, 0, 691]], ![![218, 1, 0, 0], ![0, 218, 1, 0], ![0, 0, 218, 1], ![383, 332, 80, 219]]]
  hmulB := by decide
  f := ![![![31393, -1600, 3918760, 17976], ![-99504, 5528, -12421416, 0]], ![![9810, -609, 1245213, 5712], ![-31094, 2073, -3946992, 0]], ![![7045, -404, 878974, 4032], ![-22330, 1383, -2786112, 0]], ![![2883, -354, 391308, 1795], ![-9138, 1164, -1240344, 0]]]
  g := ![![![1, 0, 0, 0], ![-218, 691, 0, 0], ![-155, 0, 691, 0], ![-69, 0, 0, 691]], ![![0, 1, 0, 0], ![-69, 218, 1, 0], ![-49, 0, 218, 1], ![-144, 332, 80, 219]]]
  hle1 := by decide
  hle2 := by decide

lemma NI691N1 : Nat.card (O ⧸ I691N1) = 691 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI691N1)

lemma isPrimeI691N1 : Ideal.IsPrime I691N1 := prime_ideal_of_norm_prime hp691.out _ NI691N1
def I691N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![691, 0, 0, 0], ![-42, 1, 0, 0]] i)))

def SI691N2: IdealEqSpanCertificate timesTableO I691N2
 ![![691, 0, 0, 0], ![-42, 1, 0, 0]] 
 ![![691, 0, 0, 0], ![649, 1, 0, 0], ![309, 0, 1, 0], ![540, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![691, 0, 0, 0], ![0, 691, 0, 0], ![0, 0, 691, 0], ![0, 0, 0, 691]], ![![-42, 1, 0, 0], ![0, -42, 1, 0], ![0, 0, -42, 1], ![383, 332, 80, -41]]]
  hmulB := by decide
  f := ![![![8359, 95, 3094007, -73667], ![137509, 4837, 50903897, 0]], ![![7813, 108, 2911559, -69323], ![128527, 4837, 47902193, 0]], ![![3741, 37, 1383561, -32942], ![61541, 2074, 22762922, 0]], ![![6492, 58, 2417893, -57569], ![106796, 3497, 39780180, 0]]]
  g := ![![![1, 0, 0, 0], ![-649, 691, 0, 0], ![-309, 0, 691, 0], ![-540, 0, 0, 691]], ![![-1, 1, 0, 0], ![39, -42, 1, 0], ![18, 0, -42, 1], ![-315, 332, 80, -41]]]
  hle1 := by decide
  hle2 := by decide

lemma NI691N2 : Nat.card (O ⧸ I691N2) = 691 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI691N2)

lemma isPrimeI691N2 : Ideal.IsPrime I691N2 := prime_ideal_of_norm_prime hp691.out _ NI691N2
def MulI691N0 : IdealMulEqCertificate timesTableO (I691N0) I691N1
  ![![541, 268, 16, -4]] ![![691, 0, 0, 0], ![218, 1, 0, 0]]
  ![![691, 0, 0, 0], ![-28065, -14582, -859, 215]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![373831, 185188, 11056, -2764], ![116406, 57637, 3436, -860]]]
 hmul := by decide
 f :=  ![![![![4862361919219710994709, -11709928070641946655017838, -53715368692862423809145, 219084032], ![-15412349019178074758456, 37117319766800937232532499, -151387066116, 0]]], ![![![-197298152290319335819283, 475149157996234416980453406, 2179587445106457663561969, -8889686829], ![625380840516562665372136, -1506094924569901370165865482, 6142773598830, 0]]]]
 g :=  ![![![![541, 268, 16, -4], ![0, 0, 0, 0]], ![![6, -1, 0, 0], ![-4, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI691N1 : IdealMulEqCertificate timesTableO (I691N0*I691N1) I691N2
  ![![691, 0, 0, 0], ![-28065, -14582, -859, 215]] ![![691, 0, 0, 0], ![-42, 1, 0, 0]]
  ![![691, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI691N0
 hI2 := rfl
 M :=  ![![![477481, 0, 0, 0], ![-29022, 691, 0, 0]], ![![-19392915, -10076162, -593569, 148565], ![1261075, 655759, 38696, -9674]]]
 hmul := by decide
 f :=  ![![![![132403331754349, -31605225623922083, 755200839574048, -66018968973], ![2178215780203349, -519929419535837062, 45575904750843, 0]], ![![200943300, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![691, 0, 0, 0]], ![![-42, 1, 0, 0]]], ![![![-28065, -14582, -859, 215]], ![![1825, 949, 56, -14]]]]
 hle1 := by decide
 hle2 := by decide

def PBC691 : IsPrimesAboveP 691 ![I691N0, I691N1, I691N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI691N0
    exact isPrimeI691N1
    exact isPrimeI691N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI691N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl

