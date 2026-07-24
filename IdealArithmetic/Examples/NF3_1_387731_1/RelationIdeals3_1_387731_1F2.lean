import IdealArithmetic.Examples.NF3_1_387731_1.PrimesBelow3_1_387731_1F2
import IdealArithmetic.Examples.NF3_1_387731_1.ClassGroupData3_1_387731_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 2 ![![83, 0, 0], ![-5, 1, 0]]
  ![0, -1, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![166, 0, 0], ![-10, 2, 0]]
    hsu := by decide
    w := ![![0, -2, 2], ![4, -30, -4]]
    hw := by decide
    g := ![![![-33, -2680, -17], ![-1340, 0, -231]], ![![1, 162, 1], ![82, 0, 14]]]
    h := ![![![0, 1, -1], ![0, 21, 0]], ![![24, -3, -2], ![398, 41, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {2} * I83N1 =  Ideal.span {B.equivFun.symm ![0, -1, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E83RS1 


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0], ![-19, 1, 0]]
  ![-2, 13, -7] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![202, 0, 0], ![-38, 2, 0]]
    hsu := by decide
    w := ![![-4, 26, -14], ![-28, 214, 52]]
    hw := by decide
    g := ![![![31491, 60, 337], ![-420, 375, 0]], ![![-5881, -12, -63], ![80, -70, 0]]]
    h := ![![![6, 13, -3], ![32, 74, 0]], ![![-186, 21, -2], ![-988, 57, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![-2, 13, -7]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 5 ![![103, 0, 0], ![15, 1, 0]]
  ![193484840, 230538, 6678743] ![![5, 0, 0], ![17, -2, 1]] where
    su := ![![515, 0, 0], ![75, 5, 0]]
    hsu := by decide
    w := ![![967424200, 1152690, 33393715], ![3230055745, 3848625, 111495620]]
    hw := by decide
    g := ![![![195, 3157, 1903], ![-172, 0, 0]], ![![-25, -24, 395], ![12, 0, 0]]]
    h := ![![![11009485760, 754481710, 5224589], ![-75585569896, -132863481, 0]], ![![36758696738, 2519079028, 17443972], ![-252366650191, -443607498, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {5} * I103N0 =  Ideal.span {B.equivFun.symm ![193484840, 230538, 6678743]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 10 ![![103, 0, 0], ![21, 1, 0]]
  ![8, -59, -5] ![![10, 0, 0], ![34, 1, 2]] where
    su := ![![1030, 0, 0], ![210, 10, 0]]
    hsu := by decide
    w := ![![80, -590, -50], ![-210, 1500, -100]]
    hw := by decide
    g := ![![![3392, -1077, -814], ![11267, 0, 0]], ![![663, -222, -169], ![2322, 0, 0]]]
    h := ![![![1172, 39, -3], ![-5748, 76, 0]], ![![-3150, -159, -2], ![15449, 49, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {10} * I103N1 =  Ideal.span {B.equivFun.symm ![8, -59, -5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 2 ![![103, 0, 0], ![-37, 1, 0]]
  ![-19, 118, -91] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![206, 0, 0], ![-74, 2, 0]]
    hsu := by decide
    w := ![![-38, 236, -182], ![-364, 2738, 472]]
    hw := by decide
    g := ![![![4415848, 4209, 152427], ![2105, 0, 0]], ![![-1580356, -1507, -54551], ![-752, 0, 0]]]
    h := ![![![-770, 23, -1], ![-2143, 3, 0]], ![![-7738, 243, 0], ![-21536, 59, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {2} * I103N2 =  Ideal.span {B.equivFun.symm ![-19, 118, -91]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E103RS2 


noncomputable def E109RS1 : RelationCertificate Table 10 ![![109, 0, 0], ![-7, 1, 0]]
  ![-7, 1, 0] ![![10, 0, 0], ![34, 1, 2]] where
    su := ![![1090, 0, 0], ![-70, 10, 0]]
    hsu := by decide
    w := ![![-70, 10, 0], ![-230, -30, -10]]
    hw := by decide
    g := ![![![-26, -1, -1], ![3, 0, 0]], ![![-33, -1, -2], ![10, 0, 0]]]
    h := ![![![-490, 76, -4], ![-7629, 109, 0]], ![![-1600, 230, -1], ![-24911, 27, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {10} * I109N1 =  Ideal.span {B.equivFun.symm ![-7, 1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E109RS1 


noncomputable def E127RS1 : RelationCertificate Table 2 ![![127, 0, 0], ![-22, 1, 0]]
  ![84767, 101, 2926] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![254, 0, 0], ![-44, 2, 0]]
    hsu := by decide
    w := ![![169534, 202, 5852], ![11704, 14, 404]]
    hw := by decide
    g := ![![![-3, 3, -80], ![3, 0, 0]], ![![-2, 14, 14], ![7, 0, 0]]]
    h := ![![![1454653, -67008, 198], ![8393462, -5555, 0]], ![![100452, -4608, 10], ![579616, -267, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {2} * I127N1 =  Ideal.span {B.equivFun.symm ![84767, 101, 2926]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 5 ![![131, 0, 0], ![37, 1, 0]]
  ![-90, 618, -157] ![![5, 0, 0], ![17, -2, 1]] where
    su := ![![655, 0, 0], ![185, 5, 0]]
    hsu := by decide
    w := ![![-450, 3090, -785], ![2355, -17735, -3150]]
    hw := by decide
    g := ![![![1244020, 1454823, -254302], ![3596923, 0, 0]], ![![352672, 412438, -72094], ![1019717, 0, 0]]]
    h := ![![![-9532, -308, -7], ![33746, 190, 0]], ![![49450, 1450, 10], ![-175067, -485, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {5} * I131N1 =  Ideal.span {B.equivFun.symm ![-90, 618, -157]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 2 ![![137, 0, 0], ![22, 1, 0]]
  ![1, -4, 15] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![274, 0, 0], ![44, 2, 0]]
    hsu := by decide
    w := ![![2, -8, 30], ![60, -438, -16]]
    hw := by decide
    g := ![![![96094, 91, 3317], ![47, 0, 0]], ![![15528, 14, 536], ![9, 0, 0]]]
    h := ![![![9, -6, -1], ![-56, 38, 0]], ![![1018, 45, 0], ![-6338, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {2} * I137N1 =  Ideal.span {B.equivFun.symm ![1, -4, 15]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E137RS1 
