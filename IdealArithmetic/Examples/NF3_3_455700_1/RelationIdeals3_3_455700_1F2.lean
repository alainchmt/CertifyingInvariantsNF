import IdealArithmetic.Examples.NF3_3_455700_1.PrimesBelow3_3_455700_1F2
import IdealArithmetic.Examples.NF3_3_455700_1.ClassGroupData3_3_455700_1

set_option linter.all false

noncomputable section


noncomputable def E101RS1 : RelationCertificate Table 3 ![![101, 0, 0], ![9, 1, 0]]
  ![-308, 35, 12] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![303, 0, 0], ![27, 3, 0]]
    hsu := by decide
    w := ![![-924, 105, 36], ![-3297, 375, 129]]
    hw := by decide
    g := ![![![10041, -3106, -85], ![2315, 0, 130]], ![![1079, -335, -9], ![250, 0, 14]]]
    h := ![![![39126, 357761, 119277], ![7069, -4015655, 0]], ![![139616, 1276560, 425603], ![25145, -14328620, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {3} * I101N1 =  Ideal.span {B.equivFun.symm ![-308, 35, 12]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E101RS1 


noncomputable def E107RS1 : RelationCertificate Table 9 ![![107, 0, 0], ![-32, 1, 0]]
  ![-70, 7, 3] ![![9, 0, 0], ![1, 1, 0]] where
    su := ![![963, 0, 0], ![-288, 9, 0]]
    hsu := by decide
    w := ![![-630, 63, 27], ![-819, 99, 27]]
    hw := by decide
    g := ![![![-73853207, -73857328, -227040560], ![-16412275, 681121602, 123]], ![![21614630, 21615839, 66448007], ![4803387, -199343998, -36]]]
    h := ![![![5165, -197664, 18534], ![-3385, -661045, 0]], ![![6748, -257495, 24144], ![-4344, -861135, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {9} * I107N1 =  Ideal.span {B.equivFun.symm ![-70, 7, 3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E107RS1 


noncomputable def E127RS1 : RelationCertificate Table 99 ![![127, 0, 0], ![-33, 1, 0]]
  ![-527, 32, 15] ![![99, 0, 0], ![19, 1, 0]] where
    su := ![![12573, 0, 0], ![-3267, 99, 0]]
    hsu := by decide
    w := ![![-52173, 3168, 1485], ![-13761, 891, 396]]
    hw := by decide
    g := ![![![-102623, -2106586, -332703], ![-40904, 10978108, 164]], ![![25023, 513807, 81148], ![10014, -2677618, -40]]]
    h := ![![![2276761, -86001770, 7819251], ![-1268660, -331014954, 0]], ![![600574, -22685404, 2062549], ![-334592, -87314573, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {99} * I127N1 =  Ideal.span {B.equivFun.symm ![-527, 32, 15]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 9 ![![131, 0, 0], ![-23, 1, 0]]
  ![377, -44, -15] ![![9, 0, 0], ![1, 1, 0]] where
    su := ![![1179, 0, 0], ![-207, 9, 0]]
    hsu := by decide
    w := ![![3393, -396, -135], ![4113, -477, -162]]
    hw := by decide
    g := ![![![7917365686, 7917375719, 24338593829], ![1759415717, -73015781290, -294]], ![![-1373419746, -1373421486, -4221998408], ![-305204575, 12665995190, 51]]]
    h := ![![![-231001, 5650896, -737157], ![83812, 32189184, 0]], ![![-280040, 6849958, -893574], ![101465, 39019392, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {9} * I131N1 =  Ideal.span {B.equivFun.symm ![377, -44, -15]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E131RS1 
