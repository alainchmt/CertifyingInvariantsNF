import IdealArithmetic.Examples.NF3_1_662796_4.PrimesBelow3_1_662796_4F1
import IdealArithmetic.Examples.NF3_1_662796_4.ClassGroupData3_1_662796_4

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 169 ![![37, 0, 0], ![-6, 1, 0]]
  ![139, 39, 3] ![![169, 0, 0], ![-26, -6, 1]] where
    su := ![![6253, 0, 0], ![-1014, 169, 0]]
    hsu := by decide
    w := ![![23491, 6591, 507], ![6760, 2028, 169]]
    hw := by decide
    g := ![![![77453281, 13696881, -890496], ![-12407322, -27150192, 0]], ![![-9739620, -1722359, 111978], ![1560291, 3414096, 0]]]
    h := ![![![147697, -25214, 100], ![910775, -3697, 0]], ![![42496, -7250, 28], ![262052, -1035, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {169} * I37N1 =  Ideal.span {B.equivFun.symm ![139, 39, 3]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E37RS1 


noncomputable def E47RS1 : RelationCertificate Table 169 ![![47, 0, 0], ![8, 1, 0]]
  ![-391, -123, -10] ![![169, 0, 0], ![-26, 46, 1]] where
    su := ![![7943, 0, 0], ![1352, 169, 0]]
    hsu := by decide
    w := ![![-66079, -20787, -1690], ![-277836, -86190, -6929]]
    hw := by decide
    g := ![![![-67, -11, 1], ![12, 0, 0]], ![![0, -1, 0], ![3, 0, 0]]]
    h := ![![![-393, -57, -1], ![2260, 37, 0]], ![![-1652, -222, -2], ![9500, 53, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {169} * I47N1 =  Ideal.span {B.equivFun.symm ![-391, -123, -10]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 13 ![![53, 0, 0], ![-18, 1, 0]]
  ![-325, -100, -8] ![![13, 0, 0], ![-6, 1, 0]] where
    su := ![![689, 0, 0], ![-234, 13, 0]]
    hsu := by decide
    w := ![![-4225, -1300, -104], ![-2002, -637, -52]]
    hw := by decide
    g := ![![![63, 1202, -201], ![72, 2605, 0]], ![![-20, -408, 68], ![-9, -880, 0]]]
    h := ![![![-503, 41, -1], ![-1463, 45, 0]], ![![-242, 29, -1], ![-704, 49, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {13} * I53N1 =  Ideal.span {B.equivFun.symm ![-325, -100, -8]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 169 ![![59, 0, 0], ![10, 1, 0]]
  ![-2807, -208, 35] ![![169, 0, 0], ![-52, 1, 0]] where
    su := ![![9971, 0, 0], ![1690, 169, 0]]
    hsu := by decide
    w := ![![-474383, -35152, 5915], ![163254, 11999, -2028]]
    hw := by decide
    g := ![![![7854695, 4722627212, -90822659], ![25527766, 15349029360, 0]], ![![1385720, 833160822, -16022836], ![4503593, 2707859280, 0]]]
    h := ![![![-2813, -296, -1], ![16316, 94, 0]], ![![954, 97, 0], ![-5532, -12, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {169} * I59N1 =  Ideal.span {B.equivFun.symm ![-2807, -208, 35]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 169 ![![61, 0, 0], ![12, 1, 0]]
  ![-119, -3, 1] ![![169, 0, 0], ![-26, 46, 1]] where
    su := ![![10309, 0, 0], ![2028, 169, 0]]
    hsu := by decide
    w := ![![-20111, -507, 169], ![24336, 0, -169]]
    hw := by decide
    g := ![![![21, -43, -1], ![155, 0, 0]], ![![24, -45, -1], ![164, 0, 0]]]
    h := ![![![-157403, -13873, -63], ![800122, 3844, 0]], ![![190416, 16768, 75], ![-967936, -4576, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {169} * I61N1 =  Ideal.span {B.equivFun.symm ![-119, -3, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E61RS1 


noncomputable def E67RS0 : RelationCertificate Table 13 ![![67, 0, 0], ![32, 1, 0]]
  ![-153, 0, 1] ![![13, 0, 0], ![0, 1, 0]] where
    su := ![![871, 0, 0], ![416, 13, 0]]
    hsu := by decide
    w := ![![-1989, 0, 13], ![494, -39, 0]]
    hw := by decide
    g := ![![![9, 2, 23], ![12, -296, 0]], ![![6, 1, 14], ![12, -180, 0]]]
    h := ![![![-30323, -1332, -12], ![63484, 805, 0]], ![![7458, 297, 2], ![-15614, -134, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {13} * I67N0 =  Ideal.span {B.equivFun.symm ![-153, 0, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 13 ![![67, 0, 0], ![-20, 1, 0]]
  ![429, 15, -4] ![![13, 0, 0], ![-6, 1, 0]] where
    su := ![![871, 0, 0], ![-260, 13, 0]]
    hsu := by decide
    w := ![![5577, 195, -52], ![-4550, -117, 39]]
    hw := by decide
    g := ![![![-33, -534, 87], ![-11, -1140, 0]], ![![12, 150, -25], ![19, 326, 0]]]
    h := ![![![119267, -6404, 22], ![399523, -1478, 0]], ![![-97290, 5245, -19], ![-325904, 1276, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {13} * I67N1 =  Ideal.span {B.equivFun.symm ![429, 15, -4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 169 ![![67, 0, 0], ![-12, 1, 0]]
  ![-31, -3, 0] ![![169, 0, 0], ![-26, 46, 1]] where
    su := ![![11323, 0, 0], ![-2028, 169, 0]]
    hsu := by decide
    w := ![![-5239, -507, 0], ![-676, -1690, -169]]
    hw := by decide
    g := ![![![25, -43, -1], ![160, 0, 0]], ![![0, -1, 0], ![3, 0, 0]]]
    h := ![![![-181, 27, -1], ![-1008, 67, 0]], ![![-4, 12, -1], ![-22, 66, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {169} * I67N2 =  Ideal.span {B.equivFun.symm ![-31, -3, 0]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E67RS2 


noncomputable def E73RS1 : RelationCertificate Table 13 ![![73, 0, 0], ![-7, 1, 0]]
  ![-7, 1, 0] ![![13, 0, 0], ![-78, -6, 1]] where
    su := ![![949, 0, 0], ![-91, 13, 0]]
    hsu := by decide
    w := ![![-91, 13, 0], ![1040, 78, -13]]
    hw := by decide
    g := ![![![1, 1, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-14, 9, -1], ![-145, 73, 0]], ![![190, -27, 0], ![1970, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {13} * I73N1 =  Ideal.span {B.equivFun.symm ![-7, 1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 169 ![![79, 0, 0], ![38, 1, 0]]
  ![-51, -39, -4] ![![169, 0, 0], ![-52, 1, 0]] where
    su := ![![13351, 0, 0], ![6422, 169, 0]]
    hsu := by decide
    w := ![![-8619, -6591, -676], ![676, 1521, 169]]
    hw := by decide
    g := ![![![-2441987, -1468273242, 28236927], ![-7936457, -4772040660, 0]], ![![-1204256, -724070445, 13924877], ![-3913832, -2353304212, 0]]]
    h := ![![![-161289, -5877, -43], ![335310, 3393, 0]], ![![12972, 455, 3], ![-26968, -236, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {169} * I79N1 =  Ideal.span {B.equivFun.symm ![-51, -39, -4]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E79RS1 
