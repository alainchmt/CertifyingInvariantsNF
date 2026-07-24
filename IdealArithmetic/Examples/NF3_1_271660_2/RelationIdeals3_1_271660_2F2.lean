import IdealArithmetic.Examples.NF3_1_271660_2.PrimesBelow3_1_271660_2F2
import IdealArithmetic.Examples.NF3_1_271660_2.ClassGroupData3_1_271660_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 5 ![![83, 0, 0], ![-3, 1, 0]]
  ![-3, 1, 0] ![![5, 0, 0], ![-44, -7, 1]] where
    su := ![![415, 0, 0], ![-15, 5, 0]]
    hsu := by decide
    w := ![![-15, 5, 0], ![370, 45, -10]]
    hw := by decide
    g := ![![![41, 9, -1], ![6, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-3, 4, -1], ![-82, 83, 0]], ![![82, -24, -1], ![2244, 81, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {5} * I83N1 =  Ideal.span {B.equivFun.symm ![-3, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS1 


noncomputable def E97RS1 : RelationCertificate Table 5 ![![97, 0, 0], ![-20, 1, 0]]
  ![-923763913, -359868441, -37373511] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![485, 0, 0], ![-100, 5, 0]]
    hsu := by decide
    w := ![![-4618819565, -1799342205, -186867555], ![-7971131705, -3105294220, -322494930]]
    hw := by decide
    g := ![![![276980, 18148, -3910], ![-51765, 8, 0]], ![![-66335, -3883, 886], ![12493, 1, 0]]]
    h := ![![![-8137872369, 416060549, -1052948], ![-39422492794, 64762445, 0]], ![![-14044292413, 718034866, -1817172], ![-68035106886, 111766698, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {5} * I97N1 =  Ideal.span {B.equivFun.symm ![-923763913, -359868441, -37373511]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E97RS1 


noncomputable def E103RS1 : RelationCertificate Table 5 ![![103, 0, 0], ![8, 1, 0]]
  ![2433, 171, -44] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![515, 0, 0], ![40, 5, 0]]
    hsu := by decide
    w := ![![12165, 855, -220], ![-12905, -730, 215]]
    hw := by decide
    g := ![![![3784, -16443, 19226], ![-4041, -95201, 0]], ![![635, -3145, 3634], ![-755, -18011, 0]]]
    h := ![![![2431, 298, -1], ![-30995, 59, 0]], ![![-2587, -325, 0], ![32985, 43, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {5} * I103N1 =  Ideal.span {B.equivFun.symm ![2433, 171, -44]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS1 


noncomputable def E113RS1 : RelationCertificate Table 5 ![![113, 0, 0], ![26, 1, 0]]
  ![20577, -346, -186] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![565, 0, 0], ![130, 5, 0]]
    hsu := by decide
    w := ![![102885, -1730, -930], ![-64845, 8275, -160]]
    hw := by decide
    g := ![![![1546744, 803699, -96058], ![-148605, 799192, 0]], ![![487287, 242948, -19426], ![-48867, 197680, 0]]]
    h := ![![![1602725, 66668, 192], ![-6964898, -21882, 0]], ![![-1009461, -41997, -123], ![4386774, 13867, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {5} * I113N1 =  Ideal.span {B.equivFun.symm ![20577, -346, -186]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E113RS1 


noncomputable def E113RS2 : RelationCertificate Table 5 ![![113, 0, 0], ![-50, 1, 0]]
  ![2725725, 1061854, 110277] ![![5, 0, 0], ![-44, -7, 1]] where
    su := ![![565, 0, 0], ![-250, 5, 0]]
    hsu := by decide
    w := ![![13628625, 5309270, 551385], ![-50932130, -19841505, -2060605]]
    hw := by decide
    g := ![![![-1375, 4938, -283], ![5334, 0, 0]], ![![712, -2387, 138], ![-2536, 0, 0]]]
    h := ![![![87625625, -1949488, 5113], ![197979398, -467492, 0]], ![![-327469202, 7285659, -19111], ![-739876668, 1747422, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N2 : Ideal.span {5} * I113N2 =  Ideal.span {B.equivFun.symm ![2725725, 1061854, 110277]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E113RS2 
