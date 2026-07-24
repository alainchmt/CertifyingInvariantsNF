import IdealArithmetic.Examples.NF3_1_703404_2.PrimesBelow3_1_703404_2F3
import IdealArithmetic.Examples.NF3_1_703404_2.ClassGroupData3_1_703404_2

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 2 ![![139, 0, 0], ![-8, 1, 0]]
  ![-8, 1, 0] ![![2, 0, 0], ![-44, -4, 1]] where
    su := ![![278, 0, 0], ![-16, 2, 0]]
    hsu := by decide
    w := ![![-16, 2, 0], ![614, 54, -12]]
    hw := by decide
    g := ![![![21, 6, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-104, 21, -1], ![-1806, 139, 0]], ![![4169, -521, 0], ![72398, -6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {2} * I139N1 =  Ideal.span {B.equivFun.symm ![-8, 1, 0]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E139RS1 


noncomputable def E167RS0 : RelationCertificate Table 2 ![![167, 0, 0], ![64, 1, 0]]
  ![-216, -77, -8] ![![2, 0, 0], ![-44, -4, 1]] where
    su := ![![334, 0, 0], ![128, 2, 0]]
    hsu := by decide
    w := ![![-432, -154, -16], ![-2286, -814, -84]]
    hw := by decide
    g := ![![![3, -30, 2], ![19, 0, 0]], ![![35, -8, 0], ![8, 0, 0]]]
    h := ![![![-13032, -265, -1], ![34002, 159, 0]], ![![-68913, -1319, -4], ![179802, 626, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N0 : Ideal.span {2} * I167N0 =  Ideal.span {B.equivFun.symm ![-216, -77, -8]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E167RS0 


noncomputable def E167RS1 : RelationCertificate Table 2 ![![167, 0, 0], ![-32, 1, 0]]
  ![24, 9, 1] ![![2, 0, 0], ![-44, -4, 1]] where
    su := ![![334, 0, 0], ![-64, 2, 0]]
    hsu := by decide
    w := ![![48, 18, 2], ![254, 100, 10]]
    hw := by decide
    g := ![![![0, 5, 0], ![-9, 0, 0]], ![![43, 3, -1], ![4, 0, 0]]]
    h := ![![![296, -9, 0], ![1544, 1, 0]], ![![1481, -45, 0], ![7725, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {2} * I167N1 =  Ideal.span {B.equivFun.symm ![24, 9, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E167RS1 


noncomputable def E179RS1 : RelationCertificate Table 14 ![![179, 0, 0], ![67, 1, 0]]
  ![-36, -3, 1] ![![14, 0, 0], ![-42, -4, 1]] where
    su := ![![2506, 0, 0], ![938, 14, 0]]
    hsu := by decide
    w := ![![-504, -42, 14], ![-322, 70, 0]]
    hw := by decide
    g := ![![![-15469650, -908885, -958049], ![46600255, 8296893, 0]], ![![-5821530, -342030, -360535], ![17536681, 3122298, 0]]]
    h := ![![![-12570, -255, -1], ![33582, 180, 0]], ![![-8109, -188, -1], ![21664, 179, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {14} * I179N1 =  Ideal.span {B.equivFun.symm ![-36, -3, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E179RS1 


noncomputable def E179RS2 : RelationCertificate Table 98 ![![179, 0, 0], ![74, 1, 0]]
  ![474, 134, -19] ![![98, 0, 0], ![38, 1, 0]] where
    su := ![![17542, 0, 0], ![7252, 98, 0]]
    hsu := by decide
    w := ![![46452, 13132, -1862], ![13034, 4312, -588]]
    hw := by decide
    g := ![![![8443508, -2454845161, -64607036], ![-21775387, 6331489496, 0]], ![![15923446986, -4629532694387, -121840835065], ![-41065731712, 11940401836355, 0]]]
    h := ![![![10318, 148, 0], ![-24952, -19, 0]], ![![2833, 41, 0], ![-6851, -6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N2 : Ideal.span {98} * I179N2 =  Ideal.span {B.equivFun.symm ![474, 134, -19]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E179RS2 


noncomputable def E193RS0 : RelationCertificate Table 14 ![![193, 0, 0], ![17, 1, 0]]
  ![-1276, -454, -47] ![![14, 0, 0], ![-4, 1, 0]] where
    su := ![![2702, 0, 0], ![238, 14, 0]]
    hsu := by decide
    w := ![![-17864, -6356, -658], ![-7210, -2562, -266]]
    hw := by decide
    g := ![![![522310, 27675525, -6951518], ![1827597, 97321227, 0]], ![![43301, 2294345, -576292], ![151519, 8068086, 0]]]
    h := ![![![-256788, -15256, -9], ![2915224, 1690, 0]], ![![-103647, -6164, -4], ![1176668, 753, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N0 : Ideal.span {14} * I193N0 =  Ideal.span {B.equivFun.symm ![-1276, -454, -47]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E193RS0 


noncomputable def E193RS1 : RelationCertificate Table 49 ![![193, 0, 0], ![-15, 1, 0]]
  ![-1025, -58, 17] ![![49, 0, 0], ![-11, 1, 0]] where
    su := ![![9457, 0, 0], ![-735, 49, 0]]
    hsu := by decide
    w := ![![-50225, -2842, 833], ![15729, 735, -245]]
    hw := by decide
    g := ![![![18, 6241, -569], ![165, 27846, 0]], ![![5, -473, 43], ![20, -2106, 0]]]
    h := ![![![-799910, 53628, -20], ![-10292107, 3877, 0]], ![![250542, -16793, 6], ![3223619, -1163, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {49} * I193N1 =  Ideal.span {B.equivFun.symm ![-1025, -58, 17]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E193RS1 


noncomputable def E193RS2 : RelationCertificate Table 2 ![![193, 0, 0], ![-2, 1, 0]]
  ![-2, 1, 0] ![![2, 0, 0], ![-44, -4, 1]] where
    su := ![![386, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-4, 2, 0], ![350, 30, -6]]
    hw := by decide
    g := ![![![35, 7, -1], ![3, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-6, 5, -1], ![-578, 193, 0]], ![![535, -265, -1], ![51540, 190, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N2 : Ideal.span {2} * I193N2 =  Ideal.span {B.equivFun.symm ![-2, 1, 0]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E193RS2 
