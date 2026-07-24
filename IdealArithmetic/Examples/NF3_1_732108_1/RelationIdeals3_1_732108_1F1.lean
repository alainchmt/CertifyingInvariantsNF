import IdealArithmetic.Examples.NF3_1_732108_1.PrimesBelow3_1_732108_1F1
import IdealArithmetic.Examples.NF3_1_732108_1.ClassGroupData3_1_732108_1

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 3 ![![41, 0, 0], ![16, 1, 0]]
  ![64, 1, 2] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![123, 0, 0], ![48, 3, 0]]
    hsu := by decide
    w := ![![192, 3, 6], ![72, 0, 3]]
    hw := by decide
    g := ![![![-217, 195, 547], ![68, -328, 0]], ![![-79, 71, 200], ![25, -120, 0]]]
    h := ![![![5488, -52575, -14598], ![904, 119704, 0]], ![![2056, -19733, -5479], ![349, 44928, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {3} * I41N1 =  Ideal.span {B.equivFun.symm ![64, 1, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E41RS1 


noncomputable def E47RS1 : RelationCertificate Table 25 ![![47, 0, 0], ![-6, 1, 0]]
  ![-16, 14, 5] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![1175, 0, 0], ![-150, 25, 0]]
    hsu := by decide
    w := ![![-400, 350, 125], ![125, -125, 75]]
    hw := by decide
    g := ![![![-6413, 12921, 16074], ![18, -80366, 47]], ![![958, -1923, -2392], ![1, 11960, -7]]]
    h := ![![![-31366, -63477, 79275], ![2697, -745184, 0]], ![![9837, 19898, -24851], ![-811, 233600, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {25} * I47N1 =  Ideal.span {B.equivFun.symm ![-16, 14, 5]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 25 ![![53, 0, 0], ![-5, 1, 0]]
  ![37797027, 488517, 1158565] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![1325, 0, 0], ![-125, 25, 0]]
    hsu := by decide
    w := ![![944925675, 12212925, 28964125], ![117483925, 1518450, 3601150]]
    hw := by decide
    g := ![![![-1598964, 3198149, 3997852], ![22, -19989484, -68]], ![![141052, -282161, -352757], ![22, 1763774, 6]]]
    h := ![![![-38851681831, -58688815213, 97734291605], ![2557916906, -1035983259300, 0]], ![![-4830483702, -7296862121, 12151440572], ![318029389, -128805241254, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {25} * I53N1 =  Ideal.span {B.equivFun.symm ![37797027, 488517, 1158565]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 75 ![![59, 0, 0], ![9, 1, 0]]
  ![278, -312, 335] ![![75, 0, 0], ![5, 1, 1]] where
    su := ![![4425, 0, 0], ![675, 75, 0]]
    hsu := by decide
    w := ![![20850, -23400, 25125], ![-150, 2025, -10350]]
    hw := by decide
    g := ![![![-251546, 245742, -35175], ![-13908, 705630, -212]], ![![-39509, 39420, -5617], ![-2111, 113165, -34]]]
    h := ![![![1761, -9777, -4435], ![131, 52400, 0]], ![![-18, 89, 38], ![12, -476, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {75} * I59N1 =  Ideal.span {B.equivFun.symm ![278, -312, 335]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E59RS1 


noncomputable def E61RS0 : RelationCertificate Table 3 ![![61, 0, 0], ![0, 1, 0]]
  ![229, 3, 7] ![![3, 0, 0], ![23, 1, 1]] where
    su := ![![183, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![687, 9, 21], ![5568, 72, 171]]
    hw := by decide
    g := ![![![-10, -5, -2], ![2, 0, 0]], ![![7, 1, 0], ![-1, 0, 0]]]
    h := ![![![-1145, 1148, 2872], ![49, -35037, 0]], ![![-9280, 9308, 23277], ![172, -283968, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {3} * I61N0 =  Ideal.span {B.equivFun.symm ![229, 3, 7]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 3 ![![61, 0, 0], ![22, 1, 0]]
  ![106, -94, -9] ![![3, 0, 0], ![23, 1, 1]] where
    su := ![![183, 0, 0], ![66, 3, 0]]
    hsu := by decide
    w := ![![318, -282, -27], ![-1104, 1029, -180]]
    hw := by decide
    g := ![![![9109, -14645, -5918], ![63023, 0, 0]], ![![3448, -5548, -2242], ![23875, 0, 0]]]
    h := ![![![1174, -15120, -3149], ![242, 38416, 0]], ![![-4174, 52580, 10950], ![-589, -133602, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {3} * I61N1 =  Ideal.span {B.equivFun.symm ![106, -94, -9]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 3 ![![61, 0, 0], ![-23, 1, 0]]
  ![-172, 174, -103] ![![3, 0, 0], ![23, 1, 1]] where
    su := ![![183, 0, 0], ![-69, 3, 0]]
    hsu := by decide
    w := ![![-516, 522, -309], ![-750, 393, 1554]]
    hw := by decide
    g := ![![![108223, -173893, -70268], ![748331, 0, 0]], ![![-38858, 62406, 25217], ![-268559, 0, 0]]]
    h := ![![![-44009, -495857, 118027], ![8501, -1439950, 0]], ![![-63401, -714217, 170013], ![12213, -2074055, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {3} * I61N2 =  Ideal.span {B.equivFun.symm ![-172, 174, -103]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E61RS2 


noncomputable def E71RS1 : RelationCertificate Table 75 ![![71, 0, 0], ![4, 1, 0]]
  ![-33, 32, -10] ![![75, 0, 0], ![5, 1, 1]] where
    su := ![![5325, 0, 0], ![300, 75, 0]]
    hsu := by decide
    w := ![![-2475, 2400, -750], ![675, -675, 375]]
    hw := by decide
    g := ![![![1693781284, -1264534355, 194672529], ![98653959, -3646819168, 3993450]], ![![112918750, -84302291, 12978168], ![6576978, -243121278, 266230]]]
    h := ![![![385, -1164, -970], ![44, 13772, 0]], ![![-109, 317, 265], ![56, -3762, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {75} * I71N1 =  Ideal.span {B.equivFun.symm ![-33, 32, -10]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E71RS1 


noncomputable def E79RS0 : RelationCertificate Table 5 ![![79, 0, 0], ![-35, 1, 0]]
  ![8, -7, 0] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![395, 0, 0], ![-175, 5, 0]]
    hsu := by decide
    w := ![![40, -35, 0], ![30, -20, -35]]
    hw := by decide
    g := ![![![-266, 525, -6], ![3, 0, 79]], ![![126, -241, 3], ![8, 0, -36]]]
    h := ![![![710, 12343, -1870], ![-86, 29546, 0]], ![![520, 9062, -1373], ![-66, 21692, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {5} * I79N0 =  Ideal.span {B.equivFun.symm ![8, -7, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 5 ![![79, 0, 0], ![-27, 1, 0]]
  ![2, -3, 0] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![395, 0, 0], ![-135, 5, 0]]
    hsu := by decide
    w := ![![10, -15, 0], ![10, -10, -15]]
    hw := by decide
    g := ![![![-2697, 2656, -79], ![-545, 0, 386]], ![![852, -840, 25], ![175, 0, -122]]]
    h := ![![![-36, -776, 155], ![76, -2449, 0]], ![![-40, -766, 153], ![62, -2418, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {5} * I79N1 =  Ideal.span {B.equivFun.symm ![2, -3, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E79RS1 


noncomputable def E79RS2 : RelationCertificate Table 5 ![![79, 0, 0], ![-18, 1, 0]]
  ![-320857, -4147, -9835] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![395, 0, 0], ![-90, 5, 0]]
    hsu := by decide
    w := ![![-1604285, -20735, -49175], ![-997315, -12890, -30570]]
    hw := by decide
    g := ![![![-12489, 12528, -389], ![-2486, 0, 1817]], ![![2989, -3002, 96], ![601, 0, -437]]]
    h := ![![![-166582967, -1370456305, 428185935], ![20608108, -6765339740, 0]], ![![-103557465, -851953756, 266184784], ![12811186, -4205720810, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {5} * I79N2 =  Ideal.span {B.equivFun.symm ![-320857, -4147, -9835]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E79RS2 
