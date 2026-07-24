import IdealArithmetic.Examples.NF3_1_136971_1.PrimesBelow3_1_136971_1F0
import IdealArithmetic.Examples.NF3_1_136971_1.ClassGroupData3_1_136971_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 4 ![![2, 0, 0], ![5, 1, 1]]
  ![-17, 1, 1] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![8, 0, 0], ![20, 4, 4]]
    hsu := by decide
    w := ![![-68, 4, 4], ![88, -24, 0]]
    hw := by decide
    g := ![![![14, 5, -1], ![-2, 7, 0]], ![![154, 41, 4], ![-26, 17, 0]]]
    h := ![![![-6, 1, 1], ![-1, 0, 0]], ![![1, -5, -2], ![4, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {4} * I2N0 =  Ideal.span {B.equivFun.symm ![-17, 1, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![2, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 98 ![![3, 0, 0], ![1, 1, 0]]
  ![47, -1, -3] ![![98, 0, 0], ![-33, 1, 0]] where
    su := ![![294, 0, 0], ![98, 98, 0]]
    hsu := by decide
    w := ![![4606, -98, -294], ![-1764, 98, 98]]
    hw := by decide
    g := ![![![25, -1485, 45], ![73, -4408, 0]], ![![5, -791, 24], ![13, -2349, 0]]]
    h := ![![![24, 9, 0], ![-25, -3, 0]], ![![-10, -5, -1], ![12, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {98} * I3N0 =  Ideal.span {B.equivFun.symm ![47, -1, -3]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E3RS0 


noncomputable def E7RS0 : RelationCertificate Table 49 ![![7, 0, 0], ![3, -2, 1]]
  ![-474, -90, -25] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![343, 0, 0], ![147, -98, 49]]
    hsu := by decide
    w := ![![-23226, -4410, -1225], ![-9359, -1764, -490]]
    hw := by decide
    g := ![![![9698, -1611138, -100734], ![-29699, 4935966, 0]], ![![4117, -685008, -42829], ![-12611, 2098625, 0]]]
    h := ![![![-60, -18, -1], ![-18, 0, 0]], ![![-26, -6, -1], ![-3, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {49} * I7N0 =  Ideal.span {B.equivFun.symm ![-474, -90, -25]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![7, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![5, 2, 0], ![-14, 0, 0]], ![![-2, -1, 0], ![8, 0, 0]]]
    h := ![![![5, 2, 0], ![-14, 0, 0]], ![![-2, -1, 0], ![8, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 14 ![![13, 0, 0], ![1, 1, 0]]
  ![17, 5, 1] ![![14, 0, 0], ![-5, 1, 0]] where
    su := ![![182, 0, 0], ![14, 14, 0]]
    hsu := by decide
    w := ![![238, 70, 14], ![-14, -14, 0]]
    hw := by decide
    g := ![![![1, 5, -1], ![4, 15, 0]], ![![5, -1, 0], ![13, 0, 0]]]
    h := ![![![2, 1, 0], ![-9, 1, 0]], ![![0, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {14} * I13N0 =  Ideal.span {B.equivFun.symm ![17, 5, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 49 ![![13, 0, 0], ![2, 1, 0]]
  ![-389, -72, -20] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![637, 0, 0], ![98, 49, 0]]
    hsu := by decide
    w := ![![-19061, -3528, -980], ![-7644, -1421, -392]]
    hw := by decide
    g := ![![![1511, -252371, -15779], ![-4629, 773175, 0]], ![![226, -38050, -2379], ![-691, 116571, 0]]]
    h := ![![![-31879, -16365, -219], ![207019, 2827, 0]], ![![-12784, -6563, -88], ![83018, 1136, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {49} * I13N1 =  Ideal.span {B.equivFun.symm ![-389, -72, -20]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 4 ![![13, 0, 0], ![-3, 1, 0]]
  ![57, 11, 3] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![52, 0, 0], ![-12, 4, 0]]
    hsu := by decide
    w := ![![228, 44, 12], ![156, 28, 8]]
    hw := by decide
    g := ![![![-15508, -263547, 279050], ![-62008, -1116199, 0]], ![![4770, 81038, -85806], ![19069, 343224, 0]]]
    h := ![![![717, -245, 3], ![3088, -36, 0]], ![![495, -169, 2], ![2132, -24, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {4} * I13N2 =  Ideal.span {B.equivFun.symm ![57, 11, 3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E13RS2 


noncomputable def E17RS0 : RelationCertificate Table 98 ![![17, 0, 0], ![6, 1, 0]]
  ![-51, -1, -3] ![![98, 0, 0], ![-33, 1, 0]] where
    su := ![![1666, 0, 0], ![588, 98, 0]]
    hsu := by decide
    w := ![![-4998, -98, -294], ![1470, 0, 98]]
    hw := by decide
    g := ![![![-263760, -85474943, 2590392], ![-783287, -253858415, 0]], ![![-99727, -32321072, 979518], ![-296159, -95992764, 0]]]
    h := ![![![-57, -14, -1], ![153, 14, 0]], ![![9, 1, 0], ![-23, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {98} * I17N0 =  Ideal.span {B.equivFun.symm ![-51, -1, -3]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E17RS0 


noncomputable def E17RS2 : RelationCertificate Table 28 ![![17, 0, 0], ![-2, 1, 0]]
  ![3, 5, 1] ![![28, 0, 0], ![-5, 1, 0]] where
    su := ![![476, 0, 0], ![-56, 28, 0]]
    hsu := by decide
    w := ![![84, 140, 28], ![56, -28, 0]]
    hw := by decide
    g := ![![![6, 679, -136], ![35, 3809, 0]], ![![0, -65, 13], ![-1, -364, 0]]]
    h := ![![![183, -91, 0], ![1554, 1, 0]], ![![126, -63, 0], ![1070, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {28} * I17N2 =  Ideal.span {B.equivFun.symm ![3, 5, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E17RS2 


noncomputable def E19RS0 : RelationCertificate Table 28 ![![19, 0, 0], ![6, 1, 0]]
  ![-25, 5, 1] ![![28, 0, 0], ![-5, 1, 0]] where
    su := ![![532, 0, 0], ![168, 28, 0]]
    hsu := by decide
    w := ![![-700, 140, 28], ![196, -56, 0]]
    hw := by decide
    g := ![![![9, 904, -181], ![45, 5070, 0]], ![![7, 289, -58], ![36, 1625, 0]]]
    h := ![![![-2149, -424, -11], ![6801, 210, 0]], ![![595, 111, 2], ![-1883, -38, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {28} * I19N0 =  Ideal.span {B.equivFun.symm ![-25, 5, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 28 ![![19, 0, 0], ![7, 1, 0]]
  ![9, -13, 3] ![![28, 0, 0], ![-5, 1, 0]] where
    su := ![![532, 0, 0], ![196, 28, 0]]
    hsu := by decide
    w := ![![252, -364, 84], ![168, 56, -28]]
    hw := by decide
    g := ![![![21747946, 3518816604, -704633238], ![121788470, 19729730671, 0]], ![![7630894, 1234678128, -247240861], ![42732991, 6922744112, 0]]]
    h := ![![![993, 168, 4], ![-2694, -73, 0]], ![![732, 119, 2], ![-1986, -39, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {28} * I19N1 =  Ideal.span {B.equivFun.symm ![9, -13, 3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 14 ![![23, 0, 0], ![-10, 1, 0]]
  ![215, 41, 11] ![![14, 0, 0], ![-5, 1, 0]] where
    su := ![![322, 0, 0], ![-140, 14, 0]]
    hsu := by decide
    w := ![![3010, 574, 154], ![-294, -56, -14]]
    hw := by decide
    g := ![![![11566, 511162, -102695], ![32381, 1437733, 0]], ![![-5001, -221130, 44426], ![-14003, -621966, 0]]]
    h := ![![![995, -102, 1], ![2267, -12, 0]], ![![-77, 17, -1], ![-175, 22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {14} * I23N1 =  Ideal.span {B.equivFun.symm ![215, 41, 11]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 2 ![![29, 0, 0], ![3, 1, 0]]
  ![5, -5, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![58, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![10, -10, 2], ![76, -6, -4]]
    hw := by decide
    g := ![![![532, -2158, -2581], ![-811, 5175, 0]], ![![71, -240, -286], ![-84, 575, 0]]]
    h := ![![![1, 0, 0], ![-8, 1, 0]], ![![34, 8, -1], ![-316, 27, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {2} * I29N0 =  Ideal.span {B.equivFun.symm ![5, -5, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 7 ![![29, 0, 0], ![10, 1, 0]]
  ![-4, -2, 1] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![203, 0, 0], ![70, 7, 0]]
    hsu := by decide
    w := ![![-28, -14, 7], ![63, -14, 0]]
    hw := by decide
    g := ![![![-1168, 31038, 15812], ![4107, -110682, 0]], ![![-480, 12733, 6487], ![1689, -45408, 0]]]
    h := ![![![4, -10, -1], ![-12, 30, 0]], ![![-9, -1, 0], ![27, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {7} * I29N1 =  Ideal.span {B.equivFun.symm ![-4, -2, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 196 ![![29, 0, 0], ![-13, 1, 0]]
  ![125, 87, -33] ![![196, 0, 0], ![-33, 1, 0]] where
    su := ![![5684, 0, 0], ![-2548, 196, 0]]
    hsu := by decide
    w := ![![24500, 17052, -6468], ![-6468, -2548, 1176]]
    hw := by decide
    g := ![![![-49247, -58966685, 1786915], ![-292552, -350235247, 0]], ![![22252, 26618176, -806632], ![132181, 158099842, 0]]]
    h := ![![![774, -58, -1], ![1717, -4, 0]], ![![-180, 16, 0], ![-399, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {196} * I29N2 =  Ideal.span {B.equivFun.symm ![125, 87, -33]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS2 
