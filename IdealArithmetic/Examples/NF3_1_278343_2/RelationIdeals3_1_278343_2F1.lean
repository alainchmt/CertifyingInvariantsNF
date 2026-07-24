import IdealArithmetic.Examples.NF3_1_278343_2.PrimesBelow3_1_278343_2F1
import IdealArithmetic.Examples.NF3_1_278343_2.ClassGroupData3_1_278343_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 2 ![![37, 0, 0], ![14, 1, 0]]
  ![1761, 71, 100] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![74, 0, 0], ![28, 2, 0]]
    hsu := by decide
    w := ![![3522, 142, 200], ![8242, 332, 468]]
    hw := by decide
    g := ![![![380999, -56446, -4697], ![-28223, 0, -9408]], ![![154797, -22934, -1908], ![-11467, 0, -3822]]]
    h := ![![![-575, -5671, -3028], ![-357, 14017, 0]], ![![-1345, -13271, -7086], ![-837, 32802, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {2} * I37N1 =  Ideal.span {B.equivFun.symm ![1761, 71, 100]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 4 ![![41, 0, 0], ![-11, 1, 0]]
  ![-3596, 1625, -2107] ![![4, 0, 0], ![9, 1, 1]] where
    su := ![![164, 0, 0], ![-44, 4, 0]]
    hsu := by decide
    w := ![![-14384, 6500, -8428], ![-17588, -5400, 22528]]
    hw := by decide
    g := ![![![66258600, -19755832, -13448282], ![140780841, 0, 0]], ![![-10214089, 3045455, 2073116], ![-21702036, 0, 0]]]
    h := ![![![-678393, 3751808, -3006803], ![273517, 15409602, 0]], ![![-805700, 4455815, -3570880], ![324875, 18301464, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {4} * I41N1 =  Ideal.span {B.equivFun.symm ![-3596, 1625, -2107]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 2 ![![43, 0, 0], ![11, 1, 0]]
  ![124, 5, 7] ![![2, 0, 0], ![11, 1, 1]] where
    su := ![![86, 0, 0], ![22, 2, 0]]
    hsu := by decide
    w := ![![248, 10, 14], ![2178, 88, 124]]
    hw := by decide
    g := ![![![-8, -6, -4], ![5, 0, 0]], ![![-9, -1, -2], ![2, 0, 0]]]
    h := ![![![228, 1505, 1005], ![102, -5401, 0]], ![![2013, 13218, 8826], ![854, -47432, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {2} * I43N1 =  Ideal.span {B.equivFun.symm ![124, 5, 7]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E43RS1 


noncomputable def E59RS0 : RelationCertificate Table 4 ![![59, 0, 0], ![17, 1, 0]]
  ![1273429, 51332, 72303] ![![4, 0, 0], ![12, 0, 1]] where
    su := ![![236, 0, 0], ![68, 4, 0]]
    hsu := by decide
    w := ![![5093716, 205328, 289212], ![17703768, 713640, 1005188]]
    hw := by decide
    g := ![![![91371, -31636, -74546], ![255481, -42390, 0]], ![![230726179904, -80230917804, -188036022795], ![645169534031, -106974557149, 0]]]
    h := ![![![3998154, 40527687, 18026997], ![1838969, -132940065, 0]], ![![13896054, 140858418, 62654803], ![6391428, -462047760, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {4} * I59N0 =  Ideal.span {B.equivFun.symm ![1273429, 51332, 72303]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 2 ![![59, 0, 0], ![-13, 1, 0]]
  ![534, 179, -721] ![![2, 0, 0], ![11, 1, 1]] where
    su := ![![118, 0, 0], ![-26, 2, 0]]
    hsu := by decide
    w := ![![1068, 358, -1442], ![-20366, 2160, 5392]]
    hw := by decide
    g := ![![![2974285, -3604897, -2343633], ![13384341, 0, 0]], ![![-419450, 508372, 330505], ![-1887496, 0, 0]]]
    h := ![![![-276, 1883, -1267], ![130, 9254, 0]], ![![5709, -37670, 25192], ![-1838, -185454, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {2} * I59N1 =  Ideal.span {B.equivFun.symm ![534, 179, -721]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 4 ![![59, 0, 0], ![-4, 1, 0]]
  ![67905, -13883, -1544] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![236, 0, 0], ![-16, 4, 0]]
    hsu := by decide
    w := ![![271620, -55532, -6176], ![-17020, 49416, -112608]]
    hw := by decide
    g := ![![![1454158507, -102603427, 102477245], ![701428397, 0, -188]], ![![16751024, -1181869, 1180489], ![8080049, 0, 12]]]
    h := ![![![21437039, -32323658, 86286216], ![-2001169, -636361036, 0]], ![![-1425277, 2149294, -5737384], ![133072, 42309688, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {4} * I59N2 =  Ideal.span {B.equivFun.symm ![67905, -13883, -1544]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E59RS2 


noncomputable def E61RS0 : RelationCertificate Table 4 ![![61, 0, 0], ![12, 1, 0]]
  ![-2271, 380, 259] ![![4, 0, 0], ![12, 0, 1]] where
    su := ![![244, 0, 0], ![48, 4, 0]]
    hsu := by decide
    w := ![![-9084, 1520, 1036], ![-2688, 1968, -3428]]
    hw := by decide
    g := ![![![284813, 113272, -50886], ![841735, 0, 0]], ![![77879, 30972, -13916], ![230168, -1, 0]]]
    h := ![![![-31583, -217307, -133825], ![-9717, 1020448, 0]], ![![-9444, -64943, -40013], ![-2881, 304992, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {4} * I61N0 =  Ideal.span {B.equivFun.symm ![-2271, 380, 259]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 4 ![![61, 0, 0], ![-24, 1, 0]]
  ![-21434549, -864028, -1217015] ![![4, 0, 0], ![12, 0, 1]] where
    su := ![![244, 0, 0], ![-96, 4, 0]]
    hsu := by decide
    w := ![![-85738196, -3456112, -4868060], ![-297992496, -12012096, -16919476]]
    hw := by decide
    g := ![![![246, -257, -628], ![619, 0, 0]], ![![-208, 259, 294], ![-520, 15, 0]]]
    h := ![![![-4086029721, 58560664215, -20383592355], ![2567629197, 155424739580, 0]], ![![-14201444124, 203534005976, -70845409009], ![8924076520, 540195714960, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {4} * I61N1 =  Ideal.span {B.equivFun.symm ![-21434549, -864028, -1217015]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 2 ![![67, 0, 0], ![-6, 1, 0]]
  ![-36467, 7191, 1480] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![134, 0, 0], ![-12, 2, 0]]
    hsu := by decide
    w := ![![-72934, 14382, 2960], ![134262, -51476, 56048]]
    hw := by decide
    g := ![![![2109666949, 68106771, 119811485], ![34053387, 0, 10146]], ![![-41560956, -1344162, -2361251], ![-672079, 0, -534]]]
    h := ![![![59723, -152141, 243800], ![-7562, -2041640, 0]], ![![-111775, 284544, -455808], ![14289, 3820895, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {2} * I67N1 =  Ideal.span {B.equivFun.symm ![-36467, 7191, 1480]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS1 


noncomputable def E73RS1 : RelationCertificate Table 4 ![![73, 0, 0], ![-27, 1, 0]]
  ![177, 7, 10] ![![4, 0, 0], ![-9, 1, -1]] where
    su := ![![292, 0, 0], ![-108, 4, 0]]
    hsu := by decide
    w := ![![708, 28, 40], ![-1096, -44, -64]]
    hw := by decide
    g := ![![![-23576, 24969, 7095], ![57539, 0, 5830]], ![![4717, -4994, -1418], ![-11506, 0, -1166]]]
    h := ![![![29143, -460363, 141722], ![-17006, -1293212, 0]], ![![-45072, 712635, -219384], ![26436, 2001877, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {4} * I73N1 =  Ideal.span {B.equivFun.symm ![177, 7, 10]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E73RS1 


noncomputable def E73RS2 : RelationCertificate Table 4 ![![73, 0, 0], ![-12, 1, 0]]
  ![-55, -2, -3] ![![4, 0, 0], ![11, -1, 1]] where
    su := ![![292, 0, 0], ![-48, 4, 0]]
    hsu := by decide
    w := ![![-220, -8, -12], ![-448, -16, -28]]
    hw := by decide
    g := ![![![-5, 0, 1], ![1, 0, 0]], ![![-21, -2, 26], ![-42, 7, 0]]]
    h := ![![![2369, -13486, 9813], ![-508, -89544, 0]], ![![4808, -27464, 19985], ![-1136, -182364, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N2 : Ideal.span {4} * I73N2 =  Ideal.span {B.equivFun.symm ![-55, -2, -3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E73RS2 
