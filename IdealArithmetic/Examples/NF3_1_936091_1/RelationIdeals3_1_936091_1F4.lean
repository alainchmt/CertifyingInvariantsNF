import IdealArithmetic.Examples.NF3_1_936091_1.PrimesBelow3_1_936091_1F4
import IdealArithmetic.Examples.NF3_1_936091_1.ClassGroupData3_1_936091_1

set_option linter.all false

noncomputable section


noncomputable def E197RS0 : RelationCertificate Table 2 ![![197, 0, 0], ![52, 1, 0]]
  ![-142071, 34657, -4685] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![394, 0, 0], ![104, 2, 0]]
    hsu := by decide
    w := ![![-284142, 69314, -9370], ![908890, -221716, 29972]]
    hw := by decide
    g := ![![![-2074, -444, -130678], ![-221, 261284, 0]], ![![-512, -128, -35034], ![-64, 70043, 0]]]
    h := ![![![-2212051, -45793, -90], ![8377538, 13045, 0]], ![![7075577, 146274, 284], ![-26796812, -40962, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N0 : Ideal.span {2} * I197N0 =  Ideal.span {B.equivFun.symm ![-142071, 34657, -4685]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E197RS0 


noncomputable def E197RS1 : RelationCertificate Table 36 ![![197, 0, 0], ![63, 1, 0]]
  ![2731553, -666339, 90077] ![![36, 0, 0], ![2, 1, 0]] where
    su := ![![7092, 0, 0], ![2268, 36, 0]]
    hsu := by decide
    w := ![![98335908, -23988204, 3242772], ![-12011832, 2930184, -396108]]
    hw := by decide
    g := ![![![-642373, 417618242, 208969693], ![11564832, -7522908269, 0]], ![![-202187, 131433156, 65767113], ![3639709, -2367615822, 0]]]
    h := ![![![3041470774, 57365352, 144769], ![-9510587475, -28429416, 0]], ![![-371518798, -7007257, -17684], ![1161728088, 3472745, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {36} * I197N1 =  Ideal.span {B.equivFun.symm ![2731553, -666339, 90077]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E197RS1 


noncomputable def E197RS2 : RelationCertificate Table 3 ![![197, 0, 0], ![81, 1, 0]]
  ![-4427, 1080, -146] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![591, 0, 0], ![243, 3, 0]]
    hsu := by decide
    w := ![![-13281, 3240, -438], ![32751, -7989, 1080]]
    hw := by decide
    g := ![![![365, 256, -190], ![-36, 568, 0]], ![![151, 107, -78], ![-14, 234, 0]]]
    h := ![![![-111115, -1711, -5], ![270188, 839, 0]], ![![273717, 4027, 10], ![-665572, -1610, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N2 : Ideal.span {3} * I197N2 =  Ideal.span {B.equivFun.symm ![-4427, 1080, -146]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E197RS2 


noncomputable def E211RS1 : RelationCertificate Table 2 ![![211, 0, 0], ![69, 1, 0]]
  ![-31, 7, -1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![422, 0, 0], ![138, 2, 0]]
    hsu := by decide
    w := ![![-62, 14, -2], ![194, -48, 6]]
    hw := by decide
    g := ![![![-60, 0, -16437], ![1, 32877, 0]], ![![-21, 0, -5479], ![0, 10959, 0]]]
    h := ![![![-577, -77, -1], ![1764, 210, 0]], ![![1387, 19, 0], ![-4240, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {2} * I211N1 =  Ideal.span {B.equivFun.symm ![-31, 7, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E211RS1 


noncomputable def E239RS0 : RelationCertificate Table 12 ![![239, 0, 0], ![-107, 1, 0]]
  ![-1489, 363, -49] ![![12, 0, 0], ![2, 1, 0]] where
    su := ![![2868, 0, 0], ![-1284, 12, 0]]
    hsu := by decide
    w := ![![-17868, 4356, -588], ![6528, -1596, 216]]
    hw := by decide
    g := ![![![-7, -376, -185], ![-23, 2203, 0]], ![![3, 166, 82], ![18, -977, 0]]]
    h := ![![![-2258928, 24087, -28], ![-5045629, 6643, 0]], ![![825454, -8777, 10], ![1843766, -2372, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N0 : Ideal.span {12} * I239N0 =  Ideal.span {B.equivFun.symm ![-1489, 363, -49]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E239RS0 


noncomputable def E239RS1 : RelationCertificate Table 12 ![![239, 0, 0], ![-89, 1, 0]]
  ![231953, -56583, 7649] ![![12, 0, 0], ![2, 1, 0]] where
    su := ![![2868, 0, 0], ![-1068, 12, 0]]
    hsu := by decide
    w := ![![2783436, -678996, 91788], ![-1020000, 248820, -33636]]
    hw := by decide
    g := ![![![-167027, 12293365, 6188256], ![996621, -74258938, 0]], ![![61371, -4517445, -2273998], ![-366217, 27287923, 0]]]
    h := ![![![11347369, -138760, 156], ![30469542, -29635, 0]], ![![-4158172, 50922, -58], ![-11165372, 11059, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {12} * I239N1 =  Ideal.span {B.equivFun.symm ![231953, -56583, 7649]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E239RS1 


noncomputable def E239RS2 : RelationCertificate Table 12 ![![239, 0, 0], ![-44, 1, 0]]
  ![221, -87, -19] ![![12, 0, 0], ![2, 1, 0]] where
    su := ![![2868, 0, 0], ![-528, 12, 0]]
    hsu := by decide
    w := ![![2652, -1044, -228], ![4128, -276, -144]]
    hw := by decide
    g := ![![![-19127, 1304931, 656626], ![105557, -7880119, 0]], ![![2778, -182377, -91752], ![-14727, 1101152, 0]]]
    h := ![![![121755, -2815, 1], ![661346, -258, 0]], ![![189408, -4395, 2], ![1028822, -490, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N2 : Ideal.span {12} * I239N2 =  Ideal.span {B.equivFun.symm ![221, -87, -19]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E239RS2 


noncomputable def E251RS1 : RelationCertificate Table 6 ![![251, 0, 0], ![76, 1, 0]]
  ![4883, -1191, 161] ![![6, 0, 0], ![2, 1, 0]] where
    su := ![![1506, 0, 0], ![456, 6, 0]]
    hsu := by decide
    w := ![![29298, -7146, 966], ![-21468, 5238, -708]]
    hw := by decide
    g := ![![![-24293, 490584, 251416], ![73669, -1508511, 0]], ![![36608398, -732166512, -375235340], ![-109824949, 2251412036, 0]]]
    h := ![![![122189, 1706, 2], ![-403481, -341, 0]], ![![-89710, -1369, -3], ![296232, 635, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N1 : Ideal.span {6} * I251N1 =  Ideal.span {B.equivFun.symm ![4883, -1191, 161]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E251RS1 


noncomputable def E257RS1 : RelationCertificate Table 36 ![![257, 0, 0], ![-94, 1, 0]]
  ![11473, -9255, -1727] ![![36, 0, 0], ![2, 1, 0]] where
    su := ![![9252, 0, 0], ![-3384, 36, 0]]
    hsu := by decide
    w := ![![413028, -333180, -62172], ![357984, -36396, -14436]]
    hw := by decide
    g := ![![![-1650971, 407018, -54113], ![-80395, -17190, 0]], ![![595904, 31722330, 15974068], ![914312, -574298717, 0]]]
    h := ![![![42709539, -502870, 509], ![116769575, -132540, 0]], ![![36958432, -435155, 445], ![101045820, -114766, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R257N1 : Ideal.span {36} * I257N1 =  Ideal.span {B.equivFun.symm ![11473, -9255, -1727]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E257RS1 
