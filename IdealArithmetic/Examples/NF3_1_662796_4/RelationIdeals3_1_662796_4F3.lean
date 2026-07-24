import IdealArithmetic.Examples.NF3_1_662796_4.PrimesBelow3_1_662796_4F3
import IdealArithmetic.Examples.NF3_1_662796_4.ClassGroupData3_1_662796_4

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 13 ![![139, 0, 0], ![-11, 1, 0]]
  ![403, 42, -6] ![![13, 0, 0], ![-6, 1, 0]] where
    su := ![![1807, 0, 0], ![-143, 13, 0]]
    hsu := by decide
    w := ![![5239, 546, -78], ![-5382, -533, 78]]
    hw := by decide
    g := ![![![-377885, -12911571, 2162427], ![-818781, -28111545, 0]], ![![28735, 981581, -164395], ![62258, 2137135, 0]]]
    h := ![![![1365, -124, 0], ![17212, -6, 0]], ![![-1376, 136, -1], ![-17350, 145, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {13} * I139N1 =  Ideal.span {B.equivFun.symm ![403, 42, -6]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 169 ![![149, 0, 0], ![-8, 1, 0]]
  ![-9211, -572, 106] ![![169, 0, 0], ![-52, 1, 0]] where
    su := ![![25181, 0, 0], ![-1352, 169, 0]]
    hsu := by decide
    w := ![![-1556659, -96668, 17914], ![531336, 32617, -6084]]
    hw := by decide
    g := ![![![36002341, 21646369499, -416289650], ![117007505, 70352950984, 0]], ![![-1622372, -975474551, 18759726], ![-5272712, -3170393690, 0]]]
    h := ![![![-29599, 3702, -1], ![-550130, 255, 0]], ![![10120, -1263, 0], ![188092, -36, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {169} * I149N1 =  Ideal.span {B.equivFun.symm ![-9211, -572, 106]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E149RS1 


noncomputable def E163RS1 : RelationCertificate Table 169 ![![163, 0, 0], ![63, 1, 0]]
  ![1209, 381, 31] ![![169, 0, 0], ![-52, -6, 1]] where
    su := ![![27547, 0, 0], ![10647, 169, 0]]
    hsu := by decide
    w := ![![204321, 64389, 5239], ![33462, 10478, 845]]
    hw := by decide
    g := ![![![18637, 2357, -214], ![-5774, -6966, 0]], ![![7401, 936, -85], ![-2280, -2766, 0]]]
    h := ![![![16743, 256, 0], ![-43300, 31, 0]], ![![2682, 41, 0], ![-6936, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {169} * I163N1 =  Ideal.span {B.equivFun.symm ![1209, 381, 31]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E163RS1 


noncomputable def E181RS1 : RelationCertificate Table 13 ![![181, 0, 0], ![-26, 1, 0]]
  ![-1633, -104, 19] ![![13, 0, 0], ![0, 1, 0]] where
    su := ![![2353, 0, 0], ![-338, 13, 0]]
    hsu := by decide
    w := ![![-21229, -1352, 247], ![9386, 533, -104]]
    hw := by decide
    g := ![![![-161, -51, -2865677], ![9, 37253748, 0]], ![![12, 3, 390560], ![10, -5077276, 0]]]
    h := ![![![-2059, 81, 0], ![-14271, 19, 0]], ![![942, -11, -1], ![6530, 173, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {13} * I181N1 =  Ideal.span {B.equivFun.symm ![-1633, -104, 19]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E181RS1 


noncomputable def E191RS1 : RelationCertificate Table 169 ![![191, 0, 0], ![-35, 1, 0]]
  ![-85, -13, 2] ![![169, 0, 0], ![-26, -6, 1]] where
    su := ![![32279, 0, 0], ![-5915, 169, 0]]
    hsu := by decide
    w := ![![-14365, -2197, 338], ![-10140, -1014, 169]]
    hw := by decide
    g := ![![![1177934665, 208306609, -13542946], ![-188696327, -412909032, 0]], ![![-202307873, -35776234, 2325973], ![32408287, 70916287, 0]]]
    h := ![![![-557540, 16420, -14], ![-3042573, 2676, 0]], ![![-393570, 11595, -10], ![-2147766, 1911, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {169} * I191N1 =  Ideal.span {B.equivFun.symm ![-85, -13, 2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E191RS1 


noncomputable def E193RS1 : RelationCertificate Table 169 ![![193, 0, 0], ![-55, 1, 0]]
  ![1625, 518, 43] ![![169, 0, 0], ![-71, 1, 0]] where
    su := ![![32617, 0, 0], ![-9295, 169, 0]]
    hsu := by decide
    w := ![![274625, 87542, 7267], ![-94133, -30251, -2535]]
    hw := by decide
    g := ![![![116861196, 55306602079, -778989409], ![278162481, 131649210048, 0]], ![![-32548692, -15404242224, 216967615], ![-77475029, -36667526912, 0]]]
    h := ![![![15376795, -300188, 375], ![53958542, -72332, 0]], ![![-5270609, 102919, -129], ![-18495036, 24882, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {169} * I193N1 =  Ideal.span {B.equivFun.symm ![1625, 518, 43]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E193RS1 
