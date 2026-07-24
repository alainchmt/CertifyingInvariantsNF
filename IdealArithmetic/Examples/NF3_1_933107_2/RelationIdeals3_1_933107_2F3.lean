import IdealArithmetic.Examples.NF3_1_933107_2.PrimesBelow3_1_933107_2F3
import IdealArithmetic.Examples.NF3_1_933107_2.ClassGroupData3_1_933107_2

set_option linter.all false

noncomputable section


noncomputable def E151RS1 : RelationCertificate Table 4 ![![151, 0, 0], ![23, 1, 0]]
  ![-141, 43, -5] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![604, 0, 0], ![92, 4, 0]]
    hsu := by decide
    w := ![![-564, 172, -20], ![808, -240, 28]]
    hw := by decide
    g := ![![![45147531, -451474830, -237024286], ![-90294942, 948097143, 0]], ![![6577935, -65779274, -34534119], ![-13155851, 138136476, 0]]]
    h := ![![![-899, -61, -1], ![5896, 146, 0]], ![![1254, 53, 0], ![-8224, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {4} * I151N1 =  Ideal.span {B.equivFun.symm ![-141, 43, -5]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E151RS1 


noncomputable def E163RS1 : RelationCertificate Table 2 ![![163, 0, 0], ![-55, 1, 0]]
  ![-7757, 2335, -271] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![326, 0, 0], ![-110, 2, 0]]
    hsu := by decide
    w := ![![-15514, 4670, -542], ![59078, -17784, 2064]]
    hw := by decide
    g := ![![![-984, -67, -39054], ![-33, 78120, 0]], ![![324, 18, 12692], ![11, -25389, 0]]]
    h := ![![![-835999, 16442, -24], ![-2477456, 3641, 0]], ![![3183893, -62487, 89], ![9435364, -13475, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {2} * I163N1 =  Ideal.span {B.equivFun.symm ![-7757, 2335, -271]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E163RS1 


noncomputable def E181RS0 : RelationCertificate Table 50 ![![181, 0, 0], ![47, 1, 0]]
  ![-413, 121, 23] ![![50, 0, 0], ![22, 1, 0]] where
    su := ![![9050, 0, 0], ![2350, 50, 0]]
    hsu := by decide
    w := ![![-20650, 6050, 1150], ![-14100, 3100, 650]]
    hw := by decide
    g := ![![![16643907, -2257529835, -102649385], ![-37827252, 5132469103, 0]], ![![4229931, -573736956, -26087693], ![-9613521, 1304384618, 0]]]
    h := ![![![-692580, -16057, -28], ![2667161, 5091, 0]], ![![-473008, -10960, -19], ![1821578, 3452, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N0 : Ideal.span {50} * I181N0 =  Ideal.span {B.equivFun.symm ![-413, 121, 23]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E181RS0 


noncomputable def E181RS1 : RelationCertificate Table 20 ![![181, 0, 0], ![-47, 1, 0]]
  ![-69, -17, -1] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![3620, 0, 0], ![-940, 20, 0]]
    hsu := by decide
    w := ![![-1380, -340, -20], ![80, -140, -20]]
    hw := by decide
    g := ![![![-40385, 8159980, 4090092], ![403977, -81801830, 0]], ![![10255, -2072491, -1038811], ![-102589, 20776217, 0]]]
    h := ![![![-76486, 1721, -2], ![-294551, 361, 0]], ![![4498, -96, 0], ![17322, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {20} * I181N1 =  Ideal.span {B.equivFun.symm ![-69, -17, -1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E181RS1 


noncomputable def E191RS1 : RelationCertificate Table 5 ![![191, 0, 0], ![-68, 1, 0]]
  ![-53, 16, -2] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![955, 0, 0], ![-340, 5, 0]]
    hsu := by decide
    w := ![![-265, 80, -10], ![330, -95, 10]]
    hw := by decide
    g := ![![![-17, -273, -143], ![-57, 721, 0]], ![![4, 95, 50], ![22, -252, 0]]]
    h := ![![![-1471, 89, -1], ![-4131, 189, 0]], ![![2014, -29, 0], ![5656, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {5} * I191N1 =  Ideal.span {B.equivFun.symm ![-53, 16, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E191RS1 
