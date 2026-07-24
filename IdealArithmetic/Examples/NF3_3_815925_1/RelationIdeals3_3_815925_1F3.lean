import IdealArithmetic.Examples.NF3_3_815925_1.PrimesBelow3_3_815925_1F3
import IdealArithmetic.Examples.NF3_3_815925_1.ClassGroupData3_3_815925_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 2 ![![139, 0, 0], ![63, 1, 0]]
  ![-72091, -823, 1975] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![278, 0, 0], ![126, 2, 0]]
    hsu := by decide
    w := ![![-144182, -1646, 3950], ![-25346, -168, 658]]
    hw := by decide
    g := ![![![-56595, 220300, 104867], ![110151, 0, 0]], ![![-30742, 119665, 56963], ![59834, 0, 0]]]
    h := ![![![11779997, 489644461, 31594093], ![8861854, -1097894238, 0]], ![![2070925, 86081876, 5554395], ![1558080, -193015144, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {2} * I139N1 =  Ideal.span {B.equivFun.symm ![-72091, -823, 1975]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS1 


noncomputable def E167RS0 : RelationCertificate Table 2 ![![167, 0, 0], ![-63, 1, 0]]
  ![-29, 63, -18] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![334, 0, 0], ![-126, 2, 0]]
    hsu := by decide
    w := ![![-58, 126, -36], ![342, -740, 216]]
    hw := by decide
    g := ![![![-5254, -47, 144], ![-23, 0, 0]], ![![1971, 17, -54], ![10, 0, 0]]]
    h := ![![![-4278, 170446, -10654], ![2781, 444800, 0]], ![![25556, -1004891, 62812], ![-15509, -2622374, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N0 : Ideal.span {2} * I167N0 =  Ideal.span {B.equivFun.symm ![-29, 63, -18]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E167RS0 


noncomputable def E167RS2 : RelationCertificate Table 2 ![![167, 0, 0], ![-52, 1, 0]]
  ![1073, 101, -56] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![334, 0, 0], ![-104, 2, 0]]
    hsu := by decide
    w := ![![2146, 202, -112], ![874, -1044, 292]]
    hw := by decide
    g := ![![![7818, -30432, -14486], ![-15215, 0, 0]], ![![-1849, 7197, 3426], ![3599, 0, 0]]]
    h := ![![![212331, -6491134, 489944], ![-104849, -20455176, 0]], ![![88309, -2699577, 203762], ![-43594, -8507027, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N2 : Ideal.span {2} * I167N2 =  Ideal.span {B.equivFun.symm ![1073, 101, -56]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E167RS2 


noncomputable def E191RS1 : RelationCertificate Table 2 ![![191, 0, 0], ![88, 1, 0]]
  ![623, -3033, -1155] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![382, 0, 0], ![176, 2, 0]]
    hsu := by decide
    w := ![![1246, -6066, -2310], ![7794, -37924, -14442]]
    hw := by decide
    g := ![![![-863, 543, -183], ![273, 0, 0]], ![![-379, 216, -72], ![109, 0, 0]]]
    h := ![![![-9503, -559365, -25725], ![-7278, 1228080, 0]], ![![-59451, -3498853, -160911], ![-45504, 7681695, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {2} * I191N1 =  Ideal.span {B.equivFun.symm ![623, -3033, -1155]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E191RS1 


noncomputable def E193RS1 : RelationCertificate Table 2 ![![193, 0, 0], ![95, 1, 0]]
  ![-16, 38, -11] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![386, 0, 0], ![190, 2, 0]]
    hsu := by decide
    w := ![![-32, 76, -22], ![208, -450, 130]]
    hw := by decide
    g := ![![![120, 18, 5], ![11, 0, 0]], ![![59, 10, 3], ![6, 0, 0]]]
    h := ![![![827, 56891, 2421], ![779, -116816, 0]], ![![-5615, -369194, -15711], ![-4551, 758072, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {2} * I193N1 =  Ideal.span {B.equivFun.symm ![-16, 38, -11]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E193RS1 
