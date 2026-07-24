import IdealArithmetic.Examples.NF3_1_45227_1.PrimesBelow3_1_45227_1F1
import IdealArithmetic.Examples.NF3_1_45227_1.ClassGroupData3_1_45227_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 2 ![![37, 0, 0], ![13, 1, 0]]
  ![466, -1211, -191] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![74, 0, 0], ![26, 2, 0]]
    hsu := by decide
    w := ![![932, -2422, -382], ![-2548, 3522, -3824]]
    hw := by decide
    g := ![![![21106024, -202328, 1325725], ![-101163, 111, 0]], ![![7659639, -73428, 481124], ![-36712, 39, 0]]]
    h := ![![![-3553, -59158, -13667], ![-2813, 168496, 0]], ![![9156, 152987, 35288], ![7370, -435856, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {2} * I37N1 =  Ideal.span {B.equivFun.symm ![466, -1211, -191]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E53RS1 : RelationCertificate Table 4 ![![53, 0, 0], ![10, 1, 0]]
  ![25542404, -306069, 1604583] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![212, 0, 0], ![40, 4, 0]]
    hsu := by decide
    w := ![![102169616, -1224276, 6418332], ![10926012, -130924, 686376]]
    hw := by decide
    g := ![![![45, 320, 672], ![82, -167, 0]], ![![88, -95, 159], ![-23, -35, 0]]]
    h := ![![![-64211611, -694032146, -208320336], ![-25210301, 3680860797, 0]], ![![-6866786, -74219752, -22277763], ![-2695985, 393631011, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {4} * I53N1 =  Ideal.span {B.equivFun.symm ![25542404, -306069, 1604583]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS1 


noncomputable def E59RS0 : RelationCertificate Table 4 ![![59, 0, 0], ![28, 1, 0]]
  ![2776568, -33271, 174425] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![236, 0, 0], ![112, 4, 0]]
    hsu := by decide
    w := ![![11106272, -133084, 697700], ![1187704, -14232, 74612]]
    hw := by decide
    g := ![![![521468670, -435, 1564405426], ![-107, -2085873839, 0]], ![![247476970, -215, 742430617], ![-53, -989907490, 0]]]
    h := ![![![126223955, 5583967553, 598565908], ![154546474, -11771738049, 0]], ![![13498370, 597149124, 64010599], ![16527214, -1258868896, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {4} * I59N0 =  Ideal.span {B.equivFun.symm ![2776568, -33271, 174425]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 4 ![![59, 0, 0], ![-15, 1, 0]]
  ![-112, 237, -39] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![236, 0, 0], ![-60, 4, 0]]
    hsu := by decide
    w := ![![-448, 948, -156], ![-36, 512, 672]]
    hw := by decide
    g := ![![![178270, -2012, 11058], ![-499, 192, 0]], ![![-44031, 496, -2733], ![127, -45, 0]]]
    h := ![![![-1516, 26011, -5205], ![868, 102352, 0]], ![![-148, 2535, -504], ![83, 9968, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {4} * I59N1 =  Ideal.span {B.equivFun.symm ![-112, 237, -39]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 4 ![![59, 0, 0], ![-14, 1, 0]]
  ![35132, -421, 2207] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![236, 0, 0], ![-56, 4, 0]]
    hsu := by decide
    w := ![![140528, -1684, 8828], ![15028, -180, 944]]
    hw := by decide
    g := ![![![11528, 46, 34645], ![12, -46207, 0]], ![![-2588, -9, -7775], ![-1, 10373, 0]]]
    h := ![![![-301245, 4726863, -1013414], ![151616, 19931211, 0]], ![![-32209, 505488, -108374], ![16239, 2131434, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {4} * I59N2 =  Ideal.span {B.equivFun.symm ![35132, -421, 2207]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS2 
