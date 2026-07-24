import IdealArithmetic.Examples.NF3_3_866133_1.PrimesBelow3_3_866133_1F0
import IdealArithmetic.Examples.NF3_3_866133_1.ClassGroupData3_3_866133_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![317, 100, -65], ![-41, 33, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![317, 100, -65], ![-41, 33, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 32 ![![2, 0, 0], ![1, 1, 0]]
  ![201, 7, -4] ![![32, 0, 0], ![-10, 1, 0]] where
    su := ![![64, 0, 0], ![32, 32, 0]]
    hsu := by decide
    w := ![![6432, 224, -128], ![-3392, -128, 64]]
    hw := by decide
    g := ![![![1084, -7183, 2616], ![-543, -20917, 5]], ![![645, -4311, 1570], ![-326, -12552, 3]]]
    h := ![![![83, -14, -2], ![35, 0, 0]], ![![-44, 7, 1], ![-18, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {32} * I2N1 =  Ideal.span {B.equivFun.symm ![201, 7, -4]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 4 ![![3, 0, 0], ![1, 1, 0]]
  ![-7, -1, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![12, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![-28, -4, 0], ![-16, -8, -4]]
    hw := by decide
    g := ![![![-21272643, -2058760, -230786], ![-11151007, 0, 307715]], ![![-3162, -310, -35], ![-1654, 0, 46]]]
    h := ![![![37, -5, 88], ![14, -66, 0]], ![![12, -2, 29], ![4, -22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {4} * I3N0 =  Ideal.span {B.equivFun.symm ![-7, -1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 16 ![![5, 0, 0], ![-43, -3, 1]]
  ![-217, -7, 4] ![![16, 0, 0], ![6, 1, 0]] where
    su := ![![80, 0, 0], ![-688, -48, 16]]
    hsu := by decide
    w := ![![-3472, -112, 64], ![80, 0, 0]]
    hw := by decide
    g := ![![![148, 23, 0], ![67, 14, -8]], ![![-1304, -203, 0], ![-493, -121, 69]]]
    h := ![![![34, 4, -1], ![9, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {16} * I5N0 =  Ideal.span {B.equivFun.symm ![-217, -7, 4]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 4 ![![5, 0, 0], ![1, 1, 0]]
  ![-11, -1, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![20, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![-44, -4, 0], ![-24, -12, -4]]
    hw := by decide
    g := ![![![-92851, -8986, -1007], ![-48668, 0, 1343]], ![![-32757, -3172, -356], ![-17168, 0, 474]]]
    h := ![![![67, -3, 144], ![14, -180, 0]], ![![19, -2, 43], ![7, -54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {4} * I5N1 =  Ideal.span {B.equivFun.symm ![-11, -1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS1 


noncomputable def E13RS0 : RelationCertificate Table 16 ![![13, 0, 0], ![-48, -6, 1]]
  ![-101, -11, 4] ![![16, 0, 0], ![6, 1, 0]] where
    su := ![![208, 0, 0], ![-768, -96, 16]]
    hsu := by decide
    w := ![![-1616, -176, 64], ![768, 96, -16]]
    hw := by decide
    g := ![![![-4034178226779591, -12069469833289199, -9768947762750226], ![-2267158699622919, 39075800058186530, -5146963215]], ![![14523043047621839, 43450095681756538, 35168215411654377], ![8161772122967981, -140672894072488958, 18529069400]]]
    h := ![![![7, 1, 0], ![4, 0, 0]], ![![48, 6, -1], ![12, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {16} * I13N0 =  Ideal.span {B.equivFun.symm ![-101, -11, 4]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 4 ![![13, 0, 0], ![-3, 1, 0]]
  ![-863, -29, 16] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![52, 0, 0], ![-12, 4, 0]]
    hsu := by decide
    w := ![![-3452, -116, 64], ![3800, 116, -68]]
    hw := by decide
    g := ![![![3500, 344, 44], ![1836, 0, -49]], ![![-560, -48, 1], ![-292, 0, 10]]]
    h := ![![![24544, -52968, 53716], ![-9737, -174573, 0]], ![![-27037, 58352, -59177], ![10737, 192321, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {4} * I13N1 =  Ideal.span {B.equivFun.symm ![-863, -29, 16]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS1 


noncomputable def E19RS1 : RelationCertificate Table 8 ![![19, 0, 0], ![1, 1, 0]]
  ![-625, -23, 12] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![152, 0, 0], ![8, 8, 0]]
    hsu := by decide
    w := ![![-5000, -184, 96], ![5392, 200, -104]]
    hw := by decide
    g := ![![![-6001791389, 9681273343, -13360000046], ![2710607023, 26719996905, -12747]], ![![-571599182, 922026032, -1272380957], ![258153050, 2544761610, -1214]]]
    h := ![![![9003, -27, 18124], ![490, -86086, 0]], ![![-9707, 28, -19539], ![-507, 92807, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {8} * I19N1 =  Ideal.span {B.equivFun.symm ![-625, -23, 12]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 32 ![![23, 0, 0], ![-10, 1, 0]]
  ![695, 153, 36] ![![32, 0, 0], ![-10, 1, 0]] where
    su := ![![736, 0, 0], ![-320, 32, 0]]
    hsu := by decide
    w := ![![22240, 4896, 1152], ![5920, 1280, 288]]
    hw := by decide
    g := ![![![975695196, -6208236145, 2263209879], ![-498912118, -18105679086, -17]], ![![-401754409, 2556316853, -931904235], ![205433157, 7455233907, 7]]]
    h := ![![![5779, -41766, 15260], ![-4325, -87736, 0]], ![![1545, -11121, 4063], ![-1137, -23360, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {32} * I23N1 =  Ideal.span {B.equivFun.symm ![695, 153, 36]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 2 ![![29, 0, 0], ![-12, 1, 0]]
  ![-77, -17, -4] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![58, 0, 0], ![-24, 2, 0]]
    hsu := by decide
    w := ![![-154, -34, -8], ![-1430, -312, -72]]
    hw := by decide
    g := ![![![-120111, -17378, -351], ![-8689, 0, 690]], ![![39942, 5789, 119], ![2895, 0, -230]]]
    h := ![![![-2271, 19053, -5880], ![1623, 42629, 0]], ![![-21167, 176966, -54612], ![14894, 395928, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {2} * I29N1 =  Ideal.span {B.equivFun.symm ![-77, -17, -4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 32 ![![31, 0, 0], ![12, 1, 0]]
  ![-1101, -35, 20] ![![32, 0, 0], ![-10, 1, 0]] where
    su := ![![992, 0, 0], ![384, 32, 0]]
    hsu := by decide
    w := ![![-35232, -1120, 640], ![17920, 544, -320]]
    hw := by decide
    g := ![![![-385573780, 2453367680, -894374115], ![197159569, 7154992738, -82]], ![![-159878894, 1017293549, -370853918], ![81752587, 2966831270, -34]]]
    h := ![![![738753, 5001292, 1823900], ![447333, -14135220, 0]], ![![-375808, -2544082, -927790], ![-227511, 7190370, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {32} * I31N1 =  Ideal.span {B.equivFun.symm ![-1101, -35, 20]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E31RS1 
