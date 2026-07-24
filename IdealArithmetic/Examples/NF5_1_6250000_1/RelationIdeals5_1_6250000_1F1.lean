import IdealArithmetic.Examples.NF5_1_6250000_1.PrimesBelow5_1_6250000_1F1
import IdealArithmetic.Examples.NF5_1_6250000_1.ClassGroupData5_1_6250000_1

set_option linter.all false

noncomputable section


noncomputable def E31RS2 : RelationCertificate Table 4 ![![31, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
  ![-8, 3, 7, 4, 11] ![![4, 0, 0, 0, 0], ![2, 11, -9, -3, -14]] where
    su := ![![124, 0, 0, 0, 0], ![-16, 4, 0, 0, 0]]
    hsu := by decide
    w := ![![-32, 12, 28, 16, 44], ![-20, -160, 112, 32, 180]]
    hw := by decide
    g := ![![![631118, -46182, -67671, 21786, 52003], ![142569, 319275, 21285, 0, 0]], ![![-44034, 3219, 4724, -1519, -3624], ![-9946, -22276, -1485, 0, 0]]]
    h := ![![![862368, -3306709, 12756375, -6391236, 5333], ![6673022, 809022, 99057272, -13776, 0]], ![![2116794, -8116549, 31311365, -15687711, 13095], ![16379786, 1985811, 243142612, -33825, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {4} * I31N2 =  Ideal.span {B.equivFun.symm ![-8, 3, 7, 4, 11]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E31RS2 


noncomputable def E47RS2 : RelationCertificate Table 2 ![![47, 0, 0, 0, 0], ![18, 1, 0, 0, 0]]
  ![1, 1, -1, 1, 2] ![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] where
    su := ![![94, 0, 0, 0, 0], ![36, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![2, 2, -2, 2, 4], ![-4, 12, -8, -6, -24]]
    hw := by decide
    g := ![![![155210, -224543, 19068, -59054, 36502], ![23341, 136323, 1683, 0, 0]], ![![86240, -124739, 10602, -32804, 20290], ![12968, 75738, 935, 0, 0]]]
    h := ![![![-2101, -100, 2388, 221, -26], ![5469, 311, -6264, 102, 0]], ![![-35929, -1379, 42696, 3966, -456], ![93517, 4724, -111945, 1785, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {2} * I47N2 =  Ideal.span {B.equivFun.symm ![1, 1, -1, 1, 2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E47RS2 


noncomputable def E59RS2 : RelationCertificate Table 4 ![![59, 0, 0, 0, 0], ![-19, 1, 0, 0, 0]]
  ![-3, -4, -2, -1, -1] ![![4, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] where
    su := ![![236, 0, 0, 0, 0], ![-76, 4, 0, 0, 0]]
    hsu := by decide
    w := ![![-12, -16, -8, -4, -4], ![-8, -12, -4, -4, -8]]
    hw := by decide
    g := ![![![-36, 0, 13, 9, 55], ![59, 0, 0, 0, 34]], ![![7, 0, -5, -3, -22], ![-19, 1, 0, 0, -16]]]
    h := ![![![-10322753, 1754642, -28080952, 2976685, -14675], ![-32043472, -832986, -87234992, 72152, 0]], ![![-6937186, 1179165, -18871161, 2000413, -9862], ![-21534132, -559798, -58624280, 48488, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {4} * I59N2 =  Ideal.span {B.equivFun.symm ![-3, -4, -2, -1, -1]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E59RS2 
