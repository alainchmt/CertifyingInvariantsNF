import IdealArithmetic.Examples.NF3_1_271660_2.PrimesBelow3_1_271660_2F1
import IdealArithmetic.Examples.NF3_1_271660_2.ClassGroupData3_1_271660_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 5 ![![37, 0, 0], ![-14, 1, 0]]
  ![9, 2, 0] ![![5, 0, 0], ![-44, -7, 1]] where
    su := ![![185, 0, 0], ![-70, 5, 0]]
    hsu := by decide
    w := ![![45, 10, 0], ![80, -15, -5]]
    hw := by decide
    g := ![![![41, 9, -1], ![9, 0, 0]], ![![2, -1, 0], ![-2, 0, 0]]]
    h := ![![![57, -4, 0], ![150, 0, 0]], ![![92, -7, 0], ![242, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {5} * I37N1 =  Ideal.span {B.equivFun.symm ![9, 2, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 5 ![![41, 0, 0], ![-10, 1, 0]]
  ![7593, 261, -109] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![205, 0, 0], ![-50, 5, 0]]
    hsu := by decide
    w := ![![37965, 1305, -545], ![-33535, -80, 370]]
    hw := by decide
    g := ![![![84703, 30869, 8634], ![-10764, -25600, 0]], ![![-737, 464, -851], ![245, 4096, 0]]]
    h := ![![![388983, -40960, 206], ![1594071, -8555, 0]], ![![-343697, 36201, -183], ![-1408487, 7577, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {5} * I41N1 =  Ideal.span {B.equivFun.symm ![7593, 261, -109]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E43RS0 : RelationCertificate Table 5 ![![43, 0, 0], ![19, 1, 0]]
  ![29, -3, 0] ![![5, 0, 0], ![-44, -7, 1]] where
    su := ![![215, 0, 0], ![95, 5, 0]]
    hsu := by decide
    w := ![![145, -15, 0], ![-1990, -275, 50]]
    hw := by decide
    g := ![![![37, 16, 2], ![-1, 0, 0]], ![![39, 13, 1], ![1, 0, 0]]]
    h := ![![![1085, 76, 1], ![-2454, -43, 0]], ![![-15158, -1126, -17], ![34284, 741, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {5} * I43N0 =  Ideal.span {B.equivFun.symm ![29, -3, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 5 ![![43, 0, 0], ![-13, 1, 0]]
  ![40141, 3467, -793] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![215, 0, 0], ![-65, 5, 0]]
    hsu := by decide
    w := ![![200705, 17335, -3965], ![-228875, -17250, 4260]]
    hw := by decide
    g := ![![![-1053479, -444655, -43194], ![121768, -2064, 0]], ![![82593, 34952, 3289], ![-9524, 648, 0]]]
    h := ![![![173585, -13986, 42], ![571078, -2599, 0]], ![![-197945, 15972, -50], ![-651220, 3002, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {5} * I43N1 =  Ideal.span {B.equivFun.symm ![40141, 3467, -793]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 5 ![![53, 0, 0], ![-7, 1, 0]]
  ![-33, -11, -1] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![265, 0, 0], ![-35, 5, 0]]
    hsu := by decide
    w := ![![-165, -55, -5], ![-205, -90, -10]]
    hw := by decide
    g := ![![![2495, 64215, -66680], ![12346, 333396, 0]], ![![-330, -8410, 8732], ![-1615, -43659, 0]]]
    h := ![![![-1165, 173, -1], ![-8816, 52, 0]], ![![-1447, 213, -1], ![-10950, 51, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {5} * I53N1 =  Ideal.span {B.equivFun.symm ![-33, -11, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS1 


noncomputable def E61RS1 : RelationCertificate Table 5 ![![61, 0, 0], ![-2, 1, 0]]
  ![-57, -4, 1] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![305, 0, 0], ![-10, 5, 0]]
    hsu := by decide
    w := ![![-285, -20, 5], ![295, 15, -5]]
    hw := by decide
    g := ![![![3, 46, -49], ![12, 244, 0]], ![![0, -3, 2], ![4, -10, 0]]]
    h := ![![![-531, 267, -1], ![-16167, 62, 0]], ![![553, -276, 0], ![16837, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {5} * I61N1 =  Ideal.span {B.equivFun.symm ![-57, -4, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 5 ![![61, 0, 0], ![-1, 1, 0]]
  ![729129, 284045, 29499] ![![5, 0, 0], ![-44, -7, 1]] where
    su := ![![305, 0, 0], ![-5, 5, 0]]
    hsu := by decide
    w := ![![3645645, 1420225, 147495], ![-13624300, -5307585, -551210]]
    hw := by decide
    g := ![![![491, -1254, 23], ![-2529, 0, 0]], ![![-39, 150, -5], ![252, 0, 0]]]
    h := ![![![24286, -7680, 487], ![752317, -208, 0]], ![![-90754, 28699, -1824], ![-2811134, 1022, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {5} * I61N2 =  Ideal.span {B.equivFun.symm ![729129, 284045, 29499]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E61RS2 


noncomputable def E71RS0 : RelationCertificate Table 5 ![![71, 0, 0], ![9, 1, 0]]
  ![-1574107, -613221, -63685] ![![5, 0, 0], ![-44, -7, 1]] where
    su := ![![355, 0, 0], ![45, 5, 0]]
    hsu := by decide
    w := ![![-7870535, -3066105, -318425], ![29413320, 11458475, 1190000]]
    hw := by decide
    g := ![![![905, -2800, 125], ![-3871, 0, 0]], ![![83, -143, 4], ![-247, 0, 0]]]
    h := ![![![-1575047, -183852, -1194], ![12250470, 21089, 0]], ![![5886114, 687046, 4459], ![-45781270, -78589, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {5} * I71N0 =  Ideal.span {B.equivFun.symm ![-1574107, -613221, -63685]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS0 


noncomputable def E71RS2 : RelationCertificate Table 5 ![![71, 0, 0], ![-35, 1, 0]]
  ![241, 52, -8] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![355, 0, 0], ![-175, 5, 0]]
    hsu := by decide
    w := ![![1205, 260, -40], ![-2145, -355, 60]]
    hw := by decide
    g := ![![![-1151, -22993, 23747], ![-4366, -118791, 0]], ![![492, 10284, -10634], ![1963, 53190, 0]]]
    h := ![![![42836, -1437, 6], ![86889, -434, 0]], ![![-76134, 2600, -12], ![-154431, 864, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {5} * I71N2 =  Ideal.span {B.equivFun.symm ![241, 52, -8]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E71RS2 


noncomputable def E73RS0 : RelationCertificate Table 5 ![![73, 0, 0], ![34, 1, 0]]
  ![53266683, 20750971, 2155056] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![365, 0, 0], ![170, 5, 0]]
    hsu := by decide
    w := ![![266333415, 103754855, 10775280], ![459636645, 179059520, 18595915]]
    hw := by decide
    g := ![![![92509, -11194, 22442], ![-20736, -122141, 0]], ![![36767, -7644, 12325], ![-8877, -65628, 0]]]
    h := ![![![3439059711, 146878613, 1366786], ![-7382296830, -97620322, 0]], ![![5935109081, 253482274, 2358792], ![-12740324576, -168472633, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {5} * I73N0 =  Ideal.span {B.equivFun.symm ![53266683, 20750971, 2155056]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS0 


noncomputable def E73RS2 : RelationCertificate Table 5 ![![73, 0, 0], ![-15, 1, 0]]
  ![-36419697, -14187932, -1473463] ![![5, 0, 0], ![-44, -7, 1]] where
    su := ![![365, 0, 0], ![-75, 5, 0]]
    hsu := by decide
    w := ![![-182098485, -70939660, -7367315], ![680528210, 265111705, 27532715]]
    hw := by decide
    g := ![![![1311, -8423, 890], ![729, 0, 0]], ![![-247, 2092, -236], ![-531, 0, 0]]]
    h := ![![![-2927116164, 201609966, -466618], ![-14242870685, 32589651, 0]], ![![10939053814, -753445367, 1743815], ![53227654852, -121791952, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N2 : Ideal.span {5} * I73N2 =  Ideal.span {B.equivFun.symm ![-36419697, -14187932, -1473463]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E73RS2 
