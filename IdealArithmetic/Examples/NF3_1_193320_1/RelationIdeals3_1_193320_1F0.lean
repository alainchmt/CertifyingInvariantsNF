import IdealArithmetic.Examples.NF3_1_193320_1.PrimesBelow3_1_193320_1F0
import IdealArithmetic.Examples.NF3_1_193320_1.ClassGroupData3_1_193320_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 4 ![![2, 0, 0], ![1, 1, 0]]
  ![-25, -6, 1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![8, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![-100, -24, 4], ![136, 20, -4]]
    hw := by decide
    g := ![![![4, 1, 0], ![3, 1, 0]], ![![19, 7, 1], ![14, 1, 0]]]
    h := ![![![-18, -11, -2], ![11, 5, 0]], ![![22, 10, 2], ![-10, -5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {4} * I2N1 =  Ideal.span {B.equivFun.symm ![-25, -6, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 8 ![![5, 0, 0], ![1, 1, 0]]
  ![-653, -274, -31] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![40, 0, 0], ![8, 8, 0]]
    hsu := by decide
    w := ![![-5224, -2192, -248], ![-7072, -2968, -336]]
    hw := by decide
    g := ![![![131, -3064, -1556], ![-348, 12441, 0]], ![![7, -1022, -518], ![-123, 4147, 0]]]
    h := ![![![-121, -121, -82], ![-48, 379, 0]], ![![-164, -164, -111], ![-64, 513, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {8} * I5N0 =  Ideal.span {B.equivFun.symm ![-653, -274, -31]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 2 ![![5, 0, 0], ![2, 1, 0]]
  ![-299, -28, 7] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![10, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![-598, -56, 14], ![1302, 100, -28]]
    hw := by decide
    g := ![![![-442, -149, -21], ![-73, 0, 0]], ![![-958, -322, -47], ![-160, 3, 0]]]
    h := ![![![-631, -356, -31], ![1428, 162, 0]], ![![1363, 764, 66], ![-3082, -344, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {2} * I5N1 =  Ideal.span {B.equivFun.symm ![-299, -28, 7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 4 ![![7, 0, 0], ![-41, -3, 1]]
  ![-57697, 15710, -1039] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![28, 0, 0], ![-164, -12, 4]]
    hsu := by decide
    w := ![![-230788, 62840, -4156], ![-308648, -85500, 13632]]
    hw := by decide
    g := ![![![-18129129, -7171089, -1118772], ![-10857332, -777, 0]], ![![-27319967, -10809469, -1687426], ![-16362349, 4662, 0]]]
    h := ![![![-429, 2816, -339], ![1334, 0, 0]], ![![-123, -2256, 221], ![1861, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {4} * I7N0 =  Ideal.span {B.equivFun.symm ![-57697, 15710, -1039]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 8 ![![7, 0, 0], ![3, 1, 0]]
  ![46759, 19622, 2221] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![56, 0, 0], ![24, 8, 0]]
    hsu := by decide
    w := ![![374072, 156976, 17768], ![506624, 212600, 24064]]
    hw := by decide
    g := ![![![475, 37, -12], ![126, -3, 0]], ![![-107, -2, 3], ![-19, -7, 0]]]
    h := ![![![582433, 249299, 18510], ![-1343424, -127349, 0]], ![![788818, 337638, 25069], ![-1819466, -172475, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {8} * I7N1 =  Ideal.span {B.equivFun.symm ![46759, 19622, 2221]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 16 ![![11, 0, 0], ![4, 1, 0]]
  ![785, 26, -13] ![![16, 0, 0], ![2, 1, 0]] where
    su := ![![176, 0, 0], ![64, 16, 0]]
    hsu := by decide
    w := ![![12560, 416, -208], ![-848, 96, 0]]
    hw := by decide
    g := ![![![-1374, 191661, 96183], ![11813, -1538850, 0]], ![![-352, 60891, 30544], ![3774, -488613, 0]]]
    h := ![![![759, 195, 4], ![-1891, -57, 0]], ![![-59, -17, -1], ![149, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {16} * I11N0 =  Ideal.span {B.equivFun.symm ![785, 26, -13]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 4 ![![11, 0, 0], ![-3, 1, 0]]
  ![17151371, 7197414, 814669] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![44, 0, 0], ![-12, 4, 0]]
    hsu := by decide
    w := ![![68605484, 28789656, 3258676], ![185831176, 77982332, 8826752]]
    hw := by decide
    g := ![![![14853, 844, -539], ![7640, -39, 0]], ![![-11455, -438, 396], ![-5833, 9, 0]]]
    h := ![![![25724725, -7872601, 231308], ![88606868, -1729719, 0]], ![![69680366, -21324456, 626543], ![240008744, -4685285, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {4} * I11N1 =  Ideal.span {B.equivFun.symm ![17151371, 7197414, 814669]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 16 ![![11, 0, 0], ![-1, 1, 0]]
  ![-3492659, -1465662, -165897] ![![16, 0, 0], ![2, 1, 0]] where
    su := ![![176, 0, 0], ![-16, 16, 0]]
    hsu := by decide
    w := ![![-55882544, -23450592, -2654352], ![-37842160, -15880112, -1797456]]
    hw := by decide
    g := ![![![3005, -45715, -23108], ![-2466, 368765, 0]], ![![-1246, 273, 202], ![-135, -2815, 0]]]
    h := ![![![-681494, 234280, -18624], ![-4003775, 38967, 0]], ![![-461488, 158647, -12612], ![-2711233, 26391, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {16} * I11N2 =  Ideal.span {B.equivFun.symm ![-3492659, -1465662, -165897]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E11RS2 


noncomputable def E13RS1 : RelationCertificate Table 8 ![![13, 0, 0], ![5, 1, 0]]
  ![61, 2, -1] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![104, 0, 0], ![40, 8, 0]]
    hsu := by decide
    w := ![![488, 16, -8], ![-64, 8, 0]]
    hw := by decide
    g := ![![![-161, 5515, 2798], ![654, -22383, 0]], ![![-65, 2247, 1140], ![271, -9119, 0]]]
    h := ![![![1372, 329, 11], ![-3555, -144, 0]], ![![-186, -47, -2], ![482, 26, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {8} * I13N1 =  Ideal.span {B.equivFun.symm ![61, 2, -1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 4 ![![13, 0, 0], ![-6, 1, 0]]
  ![-61, -26, -3] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![52, 0, 0], ![-24, 4, 0]]
    hsu := by decide
    w := ![![-244, -104, -12], ![-680, -284, -32]]
    hw := by decide
    g := ![![![305, -3451, -1810], ![-708, 7245, 0]], ![![-126, 1577, 827], ![333, -3312, 0]]]
    h := ![![![-1537, 300, -8], ![-3320, 101, 0]], ![![-4286, 823, -20], ![-9258, 252, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {4} * I13N2 =  Ideal.span {B.equivFun.symm ![-61, -26, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS2 


noncomputable def E31RS0 : RelationCertificate Table 16 ![![31, 0, 0], ![0, 1, 0]]
  ![-775, -326, -37] ![![16, 0, 0], ![2, 1, 0]] where
    su := ![![496, 0, 0], ![0, 16, 0]]
    hsu := by decide
    w := ![![-12400, -5216, -592], ![-8432, -3536, -400]]
    hw := by decide
    g := ![![![-61, -166, -78], ![-18, 1275, 0]], ![![9, -127, -64], ![9, 1020, 0]]]
    h := ![![![-25, -11, 0], ![15, -37, 0]], ![![-17, -8, 0], ![27, -25, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {16} * I31N0 =  Ideal.span {B.equivFun.symm ![-775, -326, -37]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E31RS0 
