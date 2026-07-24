import IdealArithmetic.Examples.NF3_3_895700_1.PrimesBelow3_3_895700_1F0
import IdealArithmetic.Examples.NF3_3_895700_1.ClassGroupData3_3_895700_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 171 ![![2, 0, 0], ![-57, 3, 1]]
  ![-86, 0, 1] ![![171, 0, 0], ![-1, 1, 0]] where
    su := ![![342, 0, 0], ![-9747, 513, 171]]
    hsu := by decide
    w := ![![-14706, 0, 171], ![-342, 0, 0]]
    hw := by decide
    g := ![![![0, 0, -2], ![170, 171, 0]], ![![-72974, 14663, -1], ![114, 84, -29156]]]
    h := ![![![-16636, 155454, 96319], ![756707, 0, -29667]], ![![-370, 3573, 2214], ![17396, 0, -682]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {171} * I2N0 =  Ideal.span {B.equivFun.symm ![-86, 0, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 9 ![![3, 0, 0], ![-59, 3, 1]]
  ![82, -9, -2] ![![9, 0, 0], ![-1, 1, 0]] where
    su := ![![27, 0, 0], ![-531, 27, 9]]
    hsu := by decide
    w := ![![738, -81, -18], ![765, -81, -18]]
    hw := by decide
    g := ![![![1, -2, 4], ![1, -18, 0]], ![![-32, 38, -79], ![12, 355, 0]]]
    h := ![![![47, -4, -1], ![1, 0, 0]], ![![48, -4, -1], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![82, -9, -2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![3, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 57 ![![5, 0, 0], ![-2, 1, 0]]
  ![-29, 0, 1] ![![57, 0, 0], ![-1, 1, 0]] where
    su := ![![285, 0, 0], ![-114, 57, 0]]
    hsu := by decide
    w := ![![-1653, 0, 57], ![-399, 57, 0]]
    hw := by decide
    g := ![![![-56, 55, -111], ![32, 3164, 0]], ![![14, -15, 29], ![33, -826, 0]]]
    h := ![![![2411, -6150, 6589], ![-2194, -16472, 0]], ![![625, -1591, 1704], ![-564, -4260, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {57} * I5N0 =  Ideal.span {B.equivFun.symm ![-29, 0, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E5RS0 


noncomputable def E13RS0 : RelationCertificate Table 171 ![![13, 0, 0], ![4, 1, 0]]
  ![-173, 0, 4] ![![171, 0, 0], ![-1, 1, 0]] where
    su := ![![2223, 0, 0], ![684, 171, 0]]
    hsu := by decide
    w := ![![-29583, 0, 684], ![-1539, 171, 0]]
    hw := by decide
    g := ![![![-2656297, 2656296, -5312956], ![31140, 454257740, 0]], ![![-1135873, 1135872, -2271900], ![13357, 194247452, 0]]]
    h := ![![![244701, 1169543, 591128], ![165261, -3842330, 0]], ![![12870, 61519, 31094], ![8698, -202111, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {171} * I13N0 =  Ideal.span {B.equivFun.symm ![-173, 0, 4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS0 


noncomputable def E19RS1 : RelationCertificate Table 1 ![![19, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![19, 0, 0], ![-1, 1, 0]] where
    su := ![![19, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![19, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {1} * I19N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 171 ![![23, 0, 0], ![-5, 1, 0]]
  ![1, 0, -2] ![![171, 0, 0], ![-1, 1, 0]] where
    su := ![![3933, 0, 0], ![-855, 171, 0]]
    hsu := by decide
    w := ![![171, 0, -342], ![855, -171, 0]]
    hw := by decide
    g := ![![![15457611, -15457612, 30917338], ![-180742, -2643432398, 0]], ![![-2689648, 2689648, -5379664], ![31463, 459961272, 0]]]
    h := ![![![2, 9, -4], ![18, 45, 0]], ![![-5, 49, -20], ![22, 230, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {171} * I23N1 =  Ideal.span {B.equivFun.symm ![1, 0, -2]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E23RS1 


noncomputable def E31RS1 : RelationCertificate Table 3249 ![![31, 0, 0], ![6, 1, 0]]
  ![-3031, 342, 77] ![![3249, 0, 0], ![-685, 1, 0]] where
    su := ![![100719, 0, 0], ![19494, 3249, 0]]
    hsu := by decide
    w := ![![-9847719, 1111158, 250173], ![2043621, -230679, -51984]]
    hw := by decide
    g := ![![![3466330304, -2595347403447, 7577658027], ![-1529632566, -12309905464864, 0]], ![![822399037, -615755105954, 1797825453], ![-362909456, -2920567448400, 0]]]
    h := ![![![33069, 214047, 71491], ![13317, -1108072, 0]], ![![-6865, -44420, -14836], ![-2751, 229950, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {3249} * I31N1 =  Ideal.span {B.equivFun.symm ![-3031, 342, 77]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E31RS1 
