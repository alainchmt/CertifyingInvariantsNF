import IdealArithmetic.Examples.NF3_1_732108_1.PrimesBelow3_1_732108_1F2
import IdealArithmetic.Examples.NF3_1_732108_1.ClassGroupData3_1_732108_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 15 ![![89, 0, 0], ![21, 1, 0]]
  ![26696384, 345044, 818305] ![![15, 0, 0], ![-3, 1, 0]] where
    su := ![![1335, 0, 0], ![315, 15, 0]]
    hsu := by decide
    w := ![![400445760, 5175660, 12274575], ![-50501955, -652725, -1548000]]
    hw := by decide
    g := ![![![784716891222, 413916602874, -2026466698619], ![-129348938040, 6079400096272, 200]], ![![196179216378, 103479147278, -506616657962], ![-32337233447, 1519849974008, 50]]]
    h := ![![![-248409895, 2930166165, 636938245], ![-25690341, -11337337100, 0]], ![![31328043, -369535989, -80327050], ![3239956, 1429800850, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {15} * I89N1 =  Ideal.span {B.equivFun.symm ![26696384, 345044, 818305]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E89RS1 


noncomputable def E101RS1 : RelationCertificate Table 15 ![![101, 0, 0], ![26, 1, 0]]
  ![-31, 29, -5] ![![15, 0, 0], ![-3, 1, 0]] where
    su := ![![1515, 0, 0], ![390, 15, 0]]
    hsu := by decide
    w := ![![-465, 435, -75], ![-150, 105, 165]]
    hw := by decide
    g := ![![![-6693675, -5896875, 21319573], ![945625, -64516021, -696716]], ![![-1818935, -1602412, 5793362], ![256968, -17531527, -189325]]]
    h := ![![![31719, -457416, -81675], ![3693, 1649834, 0]], ![![10156, -146587, -26174], ![1218, 528717, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {15} * I101N1 =  Ideal.span {B.equivFun.symm ![-31, 29, -5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E101RS1 


noncomputable def E107RS1 : RelationCertificate Table 75 ![![107, 0, 0], ![18, 1, 0]]
  ![-360264082, -4656322, -11042915] ![![75, 0, 0], ![27, 1, 0]] where
    su := ![![8025, 0, 0], ![1350, 75, 0]]
    hsu := by decide
    w := ![![-27019806150, -349224150, -828218625], ![-10126405425, -130881225, -310397400]]
    hw := by decide
    g := ![![![124980474060192154627614, -1914117239615672552913360, -329975451870594599835209], ![19471407466793541627155, 4949631778058918912612906, 16330061]], ![![22109567892711578249788, -338615334772297326230658, -58374035711749933627073], ![3444573311078870486925, 875610535676248989384286, 2888856]]]
    h := ![![![319180723856, -3231580210997, -807840256595], ![23492269357, 17287779282550, 0]], ![![119621635907, -1211122359586, -302760053551], ![8804365319, 6479064318265, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {75} * I107N1 =  Ideal.span {B.equivFun.symm ![-360264082, -4656322, -11042915]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E107RS1 


noncomputable def E113RS1 : RelationCertificate Table 15 ![![113, 0, 0], ![-40, 1, 0]]
  ![-4437843, -57358, -136030] ![![15, 0, 0], ![20, 1, 1]] where
    su := ![![1695, 0, 0], ![-600, 15, 0]]
    hsu := by decide
    w := ![![-66567645, -860370, -2040450], ![-94573230, -1222335, -2898885]]
    hw := by decide
    g := ![![![-3264895, 5806022, 4050206], ![-3696110, 0, 4389014]], ![![1140806, -2028741, -1415218], ![1291505, 0, -1533613]]]
    h := ![![![5883974021, 118746083446, -15623284290], ![-1031972332, 353086197748, 0]], ![![8359412890, 168703589583, -22196135353], ![-1466131980, 501632620326, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {15} * I113N1 =  Ideal.span {B.equivFun.symm ![-4437843, -57358, -136030]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 5 ![![131, 0, 0], ![47, 1, 0]]
  ![29, 14, -220] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![655, 0, 0], ![235, 5, 0]]
    hsu := by decide
    w := ![![145, 70, -1100], ![-8110, 7345, -150]]
    hw := by decide
    g := ![![![11808163, -10128051, 355938], ![2697659, 0, -1456930]], ![![4259649, -3642424, 128474], ![975379, 0, -523840]]]
    h := ![![![24739, -641326, -65440], ![4004, 1714484, 0]], ![![-1405136, 36414227, 3715560], ![-226046, -97347678, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {5} * I131N1 =  Ideal.span {B.equivFun.symm ![29, 14, -220]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 3 ![![137, 0, 0], ![51, 1, 0]]
  ![-79, 135, -349] ![![3, 0, 0], ![23, 1, 1]] where
    su := ![![411, 0, 0], ![153, 3, 0]]
    hsu := by decide
    w := ![![-237, 405, -1047], ![-6864, 5472, 3951]]
    hw := by decide
    g := ![![![850508, -1366595, -552224], ![5881004, 0, 0]], ![![323487, -519788, -210040], ![2236855, 0, 0]]]
    h := ![![![-3343, 92919, 8763], ![-440, -240176, 0]], ![![-93680, 2636256, 248701], ![-15616, -6814144, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {3} * I137N1 =  Ideal.span {B.equivFun.symm ![-79, 135, -349]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E137RS1 
