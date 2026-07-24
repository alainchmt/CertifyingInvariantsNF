import IdealArithmetic.Examples.NF3_1_441484_2.PrimesBelow3_1_441484_2F0
import IdealArithmetic.Examples.NF3_1_441484_2.ClassGroupData3_1_441484_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 3 ![![2, 0, 0], ![1, 1, 0]]
  ![-307, 286, 221] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![6, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![-921, 858, 663], ![-27651, 681, 2262]]
    hw := by decide
    g := ![![![-661687, 31183, -55170], ![10397, 3, 0]], ![![3278890, -154556, 273319], ![-51518, 4, 0]]]
    h := ![![![4144, 4433, 83], ![-8610, 5, 0]], ![![63110, 68483, 2764], ![-134135, -434, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {3} * I2N0 =  Ideal.span {B.equivFun.symm ![-307, 286, 221]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![3, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 9 ![![3, 0, 0], ![1, -1, 1]]
  ![34, -4, -5] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![27, 0, 0], ![9, -9, 9]]
    hsu := by decide
    w := ![![306, -36, -45], ![531, 36, -9]]
    hw := by decide
    g := ![![![14, 0, 7], ![5, -5, 0]], ![![89, -1, 13], ![-29, -4, 0]]]
    h := ![![![10, 0, -3], ![4, 0, 0]], ![![18, 3, -2], ![5, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {9} * I3N1 =  Ideal.span {B.equivFun.symm ![34, -4, -5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 3 ![![7, 0, 0], ![-3, 1, 1]]
  ![-58, -11, -4] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![21, 0, 0], ![-9, 3, 3]]
    hsu := by decide
    w := ![![-174, -33, -12], ![483, -105, -105]]
    hw := by decide
    g := ![![![-16, 192, 443], ![66, -124, 0]], ![![-94, -92, -230], ![-29, 62, 0]]]
    h := ![![![-7, -2, -1], ![3, 0, 0]], ![![20, -4, -4], ![-7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {3} * I7N0 =  Ideal.span {B.equivFun.symm ![-58, -11, -4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 9 ![![7, 0, 0], ![0, 1, 0]]
  ![13, -1, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![63, 0, 0], ![0, 9, 0]]
    hsu := by decide
    w := ![![117, -9, 9], ![-171, 9, -18]]
    hw := by decide
    g := ![![![8044141, 6033105, 31953113], ![-2011032, -26143456, 0]], ![![-574420, -430816, -2281725], ![143612, 1866866, 0]]]
    h := ![![![-338, -556, -1246], ![-74, 793, 0]], ![![494, 811, 1821], ![119, -1159, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {9} * I7N1 =  Ideal.span {B.equivFun.symm ![13, -1, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E17RS1 : RelationCertificate Table 9 ![![17, 0, 0], ![-6, 1, 0]]
  ![2903, -152, 242] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![153, 0, 0], ![-54, 9, 0]]
    hsu := by decide
    w := ![![26127, -1368, 2178], ![-40383, 2115, -3366]]
    hw := by decide
    g := ![![![51132, 38336, 203049], ![-12778, -166133, 0]], ![![-15196, -11405, -60412], ![3800, 49428, 0]]]
    h := ![![![960487, -341235, 3985828], ![-359051, -6159894, 0]], ![![-1484560, 527426, -6160671], ![554996, 9521003, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {9} * I17N1 =  Ideal.span {B.equivFun.symm ![2903, -152, 242]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 9 ![![19, 0, 0], ![1, 1, 0]]
  ![-4525, -446, -22] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![171, 0, 0], ![9, 9, 0]]
    hsu := by decide
    w := ![![-40725, -4014, -198], ![15075, -5373, -4752]]
    hw := by decide
    g := ![![![266562, -5573, 24750], ![-89465, -36, 0]], ![![-139026, 2918, -12848], ![46669, -32, 0]]]
    h := ![![![-105628, -211682, -389653], ![-16698, 673035, 0]], ![![58790, 117862, 217008], ![9305, -374880, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {9} * I19N0 =  Ideal.span {B.equivFun.symm ![-4525, -446, -22]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 9 ![![19, 0, 0], ![-1, 1, 0]]
  ![-10972, 5560, 4619] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![171, 0, 0], ![-9, 9, 0]]
    hsu := by decide
    w := ![![-98748, 50040, 41571], ![-546255, -9090, 28827]]
    hw := by decide
    g := ![![![26892481, -600214, 2305484], ![-9030841, 156774, 0]], ![![-16888171, 353937, -1563506], ![5668723, -1537, 0]]]
    h := ![![![-5231394, -6962938, -19161831], ![-91130, 33098128, 0]], ![![-28120744, -37429951, -103002963], ![-489941, 177914500, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {9} * I19N1 =  Ideal.span {B.equivFun.symm ![-10972, 5560, 4619]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS1 


noncomputable def E31RS0 : RelationCertificate Table 9 ![![31, 0, 0], ![14, 1, 0]]
  ![5446, -412, -641] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![279, 0, 0], ![126, 9, 0]]
    hsu := by decide
    w := ![![49014, -3708, -5769], ![65115, 5904, -45]]
    hw := by decide
    g := ![![![-506437, 10682, -46540], ![170005, -336, 0]], ![![-50429, 1091, -4493], ![16940, -152, 0]]]
    h := ![![![24084, 200457, 116365], ![17345, -327996, 0]], ![![31731, 264139, 153337], ![22855, -432132, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {9} * I31N0 =  Ideal.span {B.equivFun.symm ![5446, -412, -641]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 3 ![![31, 0, 0], ![-9, 1, 0]]
  ![-830759947, 43508500, -69253432] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![93, 0, 0], ![-27, 3, 0]]
    hsu := by decide
    w := ![![-2492279841, 130525500, -207760296], ![9064218228, -474710583, 755607228]]
    hw := by decide
    g := ![![![-57399, -79, 3614], ![-25, 10, 0]], ![![1463, -1870, -1556], ![-623, 0, 0]]]
    h := ![![![-19398960037, 28151623016, -77995505420], ![6540073036, 219799219508, 0]], ![![70552433297, -102385153665, 283663283031], ![-23785711386, -799391809535, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {3} * I31N1 =  Ideal.span {B.equivFun.symm ![-830759947, 43508500, -69253432]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
