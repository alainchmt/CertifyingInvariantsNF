import IdealArithmetic.Examples.NF3_1_916300_1.PrimesBelow3_1_916300_1F1
import IdealArithmetic.Examples.NF3_1_916300_1.ClassGroupData3_1_916300_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 33 ![![37, 0, 0], ![2, 1, 0]]
  ![56, -13, -2] ![![33, 0, 0], ![9, 1, 0]] where
    su := ![![1221, 0, 0], ![66, 33, 0]]
    hsu := by decide
    w := ![![1848, -429, -66], ![198, 33, -33]]
    hw := by decide
    g := ![![![17, 5, 1], ![26, -18, 0]], ![![-2, 17, 2], ![19, -64, 0]]]
    h := ![![![3436, 1721, 2], ![-63538, -76, 0]], ![![366, 183, 0], ![-6768, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {33} * I37N1 =  Ideal.span {B.equivFun.symm ![56, -13, -2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E37RS1 


noncomputable def E43RS1 : RelationCertificate Table 33 ![![43, 0, 0], ![-14, 1, 0]]
  ![29, -13, 1] ![![33, 0, 0], ![15, 7, 1]] where
    su := ![![1419, 0, 0], ![-462, 33, 0]]
    hsu := by decide
    w := ![![957, -429, 33], ![-330, 396, -99]]
    hw := by decide
    g := ![![![-561, 154, -25], ![-193, 120, 0]], ![![159, -52, 7], ![80, -37, 0]]]
    h := ![![![14015, -1085, 6], ![43044, -257, 0]], ![![-4854, 388, -3], ![-14908, 126, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {33} * I43N1 =  Ideal.span {B.equivFun.symm ![29, -13, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E43RS1 


noncomputable def E47RS0 : RelationCertificate Table 11 ![![47, 0, 0], ![-22, 1, 0]]
  ![-46, 42, -9] ![![11, 0, 0], ![26, -4, 1]] where
    su := ![![517, 0, 0], ![-242, 11, 0]]
    hsu := by decide
    w := ![![-506, 462, -99], ![9361, -3344, 44]]
    hw := by decide
    g := ![![![-3974, -3732, 291], ![-7980, 0, 0]], ![![1593, 1519, -119], ![3250, 0, 0]]]
    h := ![![![-470, 40, -1], ![-1002, 38, 0]], ![![9179, -465, 2], ![19571, -90, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {11} * I47N0 =  Ideal.span {B.equivFun.symm ![-46, 42, -9]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 9 ![![47, 0, 0], ![-19, 1, 0]]
  ![47, -19, 1] ![![9, 0, 0], ![0, 1, 0]] where
    su := ![![423, 0, 0], ![-171, 9, 0]]
    hsu := by decide
    w := ![![423, -171, 9], ![153, 0, -18]]
    hw := by decide
    g := ![![![222, 8, -40], ![1, 398, 0]], ![![-76, -3, 16], ![2, -157, 0]]]
    h := ![![![172, -9, 0], ![423, 1, 0]], ![![80, 14, -1], ![197, 45, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {9} * I47N1 =  Ideal.span {B.equivFun.symm ![47, -19, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E47RS1 


noncomputable def E47RS2 : RelationCertificate Table 33 ![![47, 0, 0], ![-7, 1, 0]]
  ![1313, 47, 25] ![![33, 0, 0], ![9, 1, 0]] where
    su := ![![1551, 0, 0], ![-231, 33, 0]]
    hsu := by decide
    w := ![![43329, 1551, 825], ![15642, 561, 297]]
    hw := by decide
    g := ![![![-26, 2753, 306], ![86, -10100, 0]], ![![-5, -388, -43], ![19, 1420, 0]]]
    h := ![![![336474, -48990, 133], ![2258995, -6226, 0]], ![![121472, -17686, 48], ![815530, -2247, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {33} * I47N2 =  Ideal.span {B.equivFun.symm ![1313, 47, 25]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E47RS2 


noncomputable def E53RS0 : RelationCertificate Table 11 ![![53, 0, 0], ![18, 1, 0]]
  ![-562415, -20446, -10700] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![583, 0, 0], ![198, 11, 0]]
    hsu := by decide
    w := ![![-6186565, -224906, -117700], ![-512270, -18623, -9746]]
    hw := by decide
    g := ![![![-147, 146, -46], ![40, 450, 0]], ![![-64, 52, -15], ![17, 159, 0]]]
    h := ![![![-561937, -34275, -383], ![1623347, 9599, 0]], ![![-46562, -2845, -32], ![134512, 810, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {11} * I53N0 =  Ideal.span {B.equivFun.symm ![-562415, -20446, -10700]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 99 ![![53, 0, 0], ![-18, 1, 0]]
  ![65, -1, 1] ![![99, 0, 0], ![-18, 7, 1]] where
    su := ![![5247, 0, 0], ![-1782, 99, 0]]
    hsu := by decide
    w := ![![6435, -99, 99], ![-99, 297, 0]]
    hw := by decide
    g := ![![![10541538, -4492995, 594884], ![-2228318, -7083150, 0]], ![![-3303015, 1407805, -186397], ![698208, 2219387, 0]]]
    h := ![![![115, -6, 0], ![335, 1, 0]], ![![1, 0, 0], ![3, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {99} * I53N1 =  Ideal.span {B.equivFun.symm ![65, -1, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 3 ![![53, 0, 0], ![-1, 1, 0]]
  ![-50, -2, -1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![159, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![-150, -6, -3], ![-153, -3, -3]]
    hw := by decide
    g := ![![![2, 0, -8251], ![0, 24752, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
    h := ![![![0, 0, -1], ![50, 52, 0]], ![![0, 0, -1], ![51, 52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {3} * I53N2 =  Ideal.span {B.equivFun.symm ![-50, -2, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E53RS2 


noncomputable def E61RS0 : RelationCertificate Table 9 ![![61, 0, 0], ![30, 1, 0]]
  ![20, -10, 1] ![![9, 0, 0], ![0, 1, 0]] where
    su := ![![549, 0, 0], ![270, 9, 0]]
    hsu := by decide
    w := ![![180, -90, 9], ![153, -27, -9]]
    hw := by decide
    g := ![![![-76, -3, -109], ![3, 968, 0]], ![![-41, -2, -55], ![5, 488, 0]]]
    h := ![![![1220, 70, 1], ![-2480, -60, 0]], ![![1007, 34, 0], ![-2047, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {9} * I61N0 =  Ideal.span {B.equivFun.symm ![20, -10, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 33 ![![61, 0, 0], ![-23, 1, 0]]
  ![-82, -1, 10] ![![33, 0, 0], ![9, 1, 0]] where
    su := ![![2013, 0, 0], ![-759, 33, 0]]
    hsu := by decide
    w := ![![-2706, -33, 330], ![792, -561, 99]]
    hw := by decide
    g := ![![![-256, 523, 54], ![-37, -1949, 0]], ![![77, -193, -20], ![39, 715, 0]]]
    h := ![![![-352, 19, 0], ![-930, 10, 0]], ![![158, -6, 0], ![418, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {33} * I61N1 =  Ideal.span {B.equivFun.symm ![-82, -1, 10]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 11 ![![61, 0, 0], ![-8, 1, 0]]
  ![-8, 1, 0] ![![11, 0, 0], ![26, -4, 1]] where
    su := ![![671, 0, 0], ![-88, 11, 0]]
    hsu := by decide
    w := ![![-88, 11, 0], ![-55, 11, -11]]
    hw := by decide
    g := ![![![-7, -1, 0], ![-1, 0, 0]], ![![-25, 4, -1], ![11, 0, 0]]]
    h := ![![![-24, 11, -1], ![-182, 61, 0]], ![![-17, 10, -1], ![-129, 60, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {11} * I61N2 =  Ideal.span {B.equivFun.symm ![-8, 1, 0]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E61RS2 


noncomputable def E71RS1 : RelationCertificate Table 99 ![![71, 0, 0], ![-14, 1, 0]]
  ![-556, 188, 1] ![![99, 0, 0], ![9, 1, 0]] where
    su := ![![7029, 0, 0], ![-1386, 99, 0]]
    hsu := by decide
    w := ![![-55044, 18612, 99], ![-4851, 1089, 198]]
    hw := by decide
    g := ![![![-628629, 690017665, 76676385], ![6912787, -7590962480, 0]], ![![126130, -138458949, -15385884], ![-1387097, 1523202573, 0]]]
    h := ![![![-792032, 58634, -147], ![-4016694, 10438, 0]], ![![-69755, 5165, -13], ![-353754, 925, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {99} * I71N1 =  Ideal.span {B.equivFun.symm ![-556, 188, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E71RS1 
