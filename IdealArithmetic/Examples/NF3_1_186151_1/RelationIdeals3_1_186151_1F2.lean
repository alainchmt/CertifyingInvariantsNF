import IdealArithmetic.Examples.NF3_1_186151_1.PrimesBelow3_1_186151_1F2
import IdealArithmetic.Examples.NF3_1_186151_1.ClassGroupData3_1_186151_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 9 ![![89, 0, 0], ![25, 1, 0]]
  ![31, 12, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![801, 0, 0], ![225, 9, 0]]
    hsu := by decide
    w := ![![279, 108, 9], ![180, 72, 9]]
    hw := by decide
    g := ![![![-31713, -950508, 320356], ![-95039, -2883200, 0]], ![![-9353, -280400, 94505], ![-28035, -850544, 0]]]
    h := ![![![4454, 178, 0], ![-15855, 1, 0]], ![![2880, 115, 0], ![-10252, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {9} * I89N1 =  Ideal.span {B.equivFun.symm ![31, 12, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E89RS1 


noncomputable def E101RS1 : RelationCertificate Table 3 ![![101, 0, 0], ![27, 1, 0]]
  ![-19, -9, -1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![303, 0, 0], ![81, 3, 0]]
    hsu := by decide
    w := ![![-57, -27, -3], ![-273, -96, -9]]
    hw := by decide
    g := ![![![-58, -11, -84745], ![-1, 254240, 0]], ![![-11, -3, -23305], ![2, 69916, 0]]]
    h := ![![![-86, -30, -1], ![321, 100, 0]], ![![-392, -41, -1], ![1463, 98, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {3} * I101N1 =  Ideal.span {B.equivFun.symm ![-19, -9, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 9 ![![103, 0, 0], ![9, 1, 0]]
  ![-32, -6, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![927, 0, 0], ![81, 9, 0]]
    hsu := by decide
    w := ![![-288, -54, 9], ![369, 63, -9]]
    hw := by decide
    g := ![![![27043, 810992, -273334], ![81096, 2460005, 0]], ![![2476, 74226, -25017], ![7426, 225153, 0]]]
    h := ![![![-80, -9, 0], ![912, 1, 0]], ![![62, -2, -1], ![-705, 102, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {9} * I103N1 =  Ideal.span {B.equivFun.symm ![-32, -6, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS1 


noncomputable def E107RS0 : RelationCertificate Table 9 ![![107, 0, 0], ![44, 1, 0]]
  ![-305, -114, -11] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![963, 0, 0], ![396, 9, 0]]
    hsu := by decide
    w := ![![-2745, -1026, -99], ![-2088, -810, -81]]
    hw := by decide
    g := ![![![189, 270, -86], ![-23, 738, 0]], ![![5313, 157430, -53058], ![15727, 477509, 0]]]
    h := ![![![-48819, -1502, -9], ![118712, 952, 0]], ![![-37088, -1148, -7], ![90186, 740, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {9} * I107N0 =  Ideal.span {B.equivFun.symm ![-305, -114, -11]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 9 ![![107, 0, 0], ![-26, 1, 0]]
  ![-5, 3, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![963, 0, 0], ![-234, 9, 0]]
    hsu := by decide
    w := ![![-45, 27, 9], ![288, 63, 0]]
    hw := by decide
    g := ![![![40, -24, 9], ![-16, -88, 0]], ![![-11, 5, -2], ![6, 20, 0]]]
    h := ![![![-1267, 75, -1], ![-5214, 108, 0]], ![![8348, -321, 0], ![34354, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {9} * I107N1 =  Ideal.span {B.equivFun.symm ![-5, 3, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E107RS1 


noncomputable def E107RS2 : RelationCertificate Table 9 ![![107, 0, 0], ![-18, 1, 0]]
  ![137, 51, 5] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![963, 0, 0], ![-162, 9, 0]]
    hsu := by decide
    w := ![![1233, 459, 45], ![954, 369, 36]]
    hw := by decide
    g := ![![![22, -236, 79], ![-30, -712, 0]], ![![-1, 35, -12], ![14, 108, 0]]]
    h := ![![![187, -9, 0], ![1104, 5, 0]], ![![146, -7, 0], ![862, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {9} * I107N2 =  Ideal.span {B.equivFun.symm ![137, 51, 5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E107RS2 


noncomputable def E109RS0 : RelationCertificate Table 3 ![![109, 0, 0], ![46, 1, 0]]
  ![74, 3, -1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![327, 0, 0], ![138, 3, 0]]
    hsu := by decide
    w := ![![222, 9, -3], ![-273, -3, 3]]
    hw := by decide
    g := ![![![15, 5, 16], ![2, -46, 0]], ![![8, 2, 7], ![3, -20, 0]]]
    h := ![![![5086, 111, 0], ![-12050, -1, 0]], ![![-6283, -183, -1], ![14886, 110, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {3} * I109N0 =  Ideal.span {B.equivFun.symm ![74, 3, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 3 ![![109, 0, 0], ![-27, 1, 0]]
  ![37, 12, 1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![327, 0, 0], ![-81, 3, 0]]
    hsu := by decide
    w := ![![111, 36, 3], ![273, 114, 12]]
    hw := by decide
    g := ![![![-152, -18, 65990], ![-3, -197960, 0]], ![![46, 5, -15681], ![2, 47040, 0]]]
    h := ![![![3034, -112, 0], ![12247, 1, 0]], ![![7408, -273, 0], ![29903, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {3} * I109N1 =  Ideal.span {B.equivFun.symm ![37, 12, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 3 ![![109, 0, 0], ![-19, 1, 0]]
  ![115, 9, -2] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![327, 0, 0], ![-57, 3, 0]]
    hsu := by decide
    w := ![![345, 27, -6], ![-546, -39, 9]]
    hw := by decide
    g := ![![![-22, -6, 5], ![-1, -16, 0]], ![![3, 0, 0], ![2, 0, 0]]]
    h := ![![![604, -32, 0], ![3459, -2, 0]], ![![-906, 67, -1], ![-5188, 112, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {3} * I109N2 =  Ideal.span {B.equivFun.symm ![115, 9, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS2 
