import IdealArithmetic.Examples.NF3_1_283015_1.PrimesBelow3_1_283015_1F1
import IdealArithmetic.Examples.NF3_1_283015_1.ClassGroupData3_1_283015_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 3 ![![37, 0, 0], ![-10, 1, 0]]
  ![2062371, -131349, 156928] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![111, 0, 0], ![-30, 3, 0]]
    hsu := by decide
    w := ![![6187113, -394047, 470784], ![-15535872, 989454, -1182141]]
    hw := by decide
    g := ![![![-3504, -164, 299], ![-53, 0, 0]], ![![147, -90, -125], ![-27, 0, 0]]]
    h := ![![![63867743, -6679232, 298723], ![236104412, -1210647, 0]], ![![-160372172, 16771599, -750114], ![-592859174, 3040019, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {3} * I37N1 =  Ideal.span {B.equivFun.symm ![2062371, -131349, 156928]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E47RS1 : RelationCertificate Table 3 ![![47, 0, 0], ![-23, 1, 0]]
  ![-75172653, 4787622, -5719967] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![141, 0, 0], ![-69, 3, 0]]
    hsu := by decide
    w := ![![-225517959, 14362866, -17159901], ![566276733, -36065229, 43088598]]
    hw := by decide
    g := ![![![-7563, -2757, -2171], ![-916, 0, 0]], ![![8274, 1394, 476], ![467, 0, 0]]]
    h := ![![![-10436163, -1088745126, 445472879], ![-18057696, -2326993920, 0]], ![![26205307, 2733844503, -1118584647], ![45343066, 5843093475, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {3} * I47N1 =  Ideal.span {B.equivFun.symm ![-75172653, 4787622, -5719967]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 


noncomputable def E59RS1 : RelationCertificate Table 3 ![![59, 0, 0], ![-2, 1, 0]]
  ![228067562, -14525246, 17353903] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![177, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![684202686, -43575738, 52061709], ![-1718036397, 109418898, -130727214]]
    hw := by decide
    g := ![![![40838, 825, -4750], ![278, 0, 0]], ![![6586, 1043, 301], ![350, 0, 0]]]
    h := ![![![3925432, 112071065, -1010830627], ![1766463, 6628484544, 0]], ![![-9856777, -281411011, 2538200805], ![-4435522, -16644158137, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {3} * I59N1 =  Ideal.span {B.equivFun.symm ![228067562, -14525246, 17353903]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 
