import IdealArithmetic.Examples.NF3_1_358280_1.PrimesBelow3_1_358280_1F1
import IdealArithmetic.Examples.NF3_1_358280_1.ClassGroupData3_1_358280_1

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 2 ![![41, 0, 0], ![14, 1, 0]]
  ![56, -25, -5] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![82, 0, 0], ![28, 2, 0]]
    hsu := by decide
    w := ![![112, -50, -10], ![710, -94, -30]]
    hw := by decide
    g := ![![![-1489, 430, 2538], ![215, -5216, 0]], ![![-266, 76, 884], ![40, -1793, 0]]]
    h := ![![![28, -11, -1], ![-78, 36, 0]], ![![345, 14, -1], ![-985, 26, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {2} * I41N1 =  Ideal.span {B.equivFun.symm ![56, -25, -5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 2 ![![43, 0, 0], ![-2, 1, 0]]
  ![-229500345, 82855502, -10792075] ![![2, 0, 0], ![-20, 2, 1]] where
    su := ![![86, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-459000690, 165711004, -21584150], ![-2578050434, 930742230, -121230814]]
    hw := by decide
    g := ![![![-3440, -14351, -4331], ![17933, 0, 0]], ![![-257, -1838, -352], ![655, 0, 0]]]
    h := ![![![-731124757, 365564693, -623004], ![-15604432103, 15997097, 0]], ![![-4106478577, 2053252278, -3499196], ![-87644776797, 89850021, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {2} * I43N1 =  Ideal.span {B.equivFun.symm ![-229500345, 82855502, -10792075]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS1 


noncomputable def E71RS0 : RelationCertificate Table 2 ![![71, 0, 0], ![0, 1, 0]]
  ![-176604477, 63758739, -8304688] ![![2, 0, 0], ![-20, 2, 1]] where
    su := ![![142, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![-353208954, 127517478, -16609376], ![-1983854310, 716222212, -93289204]]
    hw := by decide
    g := ![![![-4428, -23310, -5680], ![18167, 0, 0]], ![![-257, -1838, -352], ![655, 0, 0]]]
    h := ![![![-2487387, 897832, 0], ![12667, -8304688, 0]], ![![-13970805, 5042818, 0], ![71028, -46644602, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {2} * I71N0 =  Ideal.span {B.equivFun.symm ![-176604477, 63758739, -8304688]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 2 ![![71, 0, 0], ![5, 1, 0]]
  ![5, 1, 0] ![![2, 0, 0], ![-20, 2, 1]] where
    su := ![![142, 0, 0], ![10, 2, 0]]
    hsu := by decide
    w := ![![10, 2, 0], ![-242, 20, 8]]
    hw := by decide
    g := ![![![10, 2, -1], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![35, 7, 0], ![-496, 0, 0]], ![![-971, -199, -1], ![13764, 75, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {2} * I71N1 =  Ideal.span {B.equivFun.symm ![5, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 2 ![![71, 0, 0], ![-6, 1, 0]]
  ![-335292081, 121049028, -15766849] ![![2, 0, 0], ![-20, 2, 1]] where
    su := ![![142, 0, 0], ![-12, 2, 0]]
    hsu := by decide
    w := ![![-670584162, 242098056, -31533698], ![-3766442682, 1359782266, -177114034]]
    hw := by decide
    g := ![![![1740, 25611, 2585], ![9617, 0, 0]], ![![-257, -1838, -352], ![655, 0, 0]]]
    h := ![![![-392362527, 66701004, -286969], ![-4587074556, 4607950, 0]], ![![-2203766643, 374636797, -1611804], ![-25764035052, 25881067, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {2} * I71N2 =  Ideal.span {B.equivFun.symm ![-335292081, 121049028, -15766849]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS2 
