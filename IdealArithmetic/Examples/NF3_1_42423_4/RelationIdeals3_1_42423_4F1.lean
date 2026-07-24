import IdealArithmetic.Examples.NF3_1_42423_4.PrimesBelow3_1_42423_4F1
import IdealArithmetic.Examples.NF3_1_42423_4.ClassGroupData3_1_42423_4

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 3 ![![41, 0, 0], ![13, 1, 0]]
  ![41, -11, -1] ![![3, 0, 0], ![4, 0, 1]] where
    su := ![![123, 0, 0], ![39, 3, 0]]
    hsu := by decide
    w := ![![123, -33, -3], ![-231, 18, 54]]
    hw := by decide
    g := ![![![506, 192, -88], ![653, 0, 0]], ![![204, 77, -35], ![261, 0, 0]]]
    h := ![![![-102, 1348, 289], ![21, -3950, 0]], ![![176, -2508, -537], ![4, 7345, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {3} * I41N1 =  Ideal.span {B.equivFun.symm ![41, -11, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 3 ![![43, 0, 0], ![-21, 1, 0]]
  ![-531, -74, -50] ![![3, 0, 0], ![4, 0, 1]] where
    su := ![![129, 0, 0], ![-63, 3, 0]]
    hsu := by decide
    w := ![![-1593, -222, -150], ![-3786, -528, -357]]
    hw := by decide
    g := ![![![-21, 6, 13], ![-17, 0, 0]], ![![9, -5, -8], ![14, 0, 0]]]
    h := ![![![-270, -5517, 826], ![37, -11856, 0]], ![![-668, -13110, 1963], ![34, -28176, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {3} * I43N1 =  Ideal.span {B.equivFun.symm ![-531, -74, -50]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 3 ![![53, 0, 0], ![20, 1, 0]]
  ![-23, 4, 3] ![![3, 0, 0], ![5, 1, 1]] where
    su := ![![159, 0, 0], ![60, 3, 0]]
    hsu := by decide
    w := ![![-69, 12, 9], ![78, -3, -21]]
    hw := by decide
    g := ![![![113, 100, -85], ![201, 0, -53]], ![![41, 35, -32], ![81, 0, -19]]]
    h := ![![![25, -820, -117], ![36, 2068, 0]], ![![-61, 910, 130], ![48, -2299, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {3} * I53N1 =  Ideal.span {B.equivFun.symm ![-23, 4, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS1 
