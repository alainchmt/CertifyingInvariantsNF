import IdealArithmetic.Examples.NF3_1_547128_1.PrimesBelow3_1_547128_1F4
import IdealArithmetic.Examples.NF3_1_547128_1.ClassGroupData3_1_547128_1

set_option linter.all false

noncomputable section


noncomputable def E199RS1 : RelationCertificate Table 2 ![![199, 0, 0], ![-57, 1, 0]]
  ![-2204, -357, -203] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![398, 0, 0], ![-114, 2, 0]]
    hsu := by decide
    w := ![![-4408, -714, -406], ![-29946, -4850, -2758]]
    hw := by decide
    g := ![![![787, -26, -28], ![-11, 0, 0]], ![![-246, 9, 7], ![5, 0, 0]]]
    h := ![![![-192623, 5742581, -1083587], ![84157, 21563361, 0]], ![![-1308801, 39012560, -7361411], ![571008, 146491941, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {2} * I199N1 =  Ideal.span {B.equivFun.symm ![-2204, -357, -203]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E199RS1 


noncomputable def E199RS2 : RelationCertificate Table 2 ![![199, 0, 0], ![-45, 1, 0]]
  ![0, -1, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![398, 0, 0], ![-90, 2, 0]]
    hsu := by decide
    w := ![![0, -2, 2], ![142, 2, -14]]
    hw := by decide
    g := ![![![0, -141170794912, -453048118411], ![-70585397455, 90109018025, -1251514140]], ![![0, 31943311078, 102513108245], ![15971655539, -20389347496, 283185382]]]
    h := ![![![9, -78, 19], ![23, -378, 0]], ![![21086, -464360, 113267], ![-6933, -2254014, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N2 : Ideal.span {2} * I199N2 =  Ideal.span {B.equivFun.symm ![0, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E199RS2 
