import IdealArithmetic.Examples.NF3_1_392196_1.PrimesBelow3_1_392196_1F3
import IdealArithmetic.Examples.NF3_1_392196_1.ClassGroupData3_1_392196_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 6 ![![139, 0, 0], ![-31, 1, 0]]
  ![1480, -212, -267] ![![6, 0, 0], ![17, -2, 1]] where
    su := ![![834, 0, 0], ![-186, 6, 0]]
    hsu := by decide
    w := ![![8880, -1272, -1602], ![39486, -16098, 5736]]
    hw := by decide
    g := ![![![10659639998, 7335814656, -15026022723], ![25252704659, -6490304065, 2363]], ![![-2454024132, -1688826432, 3459228696], ![-5813588083, 1494170720, -544]]]
    h := ![![![95125, -1691699, 307623], ![-33303, -7126644, 0]], ![![423784, -7537641, 1370678], ![-148657, -31753881, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {6} * I139N1 =  Ideal.span {B.equivFun.symm ![1480, -212, -267]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E139RS1 


noncomputable def E151RS1 : RelationCertificate Table 4 ![![151, 0, 0], ![44, 1, 0]]
  ![943314, 9786, 40453] ![![4, 0, 0], ![15, 0, 1]] where
    su := ![![604, 0, 0], ![176, 4, 0]]
    hsu := by decide
    w := ![![3773256, 39144, 161812], ![16793428, 174216, 720168]]
    hw := by decide
    g := ![![![706521, -900081, -381417], ![2554123, -514182, 0]], ![![475984637259, -606254116992, -256960127499], ![1720702357892, -346430923955, 0]]]
    h := ![![![774573958, 18389994668, 2627471107], ![347491846, -66124682784, 0]], ![![3447354883, 81847362438, 11693944662], ![1546562856, -294297577320, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {4} * I151N1 =  Ideal.span {B.equivFun.symm ![943314, 9786, 40453]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E151RS1 


noncomputable def E173RS1 : RelationCertificate Table 12 ![![173, 0, 0], ![41, 1, 0]]
  ![62, 2, 3] ![![12, 0, 0], ![-9, -5, -1]] where
    su := ![![2076, 0, 0], ![492, 12, 0]]
    hsu := by decide
    w := ![![744, 24, 36], ![-2076, 48, -120]]
    hw := by decide
    g := ![![![-11711608557600, 6866256204068, -5331420232807], ![6367051352589, -2198252942082, -173]], ![![-2707388600007, 1587281856307, -1232471721469], ![1471879986675, -508173145137, -40]]]
    h := ![![![-51744, -1094136, -168345], ![-18442, 4853948, 0]], ![![144490, 3057443, 470422], ![51969, -13563836, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {12} * I173N1 =  Ideal.span {B.equivFun.symm ![62, 2, 3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E173RS1 
