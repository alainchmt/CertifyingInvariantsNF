import IdealArithmetic.Examples.NF3_1_392196_1.PrimesBelow3_1_392196_1F3
import IdealArithmetic.Examples.NF3_1_392196_1.ClassGroupData3_1_392196_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 6 ![![139, 0, 0], ![-31, 1, 0]]
  ![1480, -212, -267] ![![6, 0, 0], ![17, 1, 1]] where
    su := ![![834, 0, 0], ![-186, 6, 0]]
    hsu := by decide
    w := ![![8880, -1272, -1602], ![-25866, 7236, 318]]
    hw := by decide
    g := ![![![1080465476, -1284573962, 425786943], ![2918187731, -684164950, -139]], ![![-248745990, 295731323, -98022399], ![-671828817, 157505565, 32]]]
    h := ![![![95125, -1691699, 307623], ![-33303, -7126644, 0]], ![![-277323, 4932816, -897001], ![97338, 20780532, 0]]]
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
  ![62, 2, 3] ![![12, 0, 0], ![69, 1, 5]] where
    su := ![![2076, 0, 0], ![492, 12, 0]]
    hsu := by decide
    w := ![![744, 24, 36], ![6012, 0, 240]]
    hw := by decide
    g := ![![![49094006167314, -178958387385580, -44759745784943], ![248727442436499, -44157516423066, -173]], ![![11351454174250, -41378532576588, -10349291956302], ![57510445472309, -10210045242955, -40]]]
    h := ![![![-51744, -1094136, -168345], ![-18442, 4853948, 0]], ![![-418250, -8848831, -1361492], ![-150121, 39256356, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {12} * I173N1 =  Ideal.span {B.equivFun.symm ![62, 2, 3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E173RS1 
