import IdealArithmetic.Examples.NF3_3_455700_1.PrimesBelow3_3_455700_1F3
import IdealArithmetic.Examples.NF3_3_455700_1.ClassGroupData3_3_455700_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 363 ![![139, 0, 0], ![42, 1, 0]]
  ![-254, 287, -81] ![![363, 0, 0], ![-80, 1, 0]] where
    su := ![![50457, 0, 0], ![15246, 363, 0]]
    hsu := by decide
    w := ![![-92202, 104181, -29403], ![41019, -27588, 7260]]
    hw := by decide
    g := ![![![697224793513529348, -61471902540527381850, 2305229713293669452], ![-323002440830880471, -278932795308143368040, 14834260]], ![![227665238707333163, -20072457973213940072, 752728069676794249], ![-105470184765290690, -91080096430764549624, 4843840]]]
    h := ![![![7454479, 375964222, 26857134], ![4957327, -1244380569, 0]], ![![-3300793, -166472100, -11891992], ![-2194888, 550995636, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {363} * I139N1 =  Ideal.span {B.equivFun.symm ![-254, 287, -81]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 33 ![![149, 0, 0], ![-74, 1, 0]]
  ![205, -40, 6] ![![33, 0, 0], ![-14, 1, 0]] where
    su := ![![4917, 0, 0], ![-2442, 33, 0]]
    hsu := by decide
    w := ![![6765, -1320, 198], ![-4422, 1089, -198]]
    hw := by decide
    g := ![![![37911300823, -762297009365, 163603797415], ![-39183491521, -1799641770888, 153]], ![![-18583990146, 373675390015, -80198022629], ![19207613732, 882178248588, -75]]]
    h := ![![![-8875, 1087870, -44106], ![11730, 2190600, 0]], ![![6002, -727665, 29502], ![-7714, -1465268, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {33} * I149N1 =  Ideal.span {B.equivFun.symm ![205, -40, 6]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E149RS1 
