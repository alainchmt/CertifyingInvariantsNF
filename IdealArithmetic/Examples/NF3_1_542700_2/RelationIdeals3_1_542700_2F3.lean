import IdealArithmetic.Examples.NF3_1_542700_2.PrimesBelow3_1_542700_2F3
import IdealArithmetic.Examples.NF3_1_542700_2.ClassGroupData3_1_542700_2

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 77 ![![139, 0, 0], ![-47, 1, 0]]
  ![4351, 91, -135] ![![77, 0, 0], ![28, 1, 0]] where
    su := ![![10703, 0, 0], ![-3619, 77, 0]]
    hsu := by decide
    w := ![![335027, 7007, -10395], ![93478, 2849, -3234]]
    hw := by decide
    g := ![![![8061239, -1932643374, -414199551], ![-22167860, 5315561100, 0]], ![![-2657097, 637023230, 136525311], ![7306895, -1752074868, 0]]]
    h := ![![![20289816, -465756, 4347], ![60005959, -100728, 0]], ![![5661060, -129944, 1212], ![16742258, -28085, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {77} * I139N1 =  Ideal.span {B.equivFun.symm ![4351, 91, -135]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E139RS1 


noncomputable def E151RS0 : RelationCertificate Table 11 ![![151, 0, 0], ![4, 1, 0]]
  ![391, 80, 30] ![![11, 0, 0], ![-5, 1, 0]] where
    su := ![![1661, 0, 0], ![44, 11, 0]]
    hsu := by decide
    w := ![![4301, 880, 330], ![4345, 891, 330]]
    hw := by decide
    g := ![![![-26474, -775313, 936750], ![-58437, -1717380, 0]], ![![-3106, -90729, 109620], ![-6830, -200970, 0]]]
    h := ![![![385, 96, 0], ![-14436, 5, 0]], ![![389, 97, 0], ![-14586, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N0 : Ideal.span {11} * I151N0 =  Ideal.span {B.equivFun.symm ![391, 80, 30]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E151RS0 


noncomputable def E151RS1 : RelationCertificate Table 49 ![![151, 0, 0], ![33, 1, 0]]
  ![-271, -56, -22] ![![49, 0, 0], ![7, 1, 0]] where
    su := ![![7399, 0, 0], ![1617, 49, 0]]
    hsu := by decide
    w := ![![-13279, -2744, -1078], ![-6517, -1323, -490]]
    hw := by decide
    g := ![![![9, -9961, -8540], ![-190, 69749, 0]], ![![-1, -2212, -1896], ![-14, 15485, 0]]]
    h := ![![![-293188, -9500, -112], ![1341549, 2815, 0]], ![![-143920, -4680, -58], ![658539, 1458, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {49} * I151N1 =  Ideal.span {B.equivFun.symm ![-271, -56, -22]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E151RS1 


noncomputable def E151RS2 : RelationCertificate Table 847 ![![151, 0, 0], ![-37, 1, 0]]
  ![-439, -126, -50] ![![847, 0, 0], ![-49, 1, 0]] where
    su := ![![127897, 0, 0], ![-31339, 847, 0]]
    hsu := by decide
    w := ![![-371833, -106722, -42350], ![11011, 4235, 1694]]
    hw := by decide
    g := ![![![-66, -1519995, 186122], ![-1151, -26274222, 0]], ![![65, 361929, -44318], ![1126, 6256224, 0]]]
    h := ![![![-6868, 195, -2], ![-28017, 42, 0]], ![![214, 19, -4], ![873, 101, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N2 : Ideal.span {847} * I151N2 =  Ideal.span {B.equivFun.symm ![-439, -126, -50]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E151RS2 


noncomputable def E157RS0 : RelationCertificate Table 5929 ![![157, 0, 0], ![52, 1, 0]]
  ![2027, 84, -128] ![![5929, 0, 0], ![-2590, 1, 0]] where
    su := ![![930853, 0, 0], ![308308, 5929, 0]]
    hsu := by decide
    w := ![![12018083, 498036, -758912], ![-5276810, -219373, 332024]]
    hw := by decide
    g := ![![![-23349, -384784202, 891392], ![-53450, -880843856, 0]], ![![-7134, -128146290, 296864], ![-16331, -293351108, 0]]]
    h := ![![![259130039, 6169744, 136900], ![-782373348, -3582238, 0]], ![![-113777098, -2708995, -60112], ![343519298, 1572940, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N0 : Ideal.span {5929} * I157N0 =  Ideal.span {B.equivFun.symm ![2027, 84, -128]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E157RS0 


noncomputable def E157RS1 : RelationCertificate Table 11 ![![157, 0, 0], ![-32, 1, 0]]
  ![-3673, -753, -281] ![![11, 0, 0], ![-5, 1, 0]] where
    su := ![![1727, 0, 0], ![-352, 11, 0]]
    hsu := by decide
    w := ![![-40403, -8283, -3091], ![-40645, -8338, -3113]]
    hw := by decide
    g := ![![![111, 486, -571], ![-2, 1030, 0]], ![![-31, -100, 116], ![9, -208, 0]]]
    h := ![![![-50797, 1663, -17], ![-249108, 398, 0]], ![![-51067, 1650, -13], ![-250432, 293, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {11} * I157N1 =  Ideal.span {B.equivFun.symm ![-3673, -753, -281]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E157RS1 


noncomputable def E157RS2 : RelationCertificate Table 7 ![![157, 0, 0], ![-20, 1, 0]]
  ![-67, -14, -5] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![1099, 0, 0], ![-140, 7, 0]]
    hsu := by decide
    w := ![![-469, -98, -35], ![-1050, -217, -84]]
    hw := by decide
    g := ![![![59, 1, -1723], ![2, 2008, 0]], ![![-10, -1, 218], ![6, -254, 0]]]
    h := ![![![-531, 43, -5], ![-4165, 130, 0]], ![![-1190, 79, -6], ![-9334, 155, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N2 : Ideal.span {7} * I157N2 =  Ideal.span {B.equivFun.symm ![-67, -14, -5]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E157RS2 


noncomputable def E179RS1 : RelationCertificate Table 5929 ![![179, 0, 0], ![-59, 1, 0]]
  ![158849, 32592, 12167] ![![5929, 0, 0], ![-2590, 1, 0]] where
    su := ![![1061291, 0, 0], ![-349811, 5929, 0]]
    hsu := by decide
    w := ![![941815721, 193237968, 72138143], ![-408863840, -83889421, -31316978]]
    hw := by decide
    g := ![![![44911, 699852080, -1621279], ![102813, 1602093855, 0]], ![![-11871, -229308664, 531217], ![-27176, -524930925, 0]]]
    h := ![![![5997921, -109123, 847], ![18194390, -23241, 0]], ![![-2603694, 47393, -370], ![-7898174, 10158, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {5929} * I179N1 =  Ideal.span {B.equivFun.symm ![158849, 32592, 12167]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E179RS1 


noncomputable def E191RS1 : RelationCertificate Table 49 ![![191, 0, 0], ![32, 1, 0]]
  ![3551, 728, 272] ![![49, 0, 0], ![7, 1, 0]] where
    su := ![![9359, 0, 0], ![1568, 49, 0]]
    hsu := by decide
    w := ![![173999, 35672, 13328], ![81977, 16807, 6272]]
    hw := by decide
    g := ![![![64, 1147, 980], ![39, -8022, 0]], ![![2, 191, 164], ![50, -1342, 0]]]
    h := ![![![3489, 94, -2], ![-20714, 109, 0]], ![![1655, 39, -2], ![-9826, 85, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {49} * I191N1 =  Ideal.span {B.equivFun.symm ![3551, 728, 272]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E191RS1 
