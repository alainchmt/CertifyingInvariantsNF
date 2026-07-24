import IdealArithmetic.Examples.NF3_1_805315_1.PrimesBelow3_1_805315_1F1
import IdealArithmetic.Examples.NF3_1_805315_1.ClassGroupData3_1_805315_1

set_option linter.all false

noncomputable section


noncomputable def E47RS1 : RelationCertificate Table 2 ![![47, 0, 0], ![-6, 1, 0]]
  ![-65631713, 4049806, 2881397] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![94, 0, 0], ![-12, 2, 0]]
    hsu := by decide
    w := ![![-131263426, 8099612, 5762794], ![-633907340, 16215812, 20249030]]
    hw := by decide
    g := ![![![-137589512245513, 19902407290623, -8820112784704], ![9951203645313, 0, 0]], ![![58850252895914, -8512725157430, 3772568559027], ![-4256362578714, 3, 0]]]
    h := ![![![-96065443, 15987697, -62054], ![-741574018, 1159587, 0]], ![![-463804250, 76946798, -382115], ![-3580307680, 5616784, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {2} * I47N1 =  Ideal.span {B.equivFun.symm ![-65631713, 4049806, 2881397]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 4 ![![53, 0, 0], ![12, 1, 0]]
  ![-3854751337, -487743176, -70984145] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![212, 0, 0], ![48, 4, 0]]
    hsu := by decide
    w := ![![-15419005348, -1950972704, -283936580], ![15616511900, -6259066428, -2438715880]]
    hw := by decide
    g := ![![![726520809356889781, -123637271107015651, 46573284361479850], ![-30909317776753910, -31339, 0]], ![![-28827789570457951, 4905832274364589, -1847992272040650], ![1226458068591151, -9317, 0]]]
    h := ![![![-116562347453, -10493811978, -300239805], ![514495805306, 3168345104, 0]], ![![117202375483, 10520762429, 292173650], ![-517318481052, -3218976484, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {4} * I53N1 =  Ideal.span {B.equivFun.symm ![-3854751337, -487743176, -70984145]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS1 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![-27, 1, 0]]
  ![-15, 8, 3] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![122, 0, 0], ![-54, 2, 0]]
    hsu := by decide
    w := ![![-30, 16, 6], ![-660, 74, 40]]
    hw := by decide
    g := ![![![-381, -4902, -31007], ![-2451, 12393, 0]], ![![257, 2004, 12774], ![1002, -5103, 0]]]
    h := ![![![-816, 41, -2], ![-1843, 25, 0]], ![![-18276, 783, -20], ![-41278, 248, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![-15, 8, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E73RS1 : RelationCertificate Table 4 ![![73, 0, 0], ![21, 1, 0]]
  ![82693, -14952, 5301] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![292, 0, 0], ![84, 4, 0]]
    hsu := by decide
    w := ![![330772, -59808, 21204], ![-1166220, 210868, -74760]]
    hw := by decide
    g := ![![![-1295, -4, 217], ![0, -161, 0]], ![![-420, -12, 64], ![-3, -50, 0]]]
    h := ![![![154444, 7753, 222], ![-532939, -2181, 0]], ![![-544590, -27414, -800], ![1879215, 7942, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {4} * I73N1 =  Ideal.span {B.equivFun.symm ![82693, -14952, 5301]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E73RS1 


noncomputable def E79RS0 : RelationCertificate Table 2 ![![79, 0, 0], ![19, 1, 0]]
  ![-1561777, 282390, -100117] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![158, 0, 0], ![38, 2, 0]]
    hsu := by decide
    w := ![![-3123554, 564780, -200234], ![22025740, -3982546, 1411950]]
    hw := by decide
    g := ![![![11261, -7621, -42392], ![-3810, 16695, 0]], ![![4531, -2068, -11257], ![-1033, 4410, 0]]]
    h := ![![![-9178886, -508347, -8733], ![38082643, 117958, 0]], ![![64724784, 3584519, 61560], ![-268539214, -831453, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {2} * I79N0 =  Ideal.span {B.equivFun.symm ![-1561777, 282390, -100117]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0], ![21, 1, 0]]
  ![-123912357, 22404998, -7943345] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![158, 0, 0], ![42, 2, 0]]
    hsu := by decide
    w := ![![-247824714, 44809996, -15886690], ![1747535900, -315977674, 112024990]]
    hw := by decide
    g := ![![![65953, -9520, -10635], ![-4758, 2205, 0]], ![![31797, -3390, -3620], ![-1695, 630, 0]]]
    h := ![![![-4461067920, -228175137, -3760010], ![16776212063, 57819489, 0]], ![![31457218936, 1608976861, 26513700], ![-118297453714, -407713961, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![-123912357, 22404998, -7943345]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS1 


noncomputable def E79RS2 : RelationCertificate Table 2 ![![79, 0, 0], ![38, 1, 0]]
  ![-15, 2, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![158, 0, 0], ![76, 2, 0]]
    hsu := by decide
    w := ![![-30, 4, 2], ![-220, 14, 10]]
    hw := by decide
    g := ![![![-17, -15748, -98439], ![-7872, 39375, 0]], ![![-4, -7686, -48038], ![-3841, 19215, 0]]]
    h := ![![![-423, -19, -1], ![879, 16, 0]], ![![-2646, -109, -5], ![5498, 80, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {2} * I79N2 =  Ideal.span {B.equivFun.symm ![-15, 2, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS2 
