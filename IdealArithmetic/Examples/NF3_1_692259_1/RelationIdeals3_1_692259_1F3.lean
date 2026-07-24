import IdealArithmetic.Examples.NF3_1_692259_1.PrimesBelow3_1_692259_1F3
import IdealArithmetic.Examples.NF3_1_692259_1.ClassGroupData3_1_692259_1

set_option linter.all false

noncomputable section


noncomputable def E151RS0 : RelationCertificate Table 4 ![![151, 0, 0], ![8, 1, 0]]
  ![1162172, 178734, -165831] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![604, 0, 0], ![32, 4, 0]]
    hsu := by decide
    w := ![![4648688, 714936, -663324], ![-24554536, 3815468, 204540]]
    hw := by decide
    g := ![![![-1087187147419, 1895097450, 84372334260], ![-271323012489, -168269872869, 0]], ![![-97339011666, 83633981, 2883057186], ![-24313844421, -8914960138, 0]]]
    h := ![![![-83366842, 583830651, 250209969], ![-550217, -12593957050, 0]], ![![447571339, -3134393052, -1343305290], ![2954894, 67613049975, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N0 : Ideal.span {4} * I151N0 =  Ideal.span {B.equivFun.symm ![1162172, 178734, -165831]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E151RS0 


noncomputable def E151RS1 : RelationCertificate Table 2 ![![151, 0, 0], ![27, 1, 0]]
  ![10, -4, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![302, 0, 0], ![54, 2, 0]]
    hsu := by decide
    w := ![![20, -8, 2], ![168, -6, -10]]
    hw := by decide
    g := ![![![441, -74, -668], ![185, 453, 0]], ![![88, -15, -119], ![38, 81, 0]]]
    h := ![![![-42, 684, 79], ![88, -3976, 0]], ![![-243, 5676, 655], ![141, -32970, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {2} * I151N1 =  Ideal.span {B.equivFun.symm ![10, -4, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E151RS1 


noncomputable def E167RS1 : RelationCertificate Table 2 ![![167, 0, 0], ![-59, 1, 0]]
  ![-326136, 66168, -4015] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![334, 0, 0], ![-118, 2, 0]]
    hsu := by decide
    w := ![![-652272, 132336, -8030], ![-1010614, -261896, 190474]]
    hw := by decide
    g := ![![![63272933311, -9012835164, 2887942798], ![27130049075, 0, 0]], ![![-20183375317, 2874996072, -921222245], ![-8654189621, 3, 0]]]
    h := ![![![3818770, 228799810, -11440001], ![20938, 636825384, 0]], ![![5898489, 353404888, -17669723], ![32316, 983646326, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {2} * I167N1 =  Ideal.span {B.equivFun.symm ![-326136, 66168, -4015]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E167RS1 


noncomputable def E181RS1 : RelationCertificate Table 2 ![![181, 0, 0], ![67, 1, 0]]
  ![-245565754, -14548302, -9229551] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![362, 0, 0], ![134, 2, 0]]
    hsu := by decide
    w := ![![-491131508, -29096604, -18459102], ![-1652368306, -97892938, -62104008]]
    hw := by decide
    g := ![![![-9881, -3691, 3291], ![-6784, 543, 0]], ![![-649, -2287, 1128], ![-1467, 198, 0]]]
    h := ![![![-61919270269, 4093958108295, 186088881783], ![-301839669, -11227365610758, 0]], ![![-208321881246, 13773758176881, 626079502839], ![-1015512944, -37773473688621, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {2} * I181N1 =  Ideal.span {B.equivFun.symm ![-245565754, -14548302, -9229551]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E181RS1 


noncomputable def E191RS1 : RelationCertificate Table 4 ![![191, 0, 0], ![77, 1, 0]]
  ![-4, -2, 1] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![764, 0, 0], ![308, 4, 0]]
    hsu := by decide
    w := ![![-16, -8, 4], ![152, -20, -4]]
    hw := by decide
    g := ![![![590593, -34743, -1876147], ![138963, 2501527, 0]], ![![238087, -14007, -756342], ![56024, 1008455, 0]]]
    h := ![![![-1986, 147870, 5837], ![100, -371622, 0]], ![![18541, -1411675, -55724], ![84, 3547761, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {4} * I191N1 =  Ideal.span {B.equivFun.symm ![-4, -2, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E191RS1 
