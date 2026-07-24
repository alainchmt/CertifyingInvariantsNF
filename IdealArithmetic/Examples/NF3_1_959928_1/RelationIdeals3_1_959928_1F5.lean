import IdealArithmetic.Examples.NF3_1_959928_1.PrimesBelow3_1_959928_1F5
import IdealArithmetic.Examples.NF3_1_959928_1.ClassGroupData3_1_959928_1

set_option linter.all false

noncomputable section


noncomputable def E263RS0 : RelationCertificate Table 500 ![![263, 0, 0], ![71, 1, 0]]
  ![-1523653009, -54414753, 32073507] ![![500, 0, 0], ![-142, 1, 0]] where
    su := ![![131500, 0, 0], ![35500, 500, 0]]
    hsu := by decide
    w := ![![-761826504500, -27207376500, 16036753500], ![224248810000, 7688355500, -4663267500]]
    hw := by decide
    g := ![![![-1069584568655, -129848825334, -60381011204], ![303502320177, 779202325622, 0]], ![![-338320628644, -51159050078, -18955756219], ![95980740815, 210695625049, 0]]]
    h := ![![![-36955346425825, -573570359917, -1474111315], ![136890909666746, 193861674676, 0]], ![![10878013316570, 168833710747, 433915125], ![-40294606390990, -57064502205, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N0 : Ideal.span {500} * I263N0 =  Ideal.span {B.equivFun.symm ![-1523653009, -54414753, 32073507]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E263RS0 


noncomputable def E263RS1 : RelationCertificate Table 2 ![![263, 0, 0], ![-51, 1, 0]]
  ![-19, -4, 1] ![![2, 0, 0], ![-31, -1, 1]] where
    su := ![![526, 0, 0], ![-102, 2, 0]]
    hsu := by decide
    w := ![![-38, -8, 2], ![-764, 30, 6]]
    hw := by decide
    g := ![![![9, 21, 6], ![-5, 0, 0]], ![![2, -3, -1], ![1, 0, 0]]]
    h := ![![![-455, 34, -1], ![-2346, 132, 0]], ![![-9266, 207, -1], ![-47776, 133, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {2} * I263N1 =  Ideal.span {B.equivFun.symm ![-19, -4, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E263RS1 


noncomputable def E263RS2 : RelationCertificate Table 10 ![![263, 0, 0], ![-21, 1, 0]]
  ![-244379, -73788, -12108] ![![10, 0, 0], ![-4, 2, 0]] where
    su := ![![2630, 0, 0], ![-210, 10, 0]]
    hsu := by decide
    w := ![![-2443790, -737880, -121080], ![-4979620, -1503550, -246720]]
    hw := by decide
    g := ![![![-4003, -353, -788], ![1533, 2372, 0]], ![![451, 49, 56], ![-170, -182, 0]]]
    h := ![![![-51535516, 2467667, -1438], ![-645409349, 183043, 0]], ![![-105012032, 5028273, -2930], ![-1315126974, 372959, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N2 : Ideal.span {10} * I263N2 =  Ideal.span {B.equivFun.symm ![-244379, -73788, -12108]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E263RS2 
