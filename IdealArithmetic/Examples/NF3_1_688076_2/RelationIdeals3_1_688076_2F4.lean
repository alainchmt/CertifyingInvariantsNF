import IdealArithmetic.Examples.NF3_1_688076_2.PrimesBelow3_1_688076_2F4
import IdealArithmetic.Examples.NF3_1_688076_2.ClassGroupData3_1_688076_2

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 11 ![![197, 0, 0], ![-83, 1, 0]]
  ![-16, 11, 3] ![![11, 0, 0], ![-1, 1, 0]] where
    su := ![![2167, 0, 0], ![-913, 11, 0]]
    hsu := by decide
    w := ![![-176, 121, 33], ![-495, 33, 22]]
    hw := by decide
    g := ![![![-1560342, 1560325, -3172223], ![283703, 17447220, 0]], ![![648013, -648005, 1317426], ![-117812, -7245840, 0]]]
    h := ![![![-399, 48180, -1161], ![431, 114360, 0]], ![![-1093, 135035, -3254], ![1268, 320520, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {11} * I197N1 =  Ideal.span {B.equivFun.symm ![-16, 11, 3]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E197RS1 


noncomputable def E211RS1 : RelationCertificate Table 7 ![![211, 0, 0], ![-39, 1, 0]]
  ![22, 7, 1] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![1477, 0, 0], ![-273, 7, 0]]
    hsu := by decide
    w := ![![154, 49, 7], ![-189, 35, 14]]
    hw := by decide
    g := ![![![-1044362, 1044345, -2173935], ![298393, 7608768, 0]], ![![190144, -190140, 395798], ![-54321, -1385292, 0]]]
    h := ![![![-16994, 710841, -36455], ![6673, 3846003, 0]], ![![20991, -876097, 44930], ![-7974, -4740114, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {7} * I211N1 =  Ideal.span {B.equivFun.symm ![22, 7, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E211RS1 


noncomputable def E223RS1 : RelationCertificate Table 539 ![![223, 0, 0], ![-60, 1, 0]]
  ![636, 77, -1] ![![539, 0, 0], ![153, 1, 0]] where
    su := ![![120197, 0, 0], ![-32340, 539, 0]]
    hsu := by decide
    w := ![![342804, 41503, -539], ![97559, 12397, 0]]
    hw := by decide
    g := ![![![10620469401, 1909728175362, 24963926039], ![6557810850, -6727778067522, 0]], ![![-2839257009, -510543242922, -6673810399], ![-1753152775, 1798591902534, 0]]]
    h := ![![![-7669159, 531954119, -17732469], ![4449120, 1977170293, 0]], ![![-2182040, 151354343, -5045334], ![1265994, 562554741, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {539} * I223N1 =  Ideal.span {B.equivFun.symm ![636, 77, -1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E223RS1 


noncomputable def E229RS1 : RelationCertificate Table 121 ![![229, 0, 0], ![108, 1, 0]]
  ![-232, -11, 5] ![![121, 0, 0], ![-45, 1, 0]] where
    su := ![![27709, 0, 0], ![13068, 121, 0]]
    hsu := by decide
    w := ![![-28072, -1331, 605], ![9559, 363, -242]]
    hw := by decide
    g := ![![![1108, -65039, 2891], ![-909, -174902, 0]], ![![559, -31384, 1395], ![-373, -84396, 0]]]
    h := ![![![7220, 1232078, 22817], ![8879, -2612544, 0]], ![![-2533, -419567, -7770], ![-2866, 889664, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {121} * I229N1 =  Ideal.span {B.equivFun.symm ![-232, -11, 5]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E229RS1 
