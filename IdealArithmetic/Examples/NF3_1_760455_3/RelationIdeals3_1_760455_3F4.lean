import IdealArithmetic.Examples.NF3_1_760455_3.PrimesBelow3_1_760455_3F4
import IdealArithmetic.Examples.NF3_1_760455_3.ClassGroupData3_1_760455_3

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 5 ![![197, 0, 0], ![-75, 1, 0]]
  ![-16, 13, 1] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![985, 0, 0], ![-375, 5, 0]]
    hsu := by decide
    w := ![![-80, 65, 5], ![95, -85, 90]]
    hw := by decide
    g := ![![![4089, -4913, 12737], ![-2613, -9062, 0]], ![![-1554, 1883, -4881], ![1001, 3473, 0]]]
    h := ![![![2817, -131938, 12153], ![-1721, -342020, 0]], ![![-3278, 157266, -14486], ![2261, 407680, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {5} * I197N1 =  Ideal.span {B.equivFun.symm ![-16, 13, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E197RS1 


noncomputable def E233RS1 : RelationCertificate Table 5 ![![233, 0, 0], ![-20, 1, 0]]
  ![-6286, -7, -209] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![1165, 0, 0], ![-100, 5, 0]]
    hsu := by decide
    w := ![![-31430, -35, -1045], ![4825, 5, 160]]
    hw := by decide
    g := ![![![8915, -16098, 40764], ![-6781, -29115, 0]], ![![7145, -12890, 32609], ![-5435, -23292, 0]]]
    h := ![![![-12106686, 128547030, -42851287], ![1590989, 1426335666, 0]], ![![1858581, -19734002, 6578350], ![-244087, -218965074, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {5} * I233N1 =  Ideal.span {B.equivFun.symm ![-6286, -7, -209]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E233RS1 


noncomputable def E239RS1 : RelationCertificate Table 5 ![![239, 0, 0], ![-66, 1, 0]]
  ![-17991307128, -19869941, -598231582] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![1195, 0, 0], ![-330, 5, 0]]
    hsu := by decide
    w := ![![-89956535640, -99349705, -2991157910], ![13808305840, 15250155, 459141995]]
    hw := by decide
    g := ![![![29461, -28685, 10475], ![-17516, -10994, 0]], ![![-8929, 8698, -3695], ![5315, 3059, 0]]]
    h := ![![![-621327725798, 23300006453292, -2434449166566], ![269069608323, 83118964653956, 0]], ![![95373651376, -3576545193655, 373687341389], ![-41302117756, -12758740394796, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {5} * I239N1 =  Ideal.span {B.equivFun.symm ![-17991307128, -19869941, -598231582]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E239RS1 
