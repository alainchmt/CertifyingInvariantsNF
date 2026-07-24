import IdealArithmetic.Examples.NF3_1_977075_1.PrimesBelow3_1_977075_1F5
import IdealArithmetic.Examples.NF3_1_977075_1.ClassGroupData3_1_977075_1

set_option linter.all false

noncomputable section


noncomputable def E263RS0 : RelationCertificate Table 256 ![![263, 0, 0], ![61, 1, 0]]
  ![10271, -561, -163] ![![256, 0, 0], ![-28, 1, 0]] where
    su := ![![67328, 0, 0], ![15616, 256, 0]]
    hsu := by decide
    w := ![![2629376, -143616, -41728], ![-233472, 14080, 3840]]
    hw := by decide
    g := ![![![30748997, 72830994817, -2601146177], ![281133025, 665893421862, 0]], ![![7307207, 17307588224, -618137471], ![66808621, 158243192683, 0]]]
    h := ![![![145300, 2478, 1], ![-626289, -426, 0]], ![![-12980, -277, -1], ![55948, 278, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N0 : Ideal.span {256} * I263N0 =  Ideal.span {B.equivFun.symm ![10271, -561, -163]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E263RS0 


noncomputable def E263RS1 : RelationCertificate Table 2 ![![263, 0, 0], ![82, 1, 0]]
  ![1599, -123, -29] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![526, 0, 0], ![164, 2, 0]]
    hsu := by decide
    w := ![![3198, -246, -58], ![9628, -518, -152]]
    hw := by decide
    g := ![![![-30981, 7967, 153053], ![3985, -307943, 0]], ![![-8500, 2186, 48094], ![1093, -96692, 0]]]
    h := ![![![136407, 1836, 2], ![-437481, -555, 0]], ![![411026, 5691, 8], ![-1318232, -2180, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {2} * I263N1 =  Ideal.span {B.equivFun.symm ![1599, -123, -29]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E263RS1 


noncomputable def E271RS0 : RelationCertificate Table 8 ![![271, 0, 0], ![-125, 1, 0]]
  ![-89, 31, -3] ![![8, 0, 0], ![4, 1, 0]] where
    su := ![![2168, 0, 0], ![-1000, 8, 0]]
    hsu := by decide
    w := ![![-712, 248, -24], ![640, -184, 16]]
    hw := by decide
    g := ![![![623905, -12478388, -3158593], ![-1247845, 25268751, 0]], ![![-286475, 5729610, 1450308], ![572964, -11602467, 0]]]
    h := ![![![-91534, 981, -2], ![-198445, 539, 0]], ![![82730, -661, 0], ![179358, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R271N0 : Ideal.span {8} * I271N0 =  Ideal.span {B.equivFun.symm ![-89, 31, -3]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E271RS0 


noncomputable def E271RS1 : RelationCertificate Table 32 ![![271, 0, 0], ![-75, 1, 0]]
  ![-55417, 17815, -1643] ![![32, 0, 0], ![4, 1, 0]] where
    su := ![![8672, 0, 0], ![-2400, 32, 0]]
    hsu := by decide
    w := ![![-1773344, 570080, -52576], ![323808, -104096, 9600]]
    hw := by decide
    g := ![![![143811, -37511025, -9386770], ![-1154238, 300376819, 0]], ![![-40340, 10519692, 2632451], ![323703, -84238480, 0]]]
    h := ![![![-159257977, 2248073, -1667], ![-575451418, 450114, 0]], ![![29080239, -410465, 304], ![105076462, -82084, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R271N1 : Ideal.span {32} * I271N1 =  Ideal.span {B.equivFun.symm ![-55417, 17815, -1643]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E271RS1 


noncomputable def E271RS2 : RelationCertificate Table 2 ![![271, 0, 0], ![-72, 1, 0]]
  ![-103, 33, -3] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![542, 0, 0], ![-144, 2, 0]]
    hsu := by decide
    w := ![![-206, 66, -6], ![996, -322, 30]]
    hw := by decide
    g := ![![![389, -16, -129966], ![-7, 259920, 0]], ![![-96, 4, 34116], ![2, -68229, 0]]]
    h := ![![![-2281, 103, -1], ![-8584, 268, 0]], ![![11694, -159, 0], ![44008, 15, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R271N2 : Ideal.span {2} * I271N2 =  Ideal.span {B.equivFun.symm ![-103, 33, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E271RS2 


noncomputable def E277RS1 : RelationCertificate Table 8 ![![277, 0, 0], ![-45, 1, 0]]
  ![113, 41, 3] ![![8, 0, 0], ![4, 1, 0]] where
    su := ![![2216, 0, 0], ![-360, 8, 0]]
    hsu := by decide
    w := ![![904, 328, 24], ![-544, 496, 56]]
    hw := by decide
    g := ![![![928217, -18557544, -4697326], ![-1855580, 37578709, 0]], ![![-154157, 3081763, 780061], ![308145, -6240508, 0]]]
    h := ![![![42869, -952, 0], ![263880, 3, 0]], ![![-25724, 618, -1], ![-158344, 284, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R277N1 : Ideal.span {8} * I277N1 =  Ideal.span {B.equivFun.symm ![113, 41, 3]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E277RS1 
