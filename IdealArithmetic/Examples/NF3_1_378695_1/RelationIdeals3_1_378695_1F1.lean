import IdealArithmetic.Examples.NF3_1_378695_1.PrimesBelow3_1_378695_1F1
import IdealArithmetic.Examples.NF3_1_378695_1.ClassGroupData3_1_378695_1

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 1 ![![41, 0, 0], ![3, 1, 0]]
  ![1, 0, 0] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![41, 0, 0], ![3, 1, 0]]
    hsu := by decide
    w := ![![41, 0, 0], ![3, 1, 0]]
    hw := by decide
    g := ![![![37, 12, 0], ![-492, 0, 0]], ![![-3, -1, 0], ![42, 0, 0]]]
    h := ![![![37, 12, 0], ![-492, 0, 0]], ![![-3, -1, 0], ![42, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {1} * I41N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E47RS1 : RelationCertificate Table 41 ![![47, 0, 0], ![16, 1, 0]]
  ![702, 3, -11] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![1927, 0, 0], ![656, 41, 0]]
    hsu := by decide
    w := ![![28782, 123, -451], ![4141, 205, -41]]
    hw := by decide
    g := ![![![-8616, 4835295, 1612714], ![117344, -66121326, 0]], ![![-2941, 1652201, 551059], ![40123, -22593428, 0]]]
    h := ![![![674, 45, 0], ![-1936, -11, 0]], ![![91, 6, 0], ![-261, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {41} * I47N1 =  Ideal.span {B.equivFun.symm ![702, 3, -11]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 


noncomputable def E53RS0 : RelationCertificate Table 41 ![![53, 0, 0], ![2, 1, 0]]
  ![-3647, -48, 53] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![2173, 0, 0], ![82, 41, 0]]
    hsu := by decide
    w := ![![-149527, -1968, 2173], ![-20746, -1353, 164]]
    hw := by decide
    g := ![![![889, -404, 16], ![74, 901, 0]], ![![-101, 34, -5], ![30, 33, 0]]]
    h := ![![![-284213, -142285, -105], ![7529821, 5618, 0]], ![![-39438, -19745, -15], ![1044854, 799, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {41} * I53N0 =  Ideal.span {B.equivFun.symm ![-3647, -48, 53]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS0 


noncomputable def E53RS2 : RelationCertificate Table 41 ![![53, 0, 0], ![-8, 1, 0]]
  ![2933, -200, -73] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![2173, 0, 0], ![-328, 41, 0]]
    hsu := by decide
    w := ![![120253, -8200, -2993], ![22304, -1025, -492]]
    hw := by decide
    g := ![![![325, 357, 175], ![72, -6600, 0]], ![![-101, -17, -22], ![30, 730, 0]]]
    h := ![![![10545, -1334, 1], ![69494, -126, 0]], ![![1968, -247, 0], ![12970, -12, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {41} * I53N2 =  Ideal.span {B.equivFun.symm ![2933, -200, -73]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS2 


noncomputable def E61RS1 : RelationCertificate Table 41 ![![61, 0, 0], ![19, 1, 0]]
  ![54, -25, -4] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![2501, 0, 0], ![779, 41, 0]]
    hsu := by decide
    w := ![![2214, -1025, -164], ![902, -205, -41]]
    hw := by decide
    g := ![![![-31506, 17747885, 5919463], ![430610, -242697978, 0]], ![![-9905, 5578549, 1860617], ![135372, -76285296, 0]]]
    h := ![![![24096, 1459, 10], ![-77358, -614, 0]], ![![9838, 594, 4], ![-31584, -245, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {41} * I61N1 =  Ideal.span {B.equivFun.symm ![54, -25, -4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E73RS1 : RelationCertificate Table 41 ![![73, 0, 0], ![16, 1, 0]]
  ![4377, -1646, 186] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![2993, 0, 0], ![656, 41, 0]]
    hsu := by decide
    w := ![![179457, -67486, 7626], ![-21279, 7995, -902]]
    hw := by decide
    g := ![![![44, 4263, 1422], ![115, -58360, 0]], ![![12, 971, 324], ![42, -13300, 0]]]
    h := ![![![25041, 1626, 8], ![-113976, -398, 0]], ![![-2991, -195, -1], ![13614, 51, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {41} * I73N1 =  Ideal.span {B.equivFun.symm ![4377, -1646, 186]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 
