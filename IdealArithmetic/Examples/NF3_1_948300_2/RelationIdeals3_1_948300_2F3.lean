import IdealArithmetic.Examples.NF3_1_948300_2.PrimesBelow3_1_948300_2F3
import IdealArithmetic.Examples.NF3_1_948300_2.ClassGroupData3_1_948300_2

set_option linter.all false

noncomputable section


noncomputable def E151RS1 : RelationCertificate Table 11 ![![151, 0, 0], ![-63, 1, 0]]
  ![-229957, -49915, -12772] ![![11, 0, 0], ![-1, 1, 0]] where
    su := ![![1661, 0, 0], ![-693, 11, 0]]
    hsu := by decide
    w := ![![-2529527, -549065, -140492], ![-2236212, -485397, -124201]]
    hw := by decide
    g := ![![![1696, -21, -1906], ![-155, 6915, 0]], ![![-728, 12, 781], ![76, -2835, 0]]]
    h := ![![![10752281, 668294171, -32336896], ![-60240, 1627619508, 0]], ![![9505512, 590801144, -28587224], ![-53189, 1438886511, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {11} * I151N1 =  Ideal.span {B.equivFun.symm ![-229957, -49915, -12772]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E151RS1 


noncomputable def E157RS1 : RelationCertificate Table 121 ![![157, 0, 0], ![-44, 1, 0]]
  ![-212790, 27267, -2269] ![![121, 0, 0], ![21, 1, 0]] where
    su := ![![18997, 0, 0], ![-5324, 121, 0]]
    hsu := by decide
    w := ![![-25747590, 3299307, -274549], ![-4942850, 341704, 36421]]
    hw := by decide
    g := ![![![-122564976, 2645837375, 360740261], ![594900, -14554728868, 0]], ![![33319270, -722076437, -98453220], ![-184812, 3971979072, 0]]]
    h := ![![![5362280, 231013466, -16117207], ![-31265, 843466410, 0]], ![![1028970, 44328597, -3092687], ![-5945, 161850720, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {121} * I157N1 =  Ideal.span {B.equivFun.symm ![-212790, 27267, -2269]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E157RS1 


noncomputable def E179RS0 : RelationCertificate Table 121 ![![179, 0, 0], ![33, 1, 0]]
  ![-122586576, 954825, 3201065] ![![121, 0, 0], ![21, 1, 0]] where
    su := ![![21659, 0, 0], ![3993, 121, 0]]
    hsu := by decide
    w := ![![-14832975696, 115533825, 387328865], ![-1944663116, -37559126, 66885775]]
    hw := by decide
    g := ![![![-7844323095467687112, 172334652065240834733, 23500250653999078021], ![62841876532391806, -947843442537485089592, 0]], ![![-1435204351762366343, 31530501986997381148, 4299626866237286374], ![11497608264361162, -173418283481023314353, 0]]]
    h := ![![![562062682698, -19091121125655, -1684512165617], ![-3033813354, 100509226948836, 0]], ![![73636144681, -2501138402365, -220688875243], ![-397461487, 13167769740424, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N0 : Ideal.span {121} * I179N0 =  Ideal.span {B.equivFun.symm ![-122586576, 954825, 3201065]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E179RS0 


noncomputable def E179RS1 : RelationCertificate Table 121 ![![179, 0, 0], ![71, 1, 0]]
  ![-37502, -1376, 1489] ![![121, 0, 0], ![21, 1, 0]] where
    su := ![![21659, 0, 0], ![8591, 121, 0]]
    hsu := by decide
    w := ![![-4537742, -166496, 180169], ![-492833, -37994, 25652]]
    hw := by decide
    g := ![![![-451713421, 9923284607, 1353178568], ![3614154, -54578260854, 0]], ![![-181025145, 3976746700, 542284963], ![1448105, -21872186934, 0]]]
    h := ![![![1021810, -73445676, -3060229], ![-4892, 182594160, 0]], ![![110843, -7971196, -332132], ![-390, 19817280, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {121} * I179N1 =  Ideal.span {B.equivFun.symm ![-37502, -1376, 1489]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E179RS1 


noncomputable def E179RS2 : RelationCertificate Table 121 ![![179, 0, 0], ![75, 1, 0]]
  ![138, -20, 3] ![![121, 0, 0], ![21, 1, 0]] where
    su := ![![21659, 0, 0], ![9075, 121, 0]]
    hsu := by decide
    w := ![![16698, -2420, 363], ![3509, -242, 0]]
    hw := by decide
    g := ![![![-225605433, 4956403783, 675875280], ![1807364, -27260302958, 0]], ![![-97056750, 2132273306, 290765418], ![777539, -11727538525, 0]]]
    h := ![![![-2149, 160739, 6345], ![83, -378584, 0]], ![![-518, 33743, 1332], ![177, -79476, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N2 : Ideal.span {121} * I179N2 =  Ideal.span {B.equivFun.symm ![138, -20, 3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E179RS2 


noncomputable def E181RS1 : RelationCertificate Table 121 ![![181, 0, 0], ![58, 1, 0]]
  ![70901613, -13024190, 1959618] ![![121, 0, 0], ![21, 1, 0]] where
    su := ![![21901, 0, 0], ![7018, 121, 0]]
    hsu := by decide
    w := ![![8579095173, -1575926990, 237113778], ![1888002809, -176438207, 119790]]
    hw := by decide
    g := ![![![-410934993890, -87568533469, -23002561338], ![-72043003245, -20415476736, 0]], ![![-156019778845, -33456916432, -8762244672], ![-27354316269, -6609060096, 0]]]
    h := ![![![-768844034, 45309923057, 2303909991], ![3961302, -139001916251, 0]], ![![-169051637, 9962648907, 506576028], ![871200, -30563420026, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {121} * I181N1 =  Ideal.span {B.equivFun.symm ![70901613, -13024190, 1959618]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E181RS1 


noncomputable def E193RS1 : RelationCertificate Table 11 ![![193, 0, 0], ![33, 1, 0]]
  ![-9776, -2122, -543] ![![11, 0, 0], ![-1, 1, 0]] where
    su := ![![2123, 0, 0], ![363, 11, 0]]
    hsu := by decide
    w := ![![-107536, -23342, -5973], ![-95073, -20636, -5280]]
    hw := by decide
    g := ![![![315, -15, -1428], ![-22, 5272, 0]], ![![68, -3, -255], ![2, 940, 0]]]
    h := ![![![12432928, -422358434, -37266951], ![-62360, 2397507000, 0]], ![![10991997, -373408776, -32947860], ![-55108, 2119645500, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {11} * I193N1 =  Ideal.span {B.equivFun.symm ![-9776, -2122, -543]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E193RS1 
