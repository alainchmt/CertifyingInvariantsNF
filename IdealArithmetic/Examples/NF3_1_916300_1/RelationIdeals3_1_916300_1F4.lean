import IdealArithmetic.Examples.NF3_1_916300_1.PrimesBelow3_1_916300_1F4
import IdealArithmetic.Examples.NF3_1_916300_1.ClassGroupData3_1_916300_1

set_option linter.all false

noncomputable section


noncomputable def E199RS1 : RelationCertificate Table 99 ![![199, 0, 0], ![23, 1, 0]]
  ![-188, -5, -4] ![![99, 0, 0], ![-18, 7, 1]] where
    su := ![![19701, 0, 0], ![2277, 99, 0]]
    hsu := by decide
    w := ![![-18612, -495, -396], ![-2277, -99, 0]]
    hw := by decide
    g := ![![![-84176168, 35877415, -4750262], ![17793573, 56560295, 0]], ![![-11874375, 5061075, -670100], ![2510099, 7978725, 0]]]
    h := ![![![-586, -48, -1], ![5062, 195, 0]], ![![-69, -26, -1], ![596, 199, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {99} * I199N1 =  Ideal.span {B.equivFun.symm ![-188, -5, -4]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E199RS1 


noncomputable def E223RS0 : RelationCertificate Table 33 ![![223, 0, 0], ![98, 1, 0]]
  ![141497, 5144, 2692] ![![33, 0, 0], ![15, 7, 1]] where
    su := ![![7359, 0, 0], ![3234, 33, 0]]
    hsu := by decide
    w := ![![4669401, 169752, 88836], ![6204495, 225555, 118041]]
    hw := by decide
    g := ![![![9053956, -2968643, 450551], ![3499405, -2295904, 0]], ![![4004640, -1313057, 199282], ![1547818, -1015496, 0]]]
    h := ![![![3210131, 39528, 81], ![-7303242, -15371, 0]], ![![4265441, 52461, 107], ![-9704136, -20284, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N0 : Ideal.span {33} * I223N0 =  Ideal.span {B.equivFun.symm ![141497, 5144, 2692]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E223RS0 


noncomputable def E223RS2 : RelationCertificate Table 99 ![![223, 0, 0], ![-27, 1, 0]]
  ![4462, -1268, -91] ![![99, 0, 0], ![9, 1, 0]] where
    su := ![![22077, 0, 0], ![-2673, 99, 0]]
    hsu := by decide
    w := ![![441738, -125532, -9009], ![26235, -2673, -2178]]
    hw := by decide
    g := ![![![13395, 533, 263], ![1225, -598, 0]], ![![-1448, 36, -18], ![-121, -966, 0]]]
    h := ![![![12333358, -463152, 235], ![101864236, -52496, 0]], ![![732355, -27478, 13], ![6048700, -2921, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N2 : Ideal.span {99} * I223N2 =  Ideal.span {B.equivFun.symm ![4462, -1268, -91]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E223RS2 


noncomputable def E229RS0 : RelationCertificate Table 9 ![![229, 0, 0], ![6, 1, 0]]
  ![-178606, -6493, -3398] ![![9, 0, 0], ![0, 1, 0]] where
    su := ![![2061, 0, 0], ![54, 9, 0]]
    hsu := by decide
    w := ![![-1607454, -58437, -30582], ![-519894, -18900, -9891]]
    hw := by decide
    g := ![![![287, -96, -2215098], ![-3, 19935875, 0]], ![![7, -2, -76241], ![8, 686165, 0]]]
    h := ![![![-9054286, -1510033, -196], ![345542148, 41486, 0]], ![![-2928406, -488390, -64], ![111757868, 13557, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N0 : Ideal.span {9} * I229N0 =  Ideal.span {B.equivFun.symm ![-178606, -6493, -3398]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E229RS0 


noncomputable def E229RS1 : RelationCertificate Table 11 ![![229, 0, 0], ![93, 1, 0]]
  ![-454, 57, 34] ![![11, 0, 0], ![26, -4, 1]] where
    su := ![![2519, 0, 0], ![1023, 11, 0]]
    hsu := by decide
    w := ![![-4994, 627, 374], ![-18689, 10615, -1441]]
    hw := by decide
    g := ![![![-62177, -58557, 4570], ![-125225, 0, 0]], ![![-26042, -24525, 1914], ![-52447, 0, 0]]]
    h := ![![![-183346, -2729, -8], ![451460, 1866, 0]], ![![-683968, -9994, -29], ![1684161, 6510, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {11} * I229N1 =  Ideal.span {B.equivFun.symm ![-454, 57, 34]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E229RS1 


noncomputable def E229RS2 : RelationCertificate Table 33 ![![229, 0, 0], ![-100, 1, 0]]
  ![-910, 170, 49] ![![33, 0, 0], ![9, 1, 0]] where
    su := ![![7557, 0, 0], ![-3300, 33, 0]]
    hsu := by decide
    w := ![![-30030, 5610, 1617], ![-693, -1683, 660]]
    hw := by decide
    g := ![![![-148683462784, 19328851298684, 2149485742861], ![545172731326, -70933029508514, 0]], ![![65576545219, -8524951361173, -948026404995], ![-240447347076, 31284871362334, 0]]]
    h := ![![![-42390, 546, -1], ![-97064, 278, 0]], ![![-949, 18, 0], ![-2173, 20, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N2 : Ideal.span {33} * I229N2 =  Ideal.span {B.equivFun.symm ![-910, 170, 49]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E229RS2 
