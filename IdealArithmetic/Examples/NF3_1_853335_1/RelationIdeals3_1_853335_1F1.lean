import IdealArithmetic.Examples.NF3_1_853335_1.PrimesBelow3_1_853335_1F1
import IdealArithmetic.Examples.NF3_1_853335_1.ClassGroupData3_1_853335_1

set_option linter.all false

noncomputable section


noncomputable def E43RS0 : RelationCertificate Table 160 ![![43, 0, 0], ![8, 1, 0]]
  ![564, 48, -61] ![![160, 0, 0], ![-17, 0, 1]] where
    su := ![![6880, 0, 0], ![1280, 160, 0]]
    hsu := by decide
    w := ![![90240, 7680, -9760], ![-6560, -1600, 1440]]
    hw := by decide
    g := ![![![5194680, -379404, 90999], ![-551303, -4669574, 0]], ![![906079, -66177, 15871], ![-96020, -814479, 0]]]
    h := ![![![13993972, 12041639, 29060873], ![2883571, -104134800, 0]], ![![-1011291, -870203, -2100117], ![-208381, 7525420, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {160} * I43N0 =  Ideal.span {B.equivFun.symm ![564, 48, -61]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 20 ![![43, 0, 0], ![-16, 1, 0]]
  ![-96, 8, -1] ![![20, 0, 0], ![3, 0, 1]] where
    su := ![![860, 0, 0], ![-320, 20, 0]]
    hsu := by decide
    w := ![![-1920, 160, -20], ![1060, 40, -80]]
    hw := by decide
    g := ![![![-4046403998, -160911994, -38517960], ![-608886481, 459748550, 0]], ![![1552770833, 61748518, 14780917], ![233654672, -176424337, 0]]]
    h := ![![![-78720, 290955, -184291], ![36087, 660376, 0]], ![![42819, -158226, 100220], ![-19598, -359122, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {20} * I43N1 =  Ideal.span {B.equivFun.symm ![-96, 8, -1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 2 ![![47, 0, 0], ![-11, 1, 0]]
  ![70, 8, -9] ![![2, 0, 0], ![-3, 0, 1]] where
    su := ![![94, 0, 0], ![-22, 2, 0]]
    hsu := by decide
    w := ![![140, 16, -18], ![402, -136, 76]]
    hw := by decide
    g := ![![![-766, -154, -590], ![859, 0, 0]], ![![40, -10, 18], ![-51, -3, 0]]]
    h := ![![![11179, -27747, 23841], ![-3175, -93378, 0]], ![![32949, -81810, 70294], ![-9408, -275315, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {2} * I47N1 =  Ideal.span {B.equivFun.symm ![70, 8, -9]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 80 ![![53, 0, 0], ![-5, 1, 0]]
  ![-2076, -112, 179] ![![80, 0, 0], ![-17, 0, 1]] where
    su := ![![4240, 0, 0], ![-400, 80, 0]]
    hsu := by decide
    w := ![![-166080, -8960, 14320], ![31600, 4320, -4560]]
    hw := by decide
    g := ![![![-267773136, 20211506, -5374575], ![56834683, 124378246, 0]], ![![27787883, -2097405, 557750], ![-5897927, -12907153, 0]]]
    h := ![![![-82788, 111392, -167369], ![9936, 739228, 0]], ![![15694, -21111, 31719], ![-1839, -140097, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {80} * I53N1 =  Ideal.span {B.equivFun.symm ![-2076, -112, 179]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E53RS1 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![5, 1, 0]]
  ![-62, 0, 3] ![![2, 0, 0], ![-3, 0, 1]] where
    su := ![![122, 0, 0], ![10, 2, 0]]
    hsu := by decide
    w := ![![-124, 0, 6], ![462, 48, -56]]
    hw := by decide
    g := ![![![181, 36, 137], ![-199, 0, 0]], ![![155, 13, 106], ![-179, -3, 0]]]
    h := ![![![-32046, -10712, -64545], ![-2776, 328104, 0]], ![![119136, 39825, 239972], ![10419, -1219860, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![-62, 0, 3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 4 ![![67, 0, 0], ![-23, 1, 0]]
  ![-792, 56, -1] ![![4, 0, 0], ![-1, 0, 1]] where
    su := ![![268, 0, 0], ![-92, 4, 0]]
    hsu := by decide
    w := ![![-3168, 224, -4], ![10780, 152, -628]]
    hw := by decide
    g := ![![![-113213, -3696, -10226], ![25749, 2010, 0]], ![![33502, 806, 2740], ![-7689, -705, 0]]]
    h := ![![![-525281, 2598903, -1201003], ![219155, 6705600, 0]], ![![1782748, -8820103, 4075937], ![-743589, -22757328, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {4} * I67N1 =  Ideal.span {B.equivFun.symm ![-792, 56, -1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E67RS1 


noncomputable def E73RS0 : RelationCertificate Table 10 ![![73, 0, 0], ![7, 1, 0]]
  ![-374, -28, -29] ![![10, 0, 0], ![-7, 0, 1]] where
    su := ![![730, 0, 0], ![70, 10, 0]]
    hsu := by decide
    w := ![![-3740, -280, -290], ![-5090, -380, -400]]
    hw := by decide
    g := ![![![-175392, 4338, -16450], ![121131, 14454, 0]], ![![-15615, 386, -1465], ![10791, 1287, 0]]]
    h := ![![![-462974, -311088, -935261], ![-48612, 5689502, 0]], ![![-630094, -423383, -1272868], ![-66187, 7743277, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {10} * I73N0 =  Ideal.span {B.equivFun.symm ![-374, -28, -29]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E73RS0 


noncomputable def E73RS1 : RelationCertificate Table 10 ![![73, 0, 0], ![24, 1, 0]]
  ![-1006, 28, 29] ![![10, 0, 0], ![-7, 0, 1]] where
    su := ![![730, 0, 0], ![240, 10, 0]]
    hsu := by decide
    w := ![![-10060, 280, 290], ![14750, 380, -980]]
    hw := by decide
    g := ![![![-21951880, 543207, -2058469], ![15160475, 1809408, 0]], ![![98736605147, -2441155310, 9260116915], ![-68189611906, -8137185043, 0]]]
    h := ![![![-77182, -303584, -173707], ![-29460, 1056720, 0]], ![![113027, 444774, 254494], ![43316, -1548180, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {10} * I73N1 =  Ideal.span {B.equivFun.symm ![-1006, 28, 29]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E73RS1 


noncomputable def E73RS2 : RelationCertificate Table 80 ![![73, 0, 0], ![-31, 1, 0]]
  ![-2649150876, -198548752, -206963581] ![![80, 0, 0], ![-17, 0, 1]] where
    su := ![![5840, 0, 0], ![-2480, 80, 0]]
    hsu := by decide
    w := ![![-211932070080, -15883900160, -16557086480], ![-9743859920, -730283520, -761234160]]
    hw := by decide
    g := ![![![-2921, 1007, -665], ![651, 3040, 0]], ![![-477548921293, 36045228078, -9585120961], ![101359331763, 221816789507, 0]]]
    h := ![![![-41567029885480, 287194816064132, -101467243927189], ![21585927979724, 617259049976768, 0]], ![![-1911099704429, 13204165166804, -4665092031243], ![992441863148, 28379309063776, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N2 : Ideal.span {80} * I73N2 =  Ideal.span {B.equivFun.symm ![-2649150876, -198548752, -206963581]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E73RS2 
