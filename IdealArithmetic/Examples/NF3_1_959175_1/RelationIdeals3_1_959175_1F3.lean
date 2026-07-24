import IdealArithmetic.Examples.NF3_1_959175_1.PrimesBelow3_1_959175_1F3
import IdealArithmetic.Examples.NF3_1_959175_1.ClassGroupData3_1_959175_1

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 2 ![![149, 0, 0], ![-36, 1, 0]]
  ![-12354, -566, 279] ![![2, 0, 0], ![-35, -2, 1]] where
    su := ![![298, 0, 0], ![-72, 2, 0]]
    hsu := by decide
    w := ![![-24708, -1132, 558], ![39550, 19008, -3944]]
    hw := by decide
    g := ![![![-16126, 473136, 147298], ![-116809, 0, 0]], ![![2589, -75340, -23461], ![18626, 3, 0]]]
    h := ![![![-386346, 10881, -7], ![-1598700, 661, 0]], ![![616711, -17260, -2], ![2551949, -837, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {2} * I149N1 =  Ideal.span {B.equivFun.symm ![-12354, -566, 279]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E149RS1 


noncomputable def E157RS1 : RelationCertificate Table 4 ![![157, 0, 0], ![-41, 1, 0]]
  ![-214700012, -25021109, 7542697] ![![4, 0, 0], ![35, 3, -1]] where
    su := ![![628, 0, 0], ![-164, 4, 0]]
    hsu := by decide
    w := ![![-858800048, -100084436, 30170788], ![7939230740, 22988764, -118844388]]
    hw := by decide
    g := ![![![-996891895151, 84929126952140, 30028230701721], ![47466983456117, 462, 0]], ![![182405349458, -15539826495570, -5494387047446], ![-8685226301909, -119, 0]]]
    h := ![![![-14450329380, 354181127, -48297], ![-55328951528, 7562663, 0]], ![![133690233678, -3278116210, 696945], ![511887362921, -69565731, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {4} * I157N1 =  Ideal.span {B.equivFun.symm ![-214700012, -25021109, 7542697]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E157RS1 


noncomputable def E163RS1 : RelationCertificate Table 2 ![![163, 0, 0], ![-57, 1, 0]]
  ![18, 6, 1] ![![2, 0, 0], ![-35, -2, 1]] where
    su := ![![326, 0, 0], ![-114, 2, 0]]
    hsu := by decide
    w := ![![36, 12, 2], ![210, 64, 8]]
    hw := by decide
    g := ![![![11, 6, -1], ![-3, 0, 0]], ![![26, -2, 4], ![-21, -3, 0]]]
    h := ![![![2064, -8, -1], ![5902, 82, 0]], ![![12135, -212, 0], ![34700, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {2} * I163N1 =  Ideal.span {B.equivFun.symm ![18, 6, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E163RS1 


noncomputable def E167RS1 : RelationCertificate Table 4 ![![167, 0, 0], ![-81, 1, 0]]
  ![-4947999076, -1439350091, -216882707] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![668, 0, 0], ![-324, 4, 0]]
    hsu := by decide
    w := ![![-19791996304, -5757400364, -867530828], ![-55779158884, -16225899840, -2444934768]]
    hw := by decide
    g := ![![![-1267292, -106408, -82761], ![290225, 216270, 0]], ![![654837, 53667, 38533], ![-150291, -102795, 0]]]
    h := ![![![-1003209628898, 12560396137, -5900617], ![-2068284691690, 384260166, 0]], ![![-2827314053156, 35398568213, -16629522], ![-5828981507251, 1082948241, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {4} * I167N1 =  Ideal.span {B.equivFun.symm ![-4947999076, -1439350091, -216882707]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E167RS1 


noncomputable def E173RS1 : RelationCertificate Table 4 ![![173, 0, 0], ![42, 1, 0]]
  ![-360812, 312319, -50194] ![![4, 0, 0], ![-69, -3, 2]] where
    su := ![![692, 0, 0], ![168, 4, 0]]
    hsu := by decide
    w := ![![-1443248, 1249276, -200776], ![270066268, 7462676, -5227936]]
    hw := by decide
    g := ![![![-2316927071, 109006935202, 32178891902], ![-25698763457, 0, 0]], ![![-726859816, 34197349377, 10095071536], ![-8062143850, 0, 0]]]
    h := ![![![-37501588, -966631, -3806], ![154462236, 304122, 0]], ![![7044770051, 181855932, 649274], ![-29016135768, -56815693, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {4} * I173N1 =  Ideal.span {B.equivFun.symm ![-360812, 312319, -50194]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E173RS1 


noncomputable def E179RS1 : RelationCertificate Table 2 ![![179, 0, 0], ![2, 1, 0]]
  ![2, 1, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![358, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![4, 2, 0], ![2, 4, 2]]
    hw := by decide
    g := ![![![-42, 8, 1], ![-17, 0, 0]], ![![0, -1, 0], ![2, 0, 0]]]
    h := ![![![2, 1, 0], ![-178, 0, 0]], ![![1, -1, -1], ![-89, 90, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {2} * I179N1 =  Ideal.span {B.equivFun.symm ![2, 1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E179RS1 


noncomputable def E191RS0 : RelationCertificate Table 2 ![![191, 0, 0], ![-94, 1, 0]]
  ![-134, -6, 3] ![![2, 0, 0], ![-35, -2, 1]] where
    su := ![![382, 0, 0], ![-188, 2, 0]]
    hsu := by decide
    w := ![![-268, -12, 6], ![490, 208, -44]]
    hw := by decide
    g := ![![![26, -54, -18], ![15, 0, 0]], ![![31, 27, 2], ![20, 3, 0]]]
    h := ![![![-6750, 119, -1], ![-13714, 97, 0]], ![![12521, -138, 0], ![25439, -11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N0 : Ideal.span {2} * I191N0 =  Ideal.span {B.equivFun.symm ![-134, -6, 3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E191RS0 


noncomputable def E191RS1 : RelationCertificate Table 2 ![![191, 0, 0], ![-66, 1, 0]]
  ![-19954, -1897, 625] ![![2, 0, 0], ![-35, -1, 1]] where
    su := ![![382, 0, 0], ![-132, 2, 0]]
    hsu := by decide
    w := ![![-39908, -3794, 1250], ![-182770, 28352, -2388]]
    hw := by decide
    g := ![![![-42984, -3208058, -1101171], ![1805689, 155652, 0]], ![![15749, 937961, 331805], ![-578624, -52647, 0]]]
    h := ![![![-1378586, 21535, -17], ![-3989242, 1936, 0]], ![![-6322153, 98644, -92], ![-18294543, 8189, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {2} * I191N1 =  Ideal.span {B.equivFun.symm ![-19954, -1897, 625]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E191RS1 


noncomputable def E191RS2 : RelationCertificate Table 4 ![![191, 0, 0], ![-31, 1, 0]]
  ![34761676, 4497535, -1300424] ![![4, 0, 0], ![-69, -3, 2]] where
    su := ![![764, 0, 0], ![-124, 4, 0]]
    hsu := by decide
    w := ![![139046704, 17990140, -5201696], ![1940657556, -53994436, -18473888]]
    hw := by decide
    g := ![![![282300405322, -13281687781769, -3920759671066], ![3131204009931, 0, 0]], ![![-27678632650, 1302226107492, 384417680096], ![-307004326299, 0, 0]]]
    h := ![![![1174363752, -38015951, 4036], ![7234474676, -1035650, 0]], ![![16404213922, -531417822, 126546], ![101055474023, -14394379, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N2 : Ideal.span {4} * I191N2 =  Ideal.span {B.equivFun.symm ![34761676, 4497535, -1300424]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E191RS2 


noncomputable def E193RS1 : RelationCertificate Table 4 ![![193, 0, 0], ![-48, 1, 0]]
  ![-137532145204612, -40007466184839, -6028364899293] ![![4, 0, 0], ![35, 3, -1]] where
    su := ![![772, 0, 0], ![-192, 4, 0]]
    hsu := by decide
    w := ![![-550128580818448, -160029864739356, -24113459597172], ![-363303237614660, -105683234796396, -15924455204108]]
    hw := by decide
    g := ![![![-462099, 8454090, -1712351], ![2725483, 1648458, 0]], ![![170924, -2508133, 494021], ![-508768, -398223, 0]]]
    h := ![![![-26479226967638884, 582075437190484, -1335363298363], ![-106465693179356250, 125848375842383, 0]], ![![-17486800763131697, 384400844167475, -881869851163], ![-70309619197396122, 83109883736716, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {4} * I193N1 =  Ideal.span {B.equivFun.symm ![-137532145204612, -40007466184839, -6028364899293]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E193RS1 
