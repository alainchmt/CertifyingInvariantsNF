import IdealArithmetic.Examples.NF3_1_557179_1.PrimesBelow3_1_557179_1F3
import IdealArithmetic.Examples.NF3_1_557179_1.ClassGroupData3_1_557179_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 24 ![![139, 0, 0], ![17, 1, 0]]
  ![-573, 52, -43] ![![24, 0, 0], ![0, 2, 0]] where
    su := ![![3336, 0, 0], ![408, 24, 0]]
    hsu := by decide
    w := ![![-13752, 1248, -1032], ![12384, -1128, 936]]
    hw := by decide
    g := ![![![-23, -47, -385], ![0, 511, 0]], ![![-1, -7, -50], ![9, 66, 0]]]
    h := ![![![-192342, -11537, -112], ![1572645, 1725, 0]], ![![173164, 10371, 93], ![-1415840, -1432, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {24} * I139N1 =  Ideal.span {B.equivFun.symm ![-573, 52, -43]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E139RS1 


noncomputable def E163RS0 : RelationCertificate Table 6 ![![163, 0, 0], ![31, 1, 0]]
  ![451, -41, 34] ![![6, 0, 0], ![0, 2, 0]] where
    su := ![![978, 0, 0], ![186, 6, 0]]
    hsu := by decide
    w := ![![2706, -246, 204], ![-9792, 888, -738]]
    hw := by decide
    g := ![![![-175, -2, 11], ![1, 0, 0]], ![![-43, -2, 2], ![2, 0, 0]]]
    h := ![![![55930, 1892, 25], ![-294069, -449, 0]], ![![-202572, -6904, -105], ![1065084, 1888, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N0 : Ideal.span {6} * I163N0 =  Ideal.span {B.equivFun.symm ![451, -41, 34]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E163RS0 


noncomputable def E163RS1 : RelationCertificate Table 16 ![![163, 0, 0], ![51, 1, 0]]
  ![-223, -64, -33] ![![16, 0, 0], ![0, 1, 0]] where
    su := ![![2608, 0, 0], ![816, 16, 0]]
    hsu := by decide
    w := ![![-3568, -1024, -528], ![4752, -320, -576]]
    hw := by decide
    g := ![![![1364, 1067491, 9646170], ![66727, -17148564, 0]], ![![336, 2165452844, 19565205102], ![135340811, -34782586803, 0]]]
    h := ![![![8867, 140, -6], ![-28344, 105, 0]], ![![-12195, -238, 0], ![38982, -4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {16} * I163N1 =  Ideal.span {B.equivFun.symm ![-223, -64, -33]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E163RS1 


noncomputable def E163RS2 : RelationCertificate Table 6 ![![163, 0, 0], ![80, 1, 0]]
  ![15, -1, 1] ![![6, 0, 0], ![0, 2, 0]] where
    su := ![![978, 0, 0], ![480, 6, 0]]
    hsu := by decide
    w := ![![90, -6, 6], ![-288, 30, -18]]
    hw := by decide
    g := ![![![29, -1, -2], ![2, 0, 0]], ![![16, 0, -1], ![0, 0, 0]]]
    h := ![![![2965, 46, 1], ![-6041, -18, 0]], ![![-9616, -228, -12], ![19592, 217, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N2 : Ideal.span {6} * I163N2 =  Ideal.span {B.equivFun.symm ![15, -1, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E163RS2 


noncomputable def E179RS0 : RelationCertificate Table 12 ![![179, 0, 0], ![24, 1, 0]]
  ![-7, 0, 1] ![![12, 0, 0], ![0, 2, 0]] where
    su := ![![2148, 0, 0], ![288, 12, 0]]
    hsu := by decide
    w := ![![-84, 0, 12], ![-288, -12, 0]]
    hw := by decide
    g := ![![![3, -35523, -328567], ![-5915, 219045, 0]], ![![0, -5573, -51540], ![-923, 34360, 0]]]
    h := ![![![-1949, -84, -1], ![14536, 20, 0]], ![![-6648, -302, -9], ![49582, 179, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N0 : Ideal.span {12} * I179N0 =  Ideal.span {B.equivFun.symm ![-7, 0, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E179RS0 


noncomputable def E179RS1 : RelationCertificate Table 96 ![![179, 0, 0], ![31, 1, 0]]
  ![267, -32, -43] ![![96, 0, 0], ![0, 2, 0]] where
    su := ![![17184, 0, 0], ![2976, 96, 0]]
    hsu := by decide
    w := ![![25632, -3072, -4128], ![12384, 384, -576]]
    hw := by decide
    g := ![![![302, 29, 532], ![9, -2716, 0]], ![![34, 286, 2612], ![41, -13917, 0]]]
    h := ![![![2247, 66, -2], ![-12966, 35, 0]], ![![1071, 24, -3], ![-6180, 59, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {96} * I179N1 =  Ideal.span {B.equivFun.symm ![267, -32, -43]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E179RS1 


noncomputable def E179RS2 : RelationCertificate Table 32 ![![179, 0, 0], ![-56, 1, 0]]
  ![99, -16, -19] ![![32, 0, 0], ![16, 1, 0]] where
    su := ![![5728, 0, 0], ![-1792, 32, 0]]
    hsu := by decide
    w := ![![3168, -512, -608], ![4320, -192, -448]]
    hw := by decide
    g := ![![![-98, 9916, 5260], ![287, -18690, 0]], ![![-91442, 7314182, 3875237], ![182850, -13778625, 0]]]
    h := ![![![90897, -1575, -8], ![290544, 157, 0]], ![![123757, -2186, -4], ![395578, 78, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N2 : Ideal.span {32} * I179N2 =  Ideal.span {B.equivFun.symm ![99, -16, -19]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E179RS2 


noncomputable def E191RS1 : RelationCertificate Table 2 ![![191, 0, 0], ![-60, 1, 0]]
  ![-165, -6, 7] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![382, 0, 0], ![-120, 2, 0]]
    hsu := by decide
    w := ![![-330, -12, 14], ![-1008, -164, -54]]
    hw := by decide
    g := ![![![4885, -355, 368], ![-177, 0, 0]], ![![-1812, 130, -150], ![66, 3, 0]]]
    h := ![![![-18255, 370, -10], ![-58109, 213, 0]], ![![-55944, 1049, -18], ![-178080, 379, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {2} * I191N1 =  Ideal.span {B.equivFun.symm ![-165, -6, 7]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E191RS1 


noncomputable def E193RS0 : RelationCertificate Table 96 ![![193, 0, 0], ![48, 1, 0]]
  ![-3169, 288, -239] ![![96, 0, 0], ![0, 2, 0]] where
    su := ![![18528, 0, 0], ![4608, 96, 0]]
    hsu := by decide
    w := ![![-304224, 27648, -22944], ![68832, -6240, 5184]]
    hw := by decide
    g := ![![![33, -18167775, -163580954], ![-378470, 872431749, 0]], ![![9, -4524968, -40742385], ![-94227, 217292719, 0]]]
    h := ![![![-7781569, -180526, -3383], ![31288326, 72520, 0]], ![![1760589, 40793, 756], ![-7079020, -16206, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N0 : Ideal.span {96} * I193N0 =  Ideal.span {B.equivFun.symm ![-3169, 288, -239]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E193RS0 


noncomputable def E193RS1 : RelationCertificate Table 96 ![![193, 0, 0], ![-44, 1, 0]]
  ![-1139, -80, 19] ![![96, 0, 0], ![0, 2, 0]] where
    su := ![![18528, 0, 0], ![-4224, 96, 0]]
    hsu := by decide
    w := ![![-109344, -7680, 1824], ![-5472, -2400, -1440]]
    hw := by decide
    g := ![![![-1390, 517, 3422], ![49, -18809, 0]], ![![395, -124, -763], ![3, 4228, 0]]]
    h := ![![![-111, -130020, 27214], ![-461, -583587, 0]], ![![7, -6465, 1353], ![32, -29016, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {96} * I193N1 =  Ideal.span {B.equivFun.symm ![-1139, -80, 19]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E193RS1 


noncomputable def E193RS2 : RelationCertificate Table 4 ![![193, 0, 0], ![-5, 1, 0]]
  ![-7183, 652, -541] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![772, 0, 0], ![-20, 4, 0]]
    hsu := by decide
    w := ![![-28732, 2608, -2164], ![77904, -7072, 5868]]
    hw := by decide
    g := ![![![-299, -25, 1], ![-5, 0, 0]], ![![7, -1, 1], ![1, -1, 0]]]
    h := ![![![-131596, 26329, -34], ![-5078169, 669, 0]], ![![356822, -71382, 72], ![13769434, -1381, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N2 : Ideal.span {4} * I193N2 =  Ideal.span {B.equivFun.symm ![-7183, 652, -541]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E193RS2 
