import IdealArithmetic.Examples.NF3_1_649415_1.PrimesBelow3_1_649415_1F2
import IdealArithmetic.Examples.NF3_1_649415_1.ClassGroupData3_1_649415_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 27 ![![83, 0, 0], ![-35, 1, 0]]
  ![269, 12, -16] ![![27, 0, 0], ![-4, 1, 0]] where
    su := ![![2241, 0, 0], ![-945, 27, 0]]
    hsu := by decide
    w := ![![7263, 324, -432], ![-3564, 81, 108]]
    hw := by decide
    g := ![![![384927, -993728, 997192], ![-93812, -5384856, 0]], ![![-157027063, 405326153, -406743756], ![38275364, 2196416288, 0]]]
    h := ![![![703568, -16410391, 2280048], ![-494335, -37848800, 0]], ![![-345569, 8061160, -1120012], ![242923, 18592200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {27} * I83N1 =  Ideal.span {B.equivFun.symm ![269, 12, -16]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E83RS1 


noncomputable def E101RS1 : RelationCertificate Table 3 ![![101, 0, 0], ![-21, 1, 0]]
  ![-643, -84, -43] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![303, 0, 0], ![-63, 3, 0]]
    hsu := by decide
    w := ![![-1929, -252, -129], ![-6276, -819, -420]]
    hw := by decide
    g := ![![![104, 15, -7], ![-28, 0, 0]], ![![-31, -4, 0], ![12, 1, 0]]]
    h := ![![![3703, -43450, 9877], ![-1162, -199524, 0]], ![![12040, -141365, 32135], ![-3818, -649155, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {3} * I101N1 =  Ideal.span {B.equivFun.symm ![-643, -84, -43]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 9 ![![103, 0, 0], ![34, 1, 0]]
  ![-32353, 912, 905] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![927, 0, 0], ![306, 9, 0]]
    hsu := by decide
    w := ![![-291177, 8208, 8145], ![273321, -29673, 1845]]
    hw := by decide
    g := ![![![4771344, -213859, 1492105], ![-2144356, -2051640, 0]], ![![107725371, -350064968, 360158465], ![-86774050, -648009661, 0]]]
    h := ![![![-1986069, -38353263, -5812605], ![-1027851, 119739844, 0]], ![![1865735, 36030209, 5460550], ![965713, -112487289, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {9} * I103N0 =  Ideal.span {B.equivFun.symm ![-32353, 912, 905]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 27 ![![103, 0, 0], ![-17, 1, 0]]
  ![-8219431, -1072860, -549637] ![![27, 0, 0], ![-4, 1, 0]] where
    su := ![![2781, 0, 0], ![-459, 27, 0]]
    hsu := by decide
    w := ![![-221924637, -28967220, -14840199], ![-55561005, -7252227, -3715389]]
    hw := by decide
    g := ![![![182, -171, 66], ![-19, 7, 0]], ![![63, 55, -37], ![11, 98, 0]]]
    h := ![![![2477862582, -23237957675, 6456691391], ![-634578811, -133007952582, 0]], ![![620357159, -5817850151, 1616495886], ![-158872962, -33299842773, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {27} * I103N1 =  Ideal.span {B.equivFun.symm ![-8219431, -1072860, -549637]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E103RS1 


noncomputable def E127RS1 : RelationCertificate Table 27 ![![127, 0, 0], ![16, 1, 0]]
  ![-35246723, -4600659, -2356964] ![![27, 0, 0], ![-4, 1, 0]] where
    su := ![![3429, 0, 0], ![432, 27, 0]]
    hsu := by decide
    w := ![![-951661521, -124217793, -63638028], ![-238257774, -31099140, -15932403]]
    hw := by decide
    g := ![![![-4757680466324, 12280762696785, -12323713978803], ![1159684613425, 66548055486702, 0]], ![![-593149140435, 1531066218545, -1536421037193], ![144580102999, 8296673600944, 0]]]
    h := ![![![3994681, 32718388, 10901643], ![760940, -277373125, 0]], ![![1000098, 8191368, 2729333], ![190584, -69443076, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {27} * I127N1 =  Ideal.span {B.equivFun.symm ![-35246723, -4600659, -2356964]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 27 ![![131, 0, 0], ![-57, 1, 0]]
  ![100, 15, 7] ![![27, 0, 0], ![-4, 1, 0]] where
    su := ![![3537, 0, 0], ![-1539, 27, 0]]
    hsu := by decide
    w := ![![2700, 405, 189], ![729, 81, 54]]
    hw := by decide
    g := ![![![185, -486, 487], ![-22, -2628, 0]], ![![40642, -104892, 105258], ![-9885, -568394, 0]]]
    h := ![![![441188, -16834339, 1451447], ![-320356, -38027910, 0]], ![![119193, -4546911, 392032], ![-86460, -10271238, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {27} * I131N1 =  Ideal.span {B.equivFun.symm ![100, 15, 7]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 2187 ![![137, 0, 0], ![-50, 1, 0]]
  ![-335, 105, -14] ![![2187, 0, 0], ![-1057, 1, 0]] where
    su := ![![299619, 0, 0], ![-109350, 2187, 0]]
    hsu := by decide
    w := ![![-732645, 229635, -30618], ![352107, -111537, 15309]]
    hw := by decide
    g := ![![![2902680, -2144301044, 10133753], ![-2381122, -4432503558, 0]], ![![-1061594, 785199801, -3710776], ![874627, 1623093421, 0]]]
    h := ![![![-76301155, 2365180995, -231912772], ![45111240, 6354409950, 0]], ![![36672083, -1136758844, 111462461], ![-21681353, -3054071430, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {2187} * I137N1 =  Ideal.span {B.equivFun.symm ![-335, 105, -14]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E137RS1 
