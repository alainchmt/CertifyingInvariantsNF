import IdealArithmetic.Examples.NF3_1_959175_1.PrimesBelow3_1_959175_1F1
import IdealArithmetic.Examples.NF3_1_959175_1.ClassGroupData3_1_959175_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 2 ![![37, 0, 0], ![-8, 1, 0]]
  ![2097082, 73853, -43417] ![![2, 0, 0], ![-35, -1, 1]] where
    su := ![![74, 0, 0], ![-16, 2, 0]]
    hsu := by decide
    w := ![![4194164, 147706, -86834], ![-28405510, -3607288, 1050600]]
    hw := by decide
    g := ![![![-126923529, 15479778633, 4277203576], ![-3380125229, -10290, 0]], ![![-14659604, 1787722520, 493959304], ![-390338464, 2205, 0]]]
    h := ![![![8026114, -1021604, 6661], ![36858642, -144937, 0]], ![![-54314183, 6879546, -39232], ![-249427752, 988442, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {2} * I37N1 =  Ideal.span {B.equivFun.symm ![2097082, 73853, -43417]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E37RS1 


noncomputable def E43RS1 : RelationCertificate Table 4 ![![43, 0, 0], ![9, 1, 0]]
  ![-76005204, -22109563, -3331491] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![172, 0, 0], ![36, 4, 0]]
    hsu := by decide
    w := ![![-304020816, -88438252, -13325964], ![-856812276, -249242736, -37556144]]
    hw := by decide
    g := ![![![57936, 2476, -11688], ![-13863, 21952, 0]], ![![7778, 774, -2751], ![-1749, 5145, 0]]]
    h := ![![![-2384764962, -279111817, -2841507], ![11385432018, 59426655, 0]], ![![-6720907860, -786612011, -8008126], ![32087203879, 167480191, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {4} * I43N1 =  Ideal.span {B.equivFun.symm ![-76005204, -22109563, -3331491]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 4 ![![53, 0, 0], ![-3, 1, 0]]
  ![33131172, 9637705, 1452219] ![![4, 0, 0], ![35, 3, -1]] where
    su := ![![212, 0, 0], ![-12, 4, 0]]
    hsu := by decide
    w := ![![132524688, 38550820, 5808876], ![87518900, 25458844, 3836164]]
    hw := by decide
    g := ![![![554, -925, 126], ![4233, -88, 0]], ![![-139, 353, -52], ![-915, 1, 0]]]
    h := ![![![51557022, -16811655, 43597], ![899796998, -429211, 0]], ![![34048105, -11102367, 28791], ![594223280, -283441, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {4} * I53N1 =  Ideal.span {B.equivFun.symm ![33131172, 9637705, 1452219]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 4 ![![59, 0, 0], ![15, 1, 0]]
  ![-3764, -1095, -165] ![![4, 0, 0], ![35, 3, -1]] where
    su := ![![236, 0, 0], ![60, 4, 0]]
    hsu := by decide
    w := ![![-15056, -4380, -660], ![-9940, -2892, -436]]
    hw := by decide
    g := ![![![92279, -199582, 18115], ![653333, 82984, 0]], ![![26205, -56697, 5146], ![185609, 23575, 0]]]
    h := ![![![2984, 167, -5], ![-11988, 65, 0]], ![![1975, 97, -5], ![-7934, 93, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {4} * I59N1 =  Ideal.span {B.equivFun.symm ![-3764, -1095, -165]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 4 ![![61, 0, 0], ![-10, 1, 0]]
  ![-363132609244, -105633599791, -15916976152] ![![4, 0, 0], ![-69, -3, 2]] where
    su := ![![244, 0, 0], ![-40, 4, 0]]
    hsu := by decide
    w := ![![-1452530436976, -422534399164, -63667904608], ![-11814899232324, -3436899648524, -517875466240]]
    hw := by decide
    g := ![![![-46295, 374044, -119680], ![459159, 0, 0]], ![![12244, -119481, 33278], ![-104246, 0, 0]]]
    h := ![![![-14521107437944, 1479972233015, -6969486688], ![-88542442110534, 204610855908, 0]], ![![-118114854431801, 12038111115987, -56689884640], ![-720205239553178, 1664307048240, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {4} * I61N1 =  Ideal.span {B.equivFun.symm ![-363132609244, -105633599791, -15916976152]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E61RS1 


noncomputable def E71RS1 : RelationCertificate Table 4 ![![71, 0, 0], ![35, 1, 0]]
  ![-645892, -187887, -28311] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![284, 0, 0], ![140, 4, 0]]
    hsu := by decide
    w := ![![-2583568, -751548, -113244], ![-7281188, -2118064, -319152]]
    hw := by decide
    g := ![![![9772, 1056, -2508], ![-2175, 4536, 0]], ![![3922, 446, -1518], ![-867, 2835, 0]]]
    h := ![![![244018, -44999127, -2500605], ![-513462, 88757322, 0]], ![![687733, -126819616, -7047376], ![-1447124, 250141954, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {4} * I71N1 =  Ideal.span {B.equivFun.symm ![-645892, -187887, -28311]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 2 ![![73, 0, 0], ![6, 1, 0]]
  ![6, 1, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![146, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![12, 2, 0], ![6, 8, 2]]
    hw := by decide
    g := ![![![-29, 3, 1], ![-11, 0, 0]], ![![0, -1, 0], ![2, 0, 0]]]
    h := ![![![54, 9, 0], ![-656, 0, 0]], ![![27, 1, -1], ![-328, 37, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {2} * I73N1 =  Ideal.span {B.equivFun.symm ![6, 1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0], ![-24, 1, 0]]
  ![98326, 59238, -11931] ![![2, 0, 0], ![-35, -2, 1]] where
    su := ![![158, 0, 0], ![-48, 2, 0]]
    hsu := by decide
    w := ![![196652, 118476, -23862], ![23167270, 572608, -436484]]
    hw := by decide
    g := ![![![-100068111, 2931107180, 912528053], ![-723650917, 0, 0]], ![![14854351, -435099715, -135457580], ![107420242, -3, 0]]]
    h := ![![![4638538, -205650, 995], ![15264424, -45268, 0]], ![![548293877, -24381957, 131682], ![1804318027, -5310560, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![98326, 59238, -11931]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E79RS1 
