import IdealArithmetic.Examples.NF3_1_410700_2.PrimesBelow3_1_410700_2F0
import IdealArithmetic.Examples.NF3_1_410700_2.ClassGroupData3_1_410700_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 27 ![![2, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![54, 0, 0], ![27, 27, 0]] where
    su := ![![54, 0, 0], ![27, 27, 0]]
    hsu := by decide
    w := ![![54, 0, 0], ![27, 27, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {27} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![-28, -2, 1]]
  ![1, 0, 0] ![![3, 0, 0], ![-28, -2, 1]] where
    su := ![![3, 0, 0], ![-28, -2, 1]]
    hsu := by decide
    w := ![![3, 0, 0], ![-28, -2, 1]]
    hw := by decide
    g := ![![![21, -12, 4], ![-84, -12, 0]], ![![-68, 116, -40], ![769, 108, 0]]]
    h := ![![![21, -12, 4], ![-84, -12, 0]], ![![-68, 116, -40], ![769, 108, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 81 ![![3, 0, 0], ![-1, 1, 0]]
  ![-20, -5, -1] ![![81, 0, 0], ![-72, -2, 3]] where
    su := ![![243, 0, 0], ![-81, 81, 0]]
    hsu := by decide
    w := ![![-1620, -405, -81], ![-972, -324, -81]]
    hw := by decide
    g := ![![![-12086, -1495, -184], ![10791, 2912, 0]], ![![49, 1, -2], ![58, 0, 0]]]
    h := ![![![-526429, -156826, 2823], ![123203, 0, 8470]], ![![-300817, -89615, 1613], ![70401, 0, 4840]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {81} * I3N1 =  Ideal.span {B.equivFun.symm ![-20, -5, -1]} * (J0 ^ 7*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_0 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 1458 ![![5, 0, 0], ![-2, 1, 0]]
  ![-549, -61, 24] ![![1458, 0, 0], ![-173, 633, 1]] where
    su := ![![7290, 0, 0], ![-2916, 1458, 0]]
    hsu := by decide
    w := ![![-800442, -88938, 34992], ![3134700, 246402, -119556]]
    hw := by decide
    g := ![![![-4418000351969, -8638193522563, -38092129679905], ![-3252232213317, 29247802688528, -1]], ![![-8834827872463, -17274093892809, -76174147171283], ![-6503601068421, 58487841062032, -2]]]
    h := ![![![-109, -220, 627], ![2, -1037, 0]], ![![430, 860, -2495], ![0, 4131, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1458} * I5N0 =  Ideal.span {B.equivFun.symm ![-549, -61, 24]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS0 


noncomputable def E11RS0 : RelationCertificate Table 1458 ![![11, 0, 0], ![-30, -7, 1]]
  ![-252, -28, 15] ![![1458, 0, 0], ![15609, 771, -567]] where
    su := ![![16038, 0, 0], ![-43740, -10206, 1458]]
    hsu := by decide
    w := ![![-367416, -40824, 21870], ![2152008, -97686, -36450]]
    hw := by decide
    g := ![![![-17442876, -1453573, 610222], ![2299979, 0, -54253]], ![![-12075912, -1006326, 422464], ![1592303, 0, -37560]]]
    h := ![![![18, 7, 0], ![15, 0, 0]], ![![36, -29, 1], ![-36, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {1458} * I11N0 =  Ideal.span {B.equivFun.symm ![-252, -28, 15]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 162 ![![11, 0, 0], ![-1, 1, 0]]
  ![43, 1, -1] ![![162, 0, 0], ![-756, -54, 27]] where
    su := ![![1782, 0, 0], ![-162, 162, 0]]
    hsu := by decide
    w := ![![6966, 162, -162], ![-14418, -1620, 648]]
    hw := by decide
    g := ![![![17557, -5265, 1662], ![-79883, -11652, 0]], ![![-1441, 441, -139], ![6661, 971, 0]]]
    h := ![![![4, 0, 1], ![1, -4, 0]], ![![-8, -1, -4], ![1, 16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {162} * I11N1 =  Ideal.span {B.equivFun.symm ![43, 1, -1]} * (J0 ^ 7*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 81 ![![13, 0, 0], ![6, 1, 0]]
  ![-46, -1, 1] ![![81, 0, 0], ![-72, -2, 3]] where
    su := ![![1053, 0, 0], ![486, 81, 0]]
    hsu := by decide
    w := ![![-3726, -81, 81], ![2106, 162, -81]]
    hw := by decide
    g := ![![![-27, -6, -2], ![79, 13, 0]], ![![42, -1, -3], ![90, 5, 0]]]
    h := ![![![8, -542, -233], ![-25, 1010, 0]], ![![-10, 304, 131], ![26, -568, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {81} * I13N0 =  Ideal.span {B.equivFun.symm ![-46, -1, 1]} * (J0 ^ 7*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_0 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 54 ![![13, 0, 0], ![-5, 1, 0]]
  ![99, 5, -3] ![![54, 0, 0], ![-21, 3, 0]] where
    su := ![![702, 0, 0], ![-270, 54, 0]]
    hsu := by decide
    w := ![![5346, 270, -162], ![-3888, -162, 108]]
    hw := by decide
    g := ![![![-4244603, -226170053, 113388192], ![-10914317, -680329122, 13]], ![![1632499, 86986113, -43609656], ![4197712, 261657924, -5]]]
    h := ![![![31958, -6826, 327], ![83071, -1418, 0]], ![![-23234, 4967, -241], ![-60394, 1045, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {54} * I13N1 =  Ideal.span {B.equivFun.symm ![99, 5, -3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 1458 ![![13, 0, 0], ![-2, 1, 0]]
  ![342, 38, -3] ![![1458, 0, 0], ![-173, 633, 1]] where
    su := ![![18954, 0, 0], ![-2916, 1458, 0]]
    hsu := by decide
    w := ![![498636, 55404, -4374], ![-433026, 157464, 72900]]
    hw := by decide
    g := ![![![123335713949558566509, 241149316516771281711, 1063404172802231756174], ![90791387527191236158, -816500302966393417189, -56849]], ![![-18974725222533294349, -37099894847803911011, -163600641965472480237], ![-13967905773063846284, 125615431222449679403, 8746]]]
    h := ![![![28, 157, -465], ![11, 2014, 0]], ![![-23, -137, 440], ![-1, -1890, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {1458} * I13N2 =  Ideal.span {B.equivFun.symm ![342, 38, -3]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E13RS2 


noncomputable def E17RS1 : RelationCertificate Table 1458 ![![17, 0, 0], ![-8, 1, 0]]
  ![441, -5, -6] ![![1458, 0, 0], ![-451, -1, 1]] where
    su := ![![24786, 0, 0], ![-11664, 1458, 0]]
    hsu := by decide
    w := ![![642978, -7290, -8748], ![-198288, 1458, 2916]]
    hw := by decide
    g := ![![![56014627354, -125454526694, -903814742], ![-17241457929, -445001115480, -13]], ![![-17393313374, 38955359096, 280646930], ![5353710921, 138178977740, 4]]]
    h := ![![![65, 1821, -783], ![83, 4435, 0]], ![![-16, -561, 241], ![-17, -1365, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {1458} * I17N1 =  Ideal.span {B.equivFun.symm ![441, -5, -6]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E17RS1 


noncomputable def E23RS1 : RelationCertificate Table 1458 ![![23, 0, 0], ![5, 1, 0]]
  ![171, 13, -6] ![![1458, 0, 0], ![315, -9, 9]] where
    su := ![![33534, 0, 0], ![7290, 1458, 0]]
    hsu := by decide
    w := ![![249318, 18954, -8748], ![91854, 5832, -2916]]
    hw := by decide
    g := ![![![-774560, -303350, 13125], ![-165380, 653039, -23]], ![![-168386, -65944, 2853], ![-35918, 141962, -5]]]
    h := ![![![-18, 2480, 1242], ![117, -9524, 0]], ![![-9, 914, 458], ![54, -3512, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {1458} * I23N1 =  Ideal.span {B.equivFun.symm ![171, 13, -6]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 1458 ![![29, 0, 0], ![-13, 1, 0]]
  ![-72, -2, 3] ![![1458, 0, 0], ![315, -9, 9]] where
    su := ![![42282, 0, 0], ![-18954, 1458, 0]]
    hsu := by decide
    w := ![![-104976, -2916, 4374], ![-33534, 0, 1458]]
    hw := by decide
    g := ![![![3137682266051855, 1228923417489112, -53127189013700], ![669980424106947, -2645541507959976, -4312730]], ![![-1291986804601279, -506027285311870, 21875901175177], ![-275874289966350, 1089340611791800, 1775830]]]
    h := ![![![-647112, 49790, -3], ![-1443552, 30, 0]], ![![-206998, 15927, -1], ![-461763, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {1458} * I29N1 =  Ideal.span {B.equivFun.symm ![-72, -2, 3]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E29RS1 
