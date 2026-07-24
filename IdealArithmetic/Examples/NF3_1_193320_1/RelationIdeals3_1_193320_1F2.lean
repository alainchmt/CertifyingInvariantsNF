import IdealArithmetic.Examples.NF3_1_193320_1.PrimesBelow3_1_193320_1F2
import IdealArithmetic.Examples.NF3_1_193320_1.ClassGroupData3_1_193320_1

set_option linter.all false

noncomputable section


noncomputable def E97RS0 : RelationCertificate Table 8 ![![97, 0, 0], ![-48, 1, 0]]
  ![191, -1338, 149] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![776, 0, 0], ![-384, 8, 0]]
    hsu := by decide
    w := ![![1528, -10704, 1192], ![28096, 6008, -1040]]
    hw := by decide
    g := ![![![-151819, -62861, -7791], ![-45804, 287, 0]], ![![61298, 25387, 3149], ![18499, -142, 0]]]
    h := ![![![78623, -1914, 7], ![158880, -530, 0]], ![![1364888, -33915, 113], ![2758138, -11091, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {8} * I97N0 =  Ideal.span {B.equivFun.symm ![191, -1338, 149]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E97RS0 


noncomputable def E97RS1 : RelationCertificate Table 16 ![![97, 0, 0], ![-26, 1, 0]]
  ![20285347, 8512558, 963529] ![![16, 0, 0], ![2, 1, 0]] where
    su := ![![1552, 0, 0], ![-416, 16, 0]]
    hsu := by decide
    w := ![![324565552, 136200928, 15416464], ![219787088, 92231616, 10439616]]
    hw := by decide
    g := ![![![-2764, 1700468, 853394], ![105937, -13656500, 0]], ![![-654595573770, 85097424196885, 42712360991144], ![5236764565586, -683397775857711, 0]]]
    h := ![![![9934849033, -403198491, 824730], ![37063848879, -79035281, 0]], ![![6727613355, -273035205, 558485], ![25098644567, -53520569, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {16} * I97N1 =  Ideal.span {B.equivFun.symm ![20285347, 8512558, 963529]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E97RS1 


noncomputable def E97RS2 : RelationCertificate Table 8 ![![97, 0, 0], ![-23, 1, 0]]
  ![931747, 57158, -18407] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![776, 0, 0], ![-184, 8, 0]]
    hsu := by decide
    w := ![![7453976, 457264, -147256], ![-1560208, -3136, 20344]]
    hw := by decide
    g := ![![![-2036004105, 80857051657, 40969400452], ![9598130437, -327617066366, 0]], ![![525789179, -19575624562, -9923914182], ![-2315505769, 79371140819, 0]]]
    h := ![![![10694019, -483403, 656], ![45060352, -82039, 0]], ![![-2238854, 101326, -151], ![-9433644, 17190, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N2 : Ideal.span {8} * I97N2 =  Ideal.span {B.equivFun.symm ![931747, 57158, -18407]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E97RS2 


noncomputable def E101RS0 : RelationCertificate Table 16 ![![101, 0, 0], ![-42, 1, 0]]
  ![-670607, -281414, -31853] ![![16, 0, 0], ![2, 1, 0]] where
    su := ![![1616, 0, 0], ![-672, 16, 0]]
    hsu := by decide
    w := ![![-10729712, -4502624, -509648], ![-7265872, -3049056, -345120]]
    hw := by decide
    g := ![![![3082828262292, -400767673656023, -201154543892926], ![-24662626070711, 3218472702285634, 0]], ![![-1297229714402, 168639862670898, 84644238763748], ![10377837702640, -1354307820219435, 0]]]
    h := ![![![-483668563, 13083422, -37707], ![-1163091768, 3776554, 0]], ![![-327527321, 8859734, -25534], ![-787614412, 2557364, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {16} * I101N0 =  Ideal.span {B.equivFun.symm ![-670607, -281414, -31853]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0], ![-38, 1, 0]]
  ![-8021, -3366, -381] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![202, 0, 0], ![-76, 2, 0]]
    hsu := by decide
    w := ![![-16042, -6732, -762], ![-70866, -29738, -3366]]
    hw := by decide
    g := ![![![-1549, -252, -7400], ![-126, 14911, 0]], ![![685, 107, 2394], ![55, -4836, 0]]]
    h := ![![![-38713, 1068, -6], ![-102684, 225, 0]], ![![-171329, 4745, -27], ![-454442, 1044, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![-8021, -3366, -381]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 4 ![![103, 0, 0], ![-45, 1, 0]]
  ![-162367, -4230, 2559] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![412, 0, 0], ![-180, 4, 0]]
    hsu := by decide
    w := ![![-649468, -16920, 10236], ![151240, -24964, 888]]
    hw := by decide
    g := ![![![-60884401, -24084364, -3757850], ![-36463290, -259, 0]], ![![21377653, 8456460, 1319446], ![12802945, 113, 0]]]
    h := ![![![-31288369, 795294, -2199], ![-71611992, 229056, 0]], ![![7295020, -185422, 519], ![16696650, -53235, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {4} * I103N1 =  Ideal.span {B.equivFun.symm ![-162367, -4230, 2559]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS1 


noncomputable def E113RS1 : RelationCertificate Table 16 ![![113, 0, 0], ![-44, 1, 0]]
  ![356465, 28042, -7741] ![![16, 0, 0], ![2, 1, 0]] where
    su := ![![1808, 0, 0], ![-704, 16, 0]]
    hsu := by decide
    w := ![![5703440, 448672, -123856], ![-726896, -28688, 12560]]
    hw := by decide
    g := ![![![10503627, 4392378, 508622], ![1587488, -4595, 0]], ![![-3268695, -1366929, -158299], ![-494015, 1710, 0]]]
    h := ![![![3919857, -96270, 102], ![10058804, -19267, 0]], ![![-499591, 12295, -15], ![-1282008, 2480, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {16} * I113N1 =  Ideal.span {B.equivFun.symm ![356465, 28042, -7741]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E113RS1 
