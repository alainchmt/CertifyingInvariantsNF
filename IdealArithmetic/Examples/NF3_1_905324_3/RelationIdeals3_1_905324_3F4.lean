import IdealArithmetic.Examples.NF3_1_905324_3.PrimesBelow3_1_905324_3F4
import IdealArithmetic.Examples.NF3_1_905324_3.ClassGroupData3_1_905324_3

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 169 ![![197, 0, 0], ![13, 1, 0]]
  ![-197, -26, -2] ![![169, 0, 0], ![-13, 1, 0]] where
    su := ![![33293, 0, 0], ![2197, 169, 0]]
    hsu := by decide
    w := ![![-33293, -4394, -338], ![2197, 169, 0]]
    hw := by decide
    g := ![![![-1, -12714, 978], ![0, -165284, 0]], ![![0, -1092, 84], ![1, -14196, 0]]]
    h := ![![![-1132, -100, -1], ![17139, 195, 0]], ![![52, 4, 0], ![-787, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {169} * I197N1 =  Ideal.span {B.equivFun.symm ![-197, -26, -2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E197RS1 


noncomputable def E197RS2 : RelationCertificate Table 13 ![![197, 0, 0], ![-14, 1, 0]]
  ![1, 0, 1] ![![13, 0, 0], ![0, 1, 0]] where
    su := ![![2561, 0, 0], ![-182, 13, 0]]
    hsu := by decide
    w := ![![13, 0, 13], ![182, -13, 0]]
    hw := by decide
    g := ![![![1, 1, 0], ![1, 1, 0]], ![![0, 0, 0], ![-1, 0, 0]]]
    h := ![![![183, -13, 0], ![2575, 1, 0]], ![![2562, -183, 0], ![36050, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N2 : Ideal.span {13} * I197N2 =  Ideal.span {B.equivFun.symm ![1, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E197RS2 


noncomputable def E199RS0 : RelationCertificate Table 17 ![![199, 0, 0], ![67, 1, 0]]
  ![27, 8, 1] ![![17, 0, 0], ![-8, 1, 0]] where
    su := ![![3383, 0, 0], ![1139, 17, 0]]
    hsu := by decide
    w := ![![459, 136, 17], ![-34, -51, 0]]
    hw := by decide
    g := ![![![2037185, 89890833, -11268185], ![4329021, 191559148, 0]], ![![692931, 30575296, -3832739], ![1472479, 65156564, 0]]]
    h := ![![![20656, 308, 0], ![-61351, 1, 0]], ![![-1674, -92, -1], ![4972, 199, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N0 : Ideal.span {17} * I199N0 =  Ideal.span {B.equivFun.symm ![27, 8, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E199RS0 


noncomputable def E199RS1 : RelationCertificate Table 17 ![![199, 0, 0], ![-35, 1, 0]]
  ![249, -32, -4] ![![17, 0, 0], ![-8, 1, 0]] where
    su := ![![3383, 0, 0], ![-595, 17, 0]]
    hsu := by decide
    w := ![![4233, -544, -68], ![-2720, 561, 0]]
    hw := by decide
    g := ![![![-145, 3986, -513], ![310, 8589, 0]], ![![21, -686, 88], ![-49, -1476, 0]]]
    h := ![![![4766, -137, 0], ![27091, -4, 0]], ![![-2970, 120, -1], ![-16882, 199, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {17} * I199N1 =  Ideal.span {B.equivFun.symm ![249, -32, -4]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E199RS1 


noncomputable def E199RS2 : RelationCertificate Table 17 ![![199, 0, 0], ![-32, 1, 0]]
  ![101, -45, 5] ![![17, 0, 0], ![-8, 1, 0]] where
    su := ![![3383, 0, 0], ![-544, 17, 0]]
    hsu := by decide
    w := ![![1717, -765, 85], ![102, 391, -85]]
    hw := by decide
    g := ![![![309, 4699, -578], ![140, 9936, 0]], ![![-36, -723, 89], ![-6, -1528, 0]]]
    h := ![![![1139, -35, 0], ![7080, 5, 0]], ![![74, 29, -1], ![460, 194, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N2 : Ideal.span {17} * I199N2 =  Ideal.span {B.equivFun.symm ![101, -45, 5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E199RS2 


noncomputable def E211RS1 : RelationCertificate Table 169 ![![211, 0, 0], ![-67, 1, 0]]
  ![6211, 806, 166] ![![169, 0, 0], ![-13, 1, 0]] where
    su := ![![35659, 0, 0], ![-11323, 169, 0]]
    hsu := by decide
    w := ![![1049659, 136214, 28054], ![-50531, -6591, -1352]]
    hw := by decide
    g := ![![![-1, 1848, -142], ![54, 24024, 0]], ![![44, 65217, -5017], ![549, 847865, 0]]]
    h := ![![![174600, -2750, 3], ![549767, -467, 0]], ![![-8358, 189, -1], ![-26317, 203, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {169} * I211N1 =  Ideal.span {B.equivFun.symm ![6211, 806, 166]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E211RS1 


noncomputable def E223RS0 : RelationCertificate Table 13 ![![223, 0, 0], ![14, 1, 0]]
  ![27, 0, 1] ![![13, 0, 0], ![0, 1, 0]] where
    su := ![![2899, 0, 0], ![182, 13, 0]]
    hsu := by decide
    w := ![![351, 0, 13], ![182, 13, 0]]
    hw := by decide
    g := ![![![1, 1, 66], ![1, -859, 0]], ![![0, 0, 5], ![1, -65, 0]]]
    h := ![![![1, 0, 0], ![-14, 1, 0]], ![![-14, -1, 0], ![224, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N0 : Ideal.span {13} * I223N0 =  Ideal.span {B.equivFun.symm ![27, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E223RS0 


noncomputable def E223RS1 : RelationCertificate Table 169 ![![223, 0, 0], ![102, 1, 0]]
  ![-787, -91, -20] ![![169, 0, 0], ![-13, 1, 0]] where
    su := ![![37687, 0, 0], ![17238, 169, 0]]
    hsu := by decide
    w := ![![-133003, -15379, -3380], ![6591, 676, 169]]
    hw := by decide
    g := ![![![-6000167, -13260369655, 1020063939], ![-78002152, -172390805680, 0]], ![![-2781840, -6147869317, 472929485], ![-36163912, -79925082960, 0]]]
    h := ![![![-7615807, -97708, -226], ![16650237, 50378, 0]], ![![377343, 4821, 11], ![-824975, -2452, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {169} * I223N1 =  Ideal.span {B.equivFun.symm ![-787, -91, -20]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E223RS1 


noncomputable def E227RS1 : RelationCertificate Table 2873 ![![227, 0, 0], ![-18, 1, 0]]
  ![2445, -832, 66] ![![2873, 0, 0], ![-858, 1, 0]] where
    su := ![![652171, 0, 0], ![-51714, 2873, 0]]
    hsu := by decide
    w := ![![7024485, -2390336, 189618], ![-2085798, 715377, -57460]]
    hw := by decide
    g := ![![![19365684739, 202917457859446, -236500559942], ![64845701938, 679466108713160, 0]], ![![-1440906664, -15098111737290, 17596868784], ![-4824854133, -50555804016420, 0]]]
    h := ![![![131988171, -7376558, 2438], ![1664517354, -553360, 0]], ![![-39191610, 2190361, -725], ![-494249708, 164555, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {2873} * I227N1 =  Ideal.span {B.equivFun.symm ![2445, -832, 66]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E227RS1 


noncomputable def E229RS1 : RelationCertificate Table 3757 ![![229, 0, 0], ![-86, 1, 0]]
  ![-3741, -572, -114] ![![3757, 0, 0], ![-1521, 1, 0]] where
    su := ![![860353, 0, 0], ![-323102, 3757, 0]]
    hsu := by decide
    w := ![![-14054937, -2149004, -428298], ![5669313, 867867, 172822]]
    hw := by decide
    g := ![![![-12050, -141761764, 93203], ![-29765, -350163693, 0]], ![![4937, 51691185, -33985], ![12195, 127681653, 0]]]
    h := ![![![-18361, 254, -1], ![-48848, 115, 0]], ![![7513, -69, 0], ![19988, 46, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {3757} * I229N1 =  Ideal.span {B.equivFun.symm ![-3741, -572, -114]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E229RS1 


noncomputable def E233RS1 : RelationCertificate Table 289 ![![233, 0, 0], ![33, 1, 0]]
  ![-2753, -346, -73] ![![289, 0, 0], ![-76, 1, 0]] where
    su := ![![67337, 0, 0], ![9537, 289, 0]]
    hsu := by decide
    w := ![![-795617, -99994, -21097], ![195942, 24565, 5202]]
    hw := by decide
    g := ![![![-270146193, -317411130579, 4176509015], ![-1027266441, -1207011105312, 0]], ![![-38520087, -45259642056, 595528275], ![-146477699, -172107671472, 0]]]
    h := ![![![-38188, -1214, -2], ![269547, 393, 0]], ![![9348, 281, 0], ![-65982, 18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {289} * I233N1 =  Ideal.span {B.equivFun.symm ![-2753, -346, -73]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E233RS1 


noncomputable def E241RS0 : RelationCertificate Table 2873 ![![241, 0, 0], ![6, 1, 0]]
  ![-46681, -6058, -1246] ![![2873, 0, 0], ![-858, 1, 0]] where
    su := ![![692393, 0, 0], ![17238, 2873, 0]]
    hsu := by decide
    w := ![![-134114513, -17404634, -3579758], ![39825526, 5168527, 1063010]]
    hw := by decide
    g := ![![![-4327, -51413099, 59922], ![-14491, -172156000, 0]], ![![350, -1395109, 1626], ![1172, -4671500, 0]]]
    h := ![![![-771268339, -128627791, -13851], ![30979270503, 3336845, 0]], ![![229029398, 38196227, 4112], ![-9199345176, -990622, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N0 : Ideal.span {2873} * I241N0 =  Ideal.span {B.equivFun.symm ![-46681, -6058, -1246]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E241RS0 


noncomputable def E241RS1 : RelationCertificate Table 17 ![![241, 0, 0], ![18, 1, 0]]
  ![61, 8, 1] ![![17, 0, 0], ![-8, 1, 0]] where
    su := ![![4097, 0, 0], ![306, 17, 0]]
    hsu := by decide
    w := ![![1037, 136, 17], ![-306, -17, 0]]
    hw := by decide
    g := ![![![49, 1666, -209], ![92, 3554, 0]], ![![8, 127, -16], ![16, 272, 0]]]
    h := ![![![271, 15, 0], ![-3625, 1, 0]], ![![-90, -23, -1], ![1204, 241, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N1 : Ideal.span {17} * I241N1 =  Ideal.span {B.equivFun.symm ![61, 8, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E241RS1 


noncomputable def E241RS2 : RelationCertificate Table 221 ![![241, 0, 0], ![-24, 1, 0]]
  ![349, 65, -28] ![![221, 0, 0], ![26, 1, 0]] where
    su := ![![53261, 0, 0], ![-5304, 221, 0]]
    hsu := by decide
    w := ![![77129, 14365, -6188], ![3978, 2431, -663]]
    hw := by decide
    g := ![![![12417976625, -23650036451432, -909635156381], ![-105552801149, 201029369560314, 0]], ![![-1241328918, 2364110892927, 90929178321], ![10551295790, -20095348408950, 0]]]
    h := ![![![1865653, -78482, 31], ![18734251, -7499, 0]], ![![96210, -4033, 1], ![966108, -244, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N2 : Ideal.span {221} * I241N2 =  Ideal.span {B.equivFun.symm ![349, 65, -28]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E241RS2 


noncomputable def E257RS1 : RelationCertificate Table 48841 ![![257, 0, 0], ![-43, 1, 0]]
  ![7299, -767, 123] ![![48841, 0, 0], ![13507, 1, 0]] where
    su := ![![12552137, 0, 0], ![-2100163, 48841, 0]]
    hsu := by decide
    w := ![![356490459, -37461047, 6007443], ![98609979, -10354292, 1660594]]
    hw := by decide
    g := ![![![-21025, 3693462135, 273448], ![76026, -13355473770, 0]], ![![-9765, -614284854, -45479], ![35310, 2221239840, 0]]]
    h := ![![![9729, -208, 0], ![57978, 123, 0]], ![![2711, -58, 0], ![16156, 34, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R257N1 : Ideal.span {48841} * I257N1 =  Ideal.span {B.equivFun.symm ![7299, -767, 123]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E257RS1 
