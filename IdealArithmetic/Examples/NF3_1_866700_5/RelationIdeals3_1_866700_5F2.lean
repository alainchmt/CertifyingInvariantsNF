import IdealArithmetic.Examples.NF3_1_866700_5.PrimesBelow3_1_866700_5F2
import IdealArithmetic.Examples.NF3_1_866700_5.ClassGroupData3_1_866700_5

set_option linter.all false

noncomputable section


noncomputable def E97RS1 : RelationCertificate Table 7 ![![97, 0, 0], ![21, 1, 0]]
  ![21, 0, -2] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![679, 0, 0], ![147, 7, 0]]
    hsu := by decide
    w := ![![147, 0, -14], ![-385, 21, 14]]
    hw := by decide
    g := ![![![-11291, 9349, 25401], ![2950, -13677, 0]], ![![-2404, 1992, 5412], ![629, -2914, 0]]]
    h := ![![![30093, -140417, -67583], ![5078, 504273, 0]], ![![-78952, 368300, 177264], ![-13223, -1322662, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {7} * I97N1 =  Ideal.span {B.equivFun.symm ![21, 0, -2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E97RS1 


noncomputable def E101RS0 : RelationCertificate Table 169 ![![101, 0, 0], ![10, 1, 0]]
  ![-217, 5, 13] ![![169, 0, 0], ![-64, 1, 0]] where
    su := ![![17069, 0, 0], ![1690, 169, 0]]
    hsu := by decide
    w := ![![-36673, 845, 2197], ![16224, -507, -845]]
    hw := by decide
    g := ![![![533233, 5741305, -1287776], ![-167924, 16726080, -2787]], ![![55140, 593289, -133075], ![-17254, 1728424, -288]]]
    h := ![![![-19840527, 53301600, 43295993], ![-1436635, -336376560, 0]], ![![8778166, -23582558, -19155715], ![635635, 148825170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {169} * I101N0 =  Ideal.span {B.equivFun.symm ![-217, 5, 13]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 7 ![![101, 0, 0], ![32, 1, 0]]
  ![7, 0, 1] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![707, 0, 0], ![224, 7, 0]]
    hsu := by decide
    w := ![![49, 0, 7], ![175, 7, -7]]
    hw := by decide
    g := ![![![8016, -6627, -18007], ![-2089, 9696, 0]], ![![2500, -2067, -5616], ![-650, 3024, 0]]]
    h := ![![![371, -2688, -919], ![168, 7140, 0]], ![![1375, -9592, -3280], ![439, 25483, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {7} * I101N1 =  Ideal.span {B.equivFun.symm ![7, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 637 ![![101, 0, 0], ![-42, 1, 0]]
  ![-4319, 266, 65] ![![637, 0, 0], ![-155, 1, 0]] where
    su := ![![64337, 0, 0], ![-26754, 637, 0]]
    hsu := by decide
    w := ![![-2751203, 169442, 41405], ![679679, -43953, -7007]]
    hw := by decide
    g := ![![![180064097437898673261, 4691897675300035349527, -409355207523322103400], ![-36449038347840280550, 20058405168642783069601, 252]], ![![-54305830726008760782, -1415037225988225805582, 123458118097299385815], ![10992726117022185792, -6049447786767669905843, -76]]]
    h := ![![![173907125, 1194958532, -431296541], ![-60486434, 3350842362, 0]], ![![-42974315, -295287389, 106578116], ![14946976, -828029979, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {637} * I101N2 =  Ideal.span {B.equivFun.symm ![-4319, 266, 65]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E101RS2 


noncomputable def E103RS1 : RelationCertificate Table 49 ![![103, 0, 0], ![18, 1, 0]]
  ![-15477, -1932, -1255] ![![49, 0, 0], ![-8, 1, 0]] where
    su := ![![5047, 0, 0], ![882, 49, 0]]
    hsu := by decide
    w := ![![-758373, -94668, -61495], ![-93002, -11613, -7546]]
    hw := by decide
    g := ![![![82110133, 28329931, -182442931], ![-12827545, 687669502, 0]], ![![14216478, 4905021, -31588019], ![-2220948, 119062533, 0]]]
    h := ![![![-1716945, 7031362, 3807434], ![-231682, -30166689, 0]], ![![-210566, 862280, 466919], ![-28349, -3699447, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {49} * I103N1 =  Ideal.span {B.equivFun.symm ![-15477, -1932, -1255]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E103RS1 


noncomputable def E107RS0 : RelationCertificate Table 91 ![![107, 0, 0], ![-44, 1, 0]]
  ![-35, 70, -104] ![![91, 0, 0], ![27, 1, 0]] where
    su := ![![9737, 0, 0], ![-4004, 91, 0]]
    hsu := by decide
    w := ![![-3185, 6370, -9464], ![-20293, 2275, -1274]]
    hw := by decide
    g := ![![![789643887835, -4642446932818, -1828013934372], ![183274044468, 12796345358772, -153411324]], ![![-320548508965, 1884557665797, 742065062467], ![-74398374441, -5194556036739, 62275884]]]
    h := ![![![318015, 2299410, -786292], ![-109160, 6471780, 0]], ![![1824675, 13194811, -4512010], ![-626896, 37137312, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {91} * I107N0 =  Ideal.span {B.equivFun.symm ![-35, 70, -104]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 91 ![![107, 0, 0], ![-19, 1, 0]]
  ![6895, 861, 559] ![![91, 0, 0], ![27, 1, 0]] where
    su := ![![9737, 0, 0], ![-1729, 91, 0]]
    hsu := by decide
    w := ![![627445, 78351, 50869], ![282737, 35308, 22932]]
    hw := by decide
    g := ![![![-24578504, 144565616, 56925680], ![-5703807, -398477796, -1212]], ![![3934163, -23140051, -9111870], ![913064, 63782775, 194]]]
    h := ![![![164280936, 366089462, -365848795], ![-25749949, 3011217048, 0]], ![![74027681, 164965888, -164857440], ![-11603296, 1356903564, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {91} * I107N1 =  Ideal.span {B.equivFun.symm ![6895, 861, 559]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E107RS1 


noncomputable def E113RS1 : RelationCertificate Table 49 ![![113, 0, 0], ![21, 1, 0]]
  ![133, -7, -3] ![![49, 0, 0], ![-8, 1, 0]] where
    su := ![![5537, 0, 0], ![1029, 49, 0]]
    hsu := by decide
    w := ![![6517, -343, -147], ![-1568, 147, -49]]
    hw := by decide
    g := ![![![522649784715, 180326492116, -1161291017329], ![-81650444561, 4377173834549, 0]], ![![92504476979, 31916224450, -205538433795], ![-14451420202, 774721788920, 0]]]
    h := ![![![2645657, -12229607, -5886695], ![383556, 51168964, 0]], ![![-636943, 2944188, 1417179], ![-92229, -12318556, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {49} * I113N1 =  Ideal.span {B.equivFun.symm ![133, -7, -3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E113RS1 


noncomputable def E127RS1 : RelationCertificate Table 8281 ![![127, 0, 0], ![-44, 1, 0]]
  ![24955, 3143, 2054] ![![8281, 0, 0], ![1119, 1, 0]] where
    su := ![![1051687, 0, 0], ![-364364, 8281, 0]]
    hsu := by decide
    w := ![![206652355, 26027183, 17009174], ![28279615, 3560830, 2326961]]
    hw := by decide
    g := ![![![-7767243485032191006367, 1478427571900260501953061, 17084050726477240455033], ![-871044304776085158000, -10882540312766002169411680, -5190]], ![![2648944356603748623927, -504203631671828173997528, -5826352662568360548911], ![297061357730680663063, 3711386646056045669504770, 1770]]]
    h := ![![![113597167377, 792376356208, -270986912326], ![-33117315017, 2647333682112, 0]], ![![15545359595, 108433825075, -37083574262], ![-4531984165, 362277994735, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {8281} * I127N1 =  Ideal.span {B.equivFun.symm ![24955, 3143, 2054]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 1183 ![![131, 0, 0], ![26, 1, 0]]
  ![-441, -28, -39] ![![1183, 0, 0], ![-64, 1, 0]] where
    su := ![![154973, 0, 0], ![30758, 1183, 0]]
    hsu := by decide
    w := ![![-521703, -33124, -46137], ![21294, 1183, 2366]]
    hw := by decide
    g := ![![![-115681543, -1121034337, 251265421], ![5311469, -22865143262, 1866]], ![![-23991180, -232491514, 52109981], ![1102213, -4742006187, 387]]]
    h := ![![![-160367, 882016, 358241], ![-25084, -3609970, 0]], ![![6544, -36003, -14623], ![1034, 147355, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {1183} * I131N1 =  Ideal.span {B.equivFun.symm ![-441, -28, -39]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E131RS1 
