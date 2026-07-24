import IdealArithmetic.Examples.NF3_1_244068_1.PrimesBelow3_1_244068_1F0
import IdealArithmetic.Examples.NF3_1_244068_1.ClassGroupData3_1_244068_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 3 ![![3, 0, 0], ![15, 0, 1]]
  ![-345002003, 1068627916, 985131603] ![![3, 0, 0], ![14, 1, 1]] where
    su := ![![9, 0, 0], ![45, 0, 3]]
    hsu := by decide
    w := ![![-1035006009, 3205883748, 2955394809], ![14238281820, -23587503063, -3868046850]]
    hw := by decide
    g := ![![![3165784848562735117, -3555456892589984971, -1432868908266125488], ![13110887359674060431, 0, 2]], ![![15437954233613013471, -17338190500313911091, -6987387231517711898], ![63935260512916855213, 0, 11]]]
    h := ![![![-101705405, 1161213979, 551598176], ![-324660922, 345002003, 0]], ![![1138220895, -13695052867, -3517964217], ![4518449761, -4746093940, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {3} * I3N0 =  Ideal.span {B.equivFun.symm ![-345002003, 1068627916, 985131603]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![-14, -1, -1]]
  ![1, 0, 0] ![![3, 0, 0], ![14, 1, 1]] where
    su := ![![3, 0, 0], ![-14, -1, -1]]
    hsu := by decide
    w := ![![3, 0, 0], ![14, 1, 1]]
    hw := by decide
    g := ![![![-9, -33, -19], ![3, 0, -6]], ![![-18, 144, 81], ![-1, 0, 27]]]
    h := ![![![5, -32, -18], ![0, 0, 6]], ![![18, -144, -81], ![-1, 0, 27]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0, 0], ![15, -2, 1]]
  ![5075, -5476, 3878] ![![3, 0, 0], ![16, 0, 1]] where
    su := ![![15, 0, 0], ![45, -6, 3]]
    hsu := by decide
    w := ![![15225, -16428, 11634], ![-42000, 56124, -12717]]
    hw := by decide
    g := ![![![27155559, 9867372, -11434953], ![141018041, 0, 0]], ![![72237693, 26248626, -30418616], ![375128231, 0, 0]]]
    h := ![![![-59, -952, 704], ![358, 0, 0]], ![![152, 3348, -651], ![-984, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![5075, -5476, 3878]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 3 ![![5, 0, 0], ![-2, 1, 0]]
  ![-56267, 94036, 16761] ![![3, 0, 0], ![14, 1, 1]] where
    su := ![![15, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![-168801, 282108, 50283], ![750360, -982695, 263064]]
    hw := by decide
    g := ![![![-6829034869, 7669611240, 3090895998], ![-28281993614, 0, -1]], ![![1824181056, -2048716965, -825644335], ![7554724518, 0, 0]]]
    h := ![![![69719, -21679, 284937], ![-32223, -234654, 0]], ![![448198, -264600, 1490696], ![-232197, -1227632, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {3} * I5N1 =  Ideal.span {B.equivFun.symm ![-56267, 94036, 16761]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E13RS1 : RelationCertificate Table 3 ![![13, 0, 0], ![-4, 1, 0]]
  ![-1, 2, 1] ![![3, 0, 0], ![16, 0, 1]] where
    su := ![![39, 0, 0], ![-12, 3, 0]]
    hsu := by decide
    w := ![![-3, 6, 3], ![0, -6, -9]]
    hw := by decide
    g := ![![![-21, -4, 4], ![-55, 0, 0]], ![![-10, 1, -2], ![17, 0, 0]]]
    h := ![![![5, -4, 7], ![9, -15, 0]], ![![0, 1, -3], ![3, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {3} * I13N1 =  Ideal.span {B.equivFun.symm ![-1, 2, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS1 


noncomputable def E19RS0 : RelationCertificate Table 3 ![![19, 0, 0], ![9, 1, 0]]
  ![-1, 2, 0] ![![3, 0, 0], ![14, 1, 1]] where
    su := ![![57, 0, 0], ![27, 3, 0]]
    hsu := by decide
    w := ![![-3, 6, 0], ![18, -15, 9]]
    hw := by decide
    g := ![![![915, -8171, -4599], ![35, 0, -1530]], ![![607, -5447, -3066], ![22, 0, -1020]]]
    h := ![![![-80, -527, -318], ![-55, 1007, 0]], ![![422, 2965, 1791], ![370, -5671, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {3} * I19N0 =  Ideal.span {B.equivFun.symm ![-1, 2, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 3 ![![19, 0, 0], ![-5, 1, 0]]
  ![-955703, 1017238, -755358] ![![3, 0, 0], ![14, 1, 1]] where
    su := ![![57, 0, 0], ![-15, 3, 0]]
    hsu := by decide
    w := ![![-2867109, 3051714, -2266074], ![1385250, 4009359, 10928709]]
    hw := by decide
    g := ![![![-2344199358627, 2632743594713, 1061010316637], ![-9708345703133, 0, 1020]], ![![534922454919, -600765314241, -242111763958], ![2215345763586, 0, 0]]]
    h := ![![![-7395982, 16067417, -24280992], ![2791975, 76763915, 0]], ![![2699570, -5760311, 9017727], ![-1013578, -27948985, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {3} * I19N1 =  Ideal.span {B.equivFun.symm ![-955703, 1017238, -755358]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 3 ![![19, 0, 0], ![-4, 1, 0]]
  ![85, -56, 129] ![![3, 0, 0], ![14, 1, 1]] where
    su := ![![57, 0, 0], ![-12, 3, 0]]
    hsu := by decide
    w := ![![255, -168, 387], ![552, -1587, -1356]]
    hw := by decide
    g := ![![![46517, -52375, -21130], ![192623, 0, -26]], ![![-8178, 9191, 3707], ![-33814, 0, 4]]]
    h := ![![![6059, -9550, 19287], ![-1768, -61054, 0]], ![![15094, -23818, 48022], ![-4422, -152145, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {3} * I19N2 =  Ideal.span {B.equivFun.symm ![85, -56, 129]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS2 


noncomputable def E29RS0 : RelationCertificate Table 3 ![![29, 0, 0], ![-12, 1, 0]]
  ![-2562248274027747601, -32444785627420606, -116960771102002003] ![![3, 0, 0], ![16, 0, 1]] where
    su := ![![87, 0, 0], ![-36, 3, 0]]
    hsu := by decide
    w := ![![-7686744822083242803, -97334356882261818, -350882313306006009], ![-40046670130003826064, -507095912847488382, -1828038861788314977]]
    hw := by decide
    g := ![![![-15342501, 368328972, 144153426], ![-33775453, 0, 0]], ![![5407286, -247268471, 6317497], ![30944708, 0, 0]]]
    h := ![![![-136777377118852839217, 952242902728696393685, -521091997796628720695], ![89433497522583809141, 2518591829221855149692, 0]], ![![-712587529507886009560, 4961028145445629418678, -2714803187325096702447], ![465933741363457294268, 13121447181023423599884, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {3} * I29N0 =  Ideal.span {B.equivFun.symm ![-2562248274027747601, -32444785627420606, -116960771102002003]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 3 ![![29, 0, 0], ![-10, 1, 0]]
  ![39125225, 495428, 1785977] ![![3, 0, 0], ![16, 0, 1]] where
    su := ![![87, 0, 0], ![-30, 3, 0]]
    hsu := by decide
    w := ![![117375675, 1486284, 5357931], ![611507868, 7743294, 27913935]]
    hw := by decide
    g := ![![![-35, -314, 833], ![106, 0, 0]], ![![28, -543, -406], ![35, 0, 0]]]
    h := ![![![4569444657, -24213925638, 16198106929], ![-2410633516, -78290552494, 0]], ![![23806051462, -126150550723, 84389460029], ![-12559002229, -407880839366, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {3} * I29N1 =  Ideal.span {B.equivFun.symm ![39125225, 495428, 1785977]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 3 ![![29, 0, 0], ![-7, 1, 0]]
  ![249584295, 3160392, 11392952] ![![3, 0, 0], ![16, 0, 1]] where
    su := ![![87, 0, 0], ![-21, 3, 0]]
    hsu := by decide
    w := ![![748752885, 9481176, 34178856], ![3900878784, 49395360, 178066191]]
    hw := by decide
    g := ![![![123, -1384, -2178], ![-2, 0, 0]], ![![-65, 1943, 384], ![-208, 0, 0]]]
    h := ![![![-5367338213, 17436086672, -17500992032], ![1896808784, 84590026980, 0]], ![![-27962945045, 90839129891, -91177276087], ![9882060201, 440700060320, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {3} * I29N2 =  Ideal.span {B.equivFun.symm ![249584295, 3160392, 11392952]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E29RS2 


noncomputable def E31RS1 : RelationCertificate Table 3 ![![31, 0, 0], ![-14, 1, 0]]
  ![-10629997450893977, -134603657268596, -485235061438629] ![![3, 0, 0], ![14, 1, 1]] where
    su := ![![93, 0, 0], ![-42, 3, 0]]
    hsu := by decide
    w := ![![-31889992352681931, -403810971805788, -1455705184315887], ![-151944092951690472, -1924010866995741, -6935900184289296]]
    hw := by decide
    g := ![![![-1129357, 13950234, -4257322], ![-2039300, 0, -63]], ![![9860, -2649468, 4712827], ![733857, 0, 27]]]
    h := ![![![-482035715821488197, 4151842690716728779, -1921487840947408569], ![351623958458631110, 9927606305718037835, 0]], ![![-2296723022094271680, 19782004484112249797, -9155183352870967842], ![1675358928820388831, 47301395328711984445, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {3} * I31N1 =  Ideal.span {B.equivFun.symm ![-10629997450893977, -134603657268596, -485235061438629]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
