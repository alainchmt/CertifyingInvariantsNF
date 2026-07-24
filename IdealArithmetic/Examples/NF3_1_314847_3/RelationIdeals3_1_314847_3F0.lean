import IdealArithmetic.Examples.NF3_1_314847_3.PrimesBelow3_1_314847_3F0
import IdealArithmetic.Examples.NF3_1_314847_3.ClassGroupData3_1_314847_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![98, 14, -27], ![4, 14, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![98, 14, -27], ![4, 14, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![-6, -1, 1]]
  ![-19, -3, 2] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![4, 0, 0], ![-12, -2, 2]]
    hsu := by decide
    w := ![![-38, -6, 4], ![216, 2, -10]]
    hw := by decide
    g := ![![![-1085, -65, -4], ![-32, 0, 21]], ![![4602, 321, 65], ![161, 0, -77]]]
    h := ![![![-413, 335, -364], ![901, 57, 0]], ![![2373, -1908, 2068], ![-5113, -324, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![-19, -3, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E2RS2 : RelationCertificate Table 2 ![![2, 0, 0], ![-6, 0, 1]]
  ![300761441, 50420871, 24294662] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![4, 0, 0], ![-12, 0, 2]]
    hsu := by decide
    w := ![![601522882, 100841742, 48589324], ![2797549224, 468992528, 225978146]]
    hw := by decide
    g := ![![![18292, -1211, -82], ![-605, 0, -21]], ![![-146895, -3267, 7589], ![-1632, 0, 63]]]
    h := ![![![6193061956, 1378636920, 7802305941], ![-14678032897, -902284323, 0]], ![![28802554629, 6411733886, 36286790717], ![-68264268525, -4196323836, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {2} * I2N2 =  Ideal.span {B.equivFun.symm ![300761441, 50420871, 24294662]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS2 


noncomputable def E3RS0 : RelationCertificate Table 50 ![![3, 0, 0], ![-1, 1, 0]]
  ![-550601, -92305, -44476] ![![50, 0, 0], ![4, 1, 0]] where
    su := ![![150, 0, 0], ![-50, 50, 0]]
    hsu := by decide
    w := ![![-27530050, -4615250, -2223800], ![-7323850, -1227800, -591600]]
    hw := by decide
    g := ![![![-1342, -2090, -2792], ![-101, 34874, 0]], ![![-289, -290, -398], ![-24, 4982, 0]]]
    h := ![![![-3784331, 3570029, -8850724], ![2451456, 6626924, 0]], ![![-1006750, 949739, -2354568], ![652163, 1762968, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {50} * I3N0 =  Ideal.span {B.equivFun.symm ![-550601, -92305, -44476]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 25 ![![5, 0, 0], ![-4, 0, 1]]
  ![-4231, 470, -6] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![125, 0, 0], ![-100, 0, 25]]
    hsu := by decide
    w := ![![-105775, 11750, -150], ![-16650, -2875, 1850]]
    hw := by decide
    g := ![![![14385, 17684, 23258], ![3024, -143658, 0]], ![![3868, -11670, -17427], ![155, 115551, 0]]]
    h := ![![![-523, 94, -82], ![404, 0, 0]], ![![-78, -23, 1], ![69, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {25} * I5N0 =  Ideal.span {B.equivFun.symm ![-4231, 470, -6]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![5, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 50 ![![7, 0, 0], ![-7, -3, 1]]
  ![21, 5, -4] ![![50, 0, 0], ![4, 1, 0]] where
    su := ![![350, 0, 0], ![-350, -150, 50]]
    hsu := by decide
    w := ![![1050, 250, -200], ![-350, 0, 0]]
    hw := by decide
    g := ![![![-4, -1, 0], ![49, 0, 0]], ![![29128, 44011, 58767], ![3218, -734586, -1]]]
    h := ![![![6, 2, -1], ![3, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {50} * I7N0 =  Ideal.span {B.equivFun.symm ![21, 5, -4]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 20 ![![7, 0, 0], ![-3, 1, 0]]
  ![-147, -25, -12] ![![20, 0, 0], ![-6, 1, 0]] where
    su := ![![140, 0, 0], ![-60, 20, 0]]
    hsu := by decide
    w := ![![-2940, -500, -240], ![-500, -80, -40]]
    hw := by decide
    g := ![![![-12123717, 48494437, -27884303], ![6061855, 139421542, 22]], ![![4408715, -17634695, 10139950], ![-2204342, -50699760, -8]]]
    h := ![![![-7984, 20456, -21368], ![6347, 37391, 0]], ![![-1365, 3498, -3654], ![1086, 6394, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {20} * I7N1 =  Ideal.span {B.equivFun.symm ![-147, -25, -12]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 4 ![![11, 0, 0], ![-7, -1, 1]]
  ![-8369, -1403, -676] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![44, 0, 0], ![-28, -4, 4]]
    hsu := by decide
    w := ![![-33476, -5612, -2704], ![-94580, -15856, -7640]]
    hw := by decide
    g := ![![![-7796, 180, -264], ![-3851, 0, 350]], ![![3942, -94, 129], ![1948, 0, -175]]]
    h := ![![![-540, -96, -93], ![347, 0, 0]], ![![-1524, -271, -263], ![983, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {4} * I11N0 =  Ideal.span {B.equivFun.symm ![-8369, -1403, -676]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 2 ![![11, 0, 0], ![3, 1, 0]]
  ![495, 83, 40] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![22, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![990, 166, 80], ![4606, 772, 372]]
    hw := by decide
    g := ![![![23828, 1553, 214], ![777, 0, -430]], ![![9527, 616, 88], ![310, 0, -172]]]
    h := ![![![-587, -663, -1376], ![-212, 3794, 0]], ![![-2723, -3082, -6402], ![-1016, 17652, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![495, 83, 40]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 5 ![![13, 0, 0], ![0, 1, 0]]
  ![-13461, -5800, 2874] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![65, 0, 0], ![0, 5, 0]]
    hsu := by decide
    w := ![![-67305, -29000, 14370], ![320875, 24005, -23200]]
    hw := by decide
    g := ![![![-31468430, -6444251, -2622818], ![5004841, 41, 0]], ![![-22515785, -4610900, -1876614], ![3580981, 0, 0]]]
    h := ![![![121149, -61177, 244590], ![-4698, -794199, 0]], ![![-577575, 289909, -1165380], ![22309, 3786325, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {5} * I13N0 =  Ideal.span {B.equivFun.symm ![-13461, -5800, 2874]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS0 


noncomputable def E17RS1 : RelationCertificate Table 100 ![![17, 0, 0], ![0, 1, 0]]
  ![-28861939987, -4838532985, -2331386212] ![![100, 0, 0], ![-46, 1, 0]] where
    su := ![![1700, 0, 0], ![0, 100, 0]]
    hsu := by decide
    w := ![![-2886193998700, -483853298500, -233138621200], ![1059188303900, 177566634400, 85558247600]]
    hw := by decide
    g := ![![![488599496542678031444, -15593554335848600466606, 1327434999912023860888], ![-380691311768117899057, -33185874997800599295312, -244764]], ![![35971, -1278063, 109022], ![-29273, -2719808, 0]]]
    h := ![![![5743526057413, -2862989989127, 11490310496812], ![-168411175830, -48834402458004, 0]], ![![-2107784724761, 1050672793316, -4216765225028], ![61804281960, 17921466101988, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {100} * I17N1 =  Ideal.span {B.equivFun.symm ![-28861939987, -4838532985, -2331386212]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 100 ![![19, 0, 0], ![-3, 1, 0]]
  ![-71, -5, 4] ![![100, 0, 0], ![-46, 1, 0]] where
    su := ![![1900, 0, 0], ![-300, 100, 0]]
    hsu := by decide
    w := ![![-7100, -500, 400], ![3700, 200, -200]]
    hw := by decide
    g := ![![![98045933605, -3129109495664, 266372104939], ![-76392224357, -6659305188138, -227970]], ![![-13072836442, 417216045675, -35516403774], ![10185665269, 887910436305, 30396]]]
    h := ![![![253, -529, 532], ![-58, -2526, 0]], ![![-131, 276, -278], ![38, 1320, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {100} * I19N1 =  Ideal.span {B.equivFun.symm ![-71, -5, 4]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 50 ![![23, 0, 0], ![-11, 1, 0]]
  ![-9363, 1985, -388] ![![50, 0, 0], ![4, 1, 0]] where
    su := ![![1150, 0, 0], ![-550, 50, 0]]
    hsu := by decide
    w := ![![-468150, 99250, -19400], ![-76550, -6900, 6000]]
    hw := by decide
    g := ![![![322070514, 486681686, 649852898], ![35499279, -8123149546, 27588]], ![![-107345059, -162225267, -216616684], ![-11832094, 2707716636, -9196]]]
    h := ![![![1463014, -12264850, 4106164], ![-1232945, -23610540, 0]], ![![206550, -1731583, 579720], ![-174049, -3333360, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {50} * I23N0 =  Ideal.span {B.equivFun.symm ![-9363, 1985, -388]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 50 ![![23, 0, 0], ![-6, 1, 0]]
  ![83, 15, 8] ![![50, 0, 0], ![4, 1, 0]] where
    su := ![![1150, 0, 0], ![-300, 50, 0]]
    hsu := by decide
    w := ![![4150, 750, 400], ![1250, 200, 100]]
    hw := by decide
    g := ![![![995098069953, 1503615003630, 2007744803575], ![109680145689, -25096809998708, -36784]], ![![-248774519772, -375903754353, -501936205493], ![-27420036623, 6274202557168, 9196]]]
    h := ![![![129, -473, 272], ![-40, -1562, 0]], ![![41, -143, 82], ![-4, -471, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {50} * I23N1 =  Ideal.span {B.equivFun.symm ![83, 15, 8]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E23RS1 


noncomputable def E31RS0 : RelationCertificate Table 5 ![![31, 0, 0], ![2, 1, 0]]
  ![-423, -10, 22] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![155, 0, 0], ![10, 5, 0]]
    hsu := by decide
    w := ![![-2115, -50, 110], ![2845, -205, -40]]
    hw := by decide
    g := ![![![-2401, -438, -294], ![396, 122, 0]], ![![-862, -173, -78], ![138, 8, 0]]]
    h := ![![![-25, -6, -22], ![0, 176, 0]], ![![21, 0, 8], ![23, -64, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {5} * I31N0 =  Ideal.span {B.equivFun.symm ![-423, -10, 22]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 5 ![![31, 0, 0], ![5, 1, 0]]
  ![2590693063, 434314320, 209268888] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![155, 0, 0], ![25, 5, 0]]
    hsu := by decide
    w := ![![12953465315, 2171571600, 1046344440], ![21506782145, 3605484415, 1737257280]]
    hw := by decide
    g := ![![![92729, 6272, -5124], ![-17290, -141, 0]], ![![-2866, 1756, -624], ![927, -24, 0]]]
    h := ![![![8088053918, 16556767685, 16608818288], ![1838614125, -128666024510, 0]], ![![13428685637, 27489385039, 27575805232], ![3052671410, -213625627684, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {5} * I31N1 =  Ideal.span {B.equivFun.symm ![2590693063, 434314320, 209268888]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 5 ![![31, 0, 0], ![-7, 1, 0]]
  ![-416921347, -69894390, -33677732] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![155, 0, 0], ![-35, 5, 0]]
    hsu := by decide
    w := ![![-2084606735, -349471950, -168388660], ![-3461095685, -580232155, -279577560]]
    hw := by decide
    g := ![![![-26113, 7626, -10532], ![6748, 12368, 0]], ![![3448, -2338, 1880], ![-1157, -1546, 0]]]
    h := ![![![-82476423370, 356074465185, -178525091164], ![30109981579, 1383561037088, 0]], ![![-136936520562, 591194384196, -296407189096], ![49991936421, 2297141736616, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {5} * I31N2 =  Ideal.span {B.equivFun.symm ![-416921347, -69894390, -33677732]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS2 
