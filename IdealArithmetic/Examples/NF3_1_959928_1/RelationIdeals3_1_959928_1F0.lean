import IdealArithmetic.Examples.NF3_1_959928_1.PrimesBelow3_1_959928_1F0
import IdealArithmetic.Examples.NF3_1_959928_1.ClassGroupData3_1_959928_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![-31, -2, 1]]
  ![74, 117, -22] ![![2, 0, 0], ![-31, -1, 1]] where
    su := ![![4, 0, 0], ![-62, -4, 2]]
    hsu := by decide
    w := ![![148, 234, -44], ![34606, 148, -534]]
    hw := by decide
    g := ![![![168, -22714, -6897], ![5446, 0, 0]], ![![1021, -145447, -44162], ![34869, 0, 0]]]
    h := ![![![213, -83, 674], ![-2774, -351, 0]], ![![230, -603, 575], ![-2305, -222, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![74, 117, -22]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 500 ![![3, 0, 0], ![0, 1, 0]]
  ![12627, 1459, -446] ![![500, 0, 0], ![216, 2, 0]] where
    su := ![![1500, 0, 0], ![0, 500, 0]]
    hsu := by decide
    w := ![![6313500, 729500, -223000], ![2508000, 300500, -90500]]
    hw := by decide
    g := ![![![2553, -1443207, -26453], ![-4427, 3310592, 0]], ![![3224, -761769, -13863], ![-1439, 1748992, 0]]]
    h := ![![![4209, 201003, 445554], ![67004, -668554, 0]], ![![1672, 81576, 180819], ![27192, -271319, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {500} * I3N0 =  Ideal.span {B.equivFun.symm ![12627, 1459, -446]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 50 ![![3, 0, 0], ![-1, 1, 0]]
  ![227, -41, 4] ![![50, 0, 0], ![8, 1, 0]] where
    su := ![![150, 0, 0], ![-50, 50, 0]]
    hsu := by decide
    w := ![![11350, -2050, 200], ![2800, 50, -50]]
    hw := by decide
    g := ![![![27, -1555, -346], ![18, 8687, 0]], ![![101, 1596, 353], ![65, -8687, 0]]]
    h := ![![![136, -74, 0], ![181, 2, 0]], ![![34, -15, -1], ![46, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {50} * I3N1 =  Ideal.span {B.equivFun.symm ![227, -41, 4]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 500 ![![5, 0, 0], ![-32, -4, 1]]
  ![5707142, 362714, -148541] ![![500, 0, 0], ![216, 2, 0]] where
    su := ![![2500, 0, 0], ![-16000, -2000, 500]]
    hsu := by decide
    w := ![![2853571000, 181357000, -74270500], ![1159660500, 76226000, -30634000]]
    hw := by decide
    g := ![![![-11471780, -20177984, -971176], ![-5036355, 36874764, 0]], ![![28732571, 124348366, 3792392], ![12909930, -261560826, 0]]]
    h := ![![![35374, -65714, 4856], ![-172821, 0, 0]], ![![14277, -25708, 1796], ![-70248, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {500} * I5N0 =  Ideal.span {B.equivFun.symm ![5707142, 362714, -148541]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 2 ![![5, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![10, 0, 0], ![-4, 2, 0]] where
    su := ![![10, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![10, 0, 0], ![-4, 2, 0]]
    hw := by decide
    g := ![![![1, 2, -4], ![0, 10, 0]], ![![0, -1, 2], ![1, -5, 0]]]
    h := ![![![1, 2, -4], ![0, 10, 0]], ![![0, -1, 2], ![1, -5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {2} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 500 ![![7, 0, 0], ![-34, -3, 1]]
  ![-21837169, 5499527, -662813] ![![500, 0, 0], ![-142, 1, 0]] where
    su := ![![3500, 0, 0], ![-17000, -1500, 500]]
    hsu := by decide
    w := ![![-10918584500, 2749763500, -331406500], ![2937826000, -829085500, 105118500]]
    hw := by decide
    g := ![![![-155666079908786953, -296164582026090417568, 4200931606575658570], ![-548119997358084999, -1050232901652078465768, 0]], ![![754007571811027217, 1434547194187977613446, -20348262469497908909], ![2654956237981623653, 5087065617377254849830, 0]]]
    h := ![![![-220061, 1041488, -179968], ![596963, 0, 0]], ![![61488, -305519, 52913], ![-160154, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {500} * I7N0 =  Ideal.span {B.equivFun.symm ![-21837169, 5499527, -662813]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 10 ![![7, 0, 0], ![-1, 1, 0]]
  ![-40685227, -12284529, -2015789] ![![10, 0, 0], ![-27, -2, 1]] where
    su := ![![70, 0, 0], ![-10, 10, 0]]
    hsu := by decide
    w := ![![-406852270, -122845290, -20157890], ![-683782770, -206461900, -33878680]]
    hw := by decide
    g := ![![![-11956, -944, -1584], ![32369, 3762, 0]], ![![2254, -209, 300], ![-5963, -495, 0]]]
    h := ![![![-11465242, 3898134, -266237], ![-39571467, -76065, 0]], ![![-19269242, 6551461, -447456], ![-66506417, -127838, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {10} * I7N1 =  Ideal.span {B.equivFun.symm ![-40685227, -12284529, -2015789]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 100 ![![13, 0, 0], ![-32, -1, 1]]
  ![10993081796719, 3319259645073, 544662891063] ![![100, 0, 0], ![-54, -4, 2]] where
    su := ![![1300, 0, 0], ![-3200, -100, 100]]
    hsu := by decide
    w := ![![1099308179671900, 331925964507300, 54466289106300], ![369513972345600, 111571335443300, 18307927857500]]
    hw := by decide
    g := ![![![95535115, 7447571, -969538], ![-51906223, -25081122, 0]], ![![-235695701, -18411242, 2399799], ![128060177, 61858104, 0]]]
    h := ![![![115289983339, 232504799589, 64720010883], ![-296697250416, 0, 0]], ![![38752790624, 78152581482, 21754544134], ![-99729795167, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {100} * I13N0 =  Ideal.span {B.equivFun.symm ![10993081796719, 3319259645073, 544662891063]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 100 ![![13, 0, 0], ![2, 1, 0]]
  ![1480181, 446927, 73337] ![![100, 0, 0], ![-54, -4, 2]] where
    su := ![![1300, 0, 0], ![200, 100, 0]]
    hsu := by decide
    w := ![![148018100, 44692700, 7333700], ![49753800, 15022700, 2465100]]
    hw := by decide
    g := ![![![148845353, 11634272, -1512902], ![-80872093, -39129398, 0]], ![![32884594, 2570363, -334248], ![-17867126, -8644867, 0]]]
    h := ![![![226613337, 120568024, 4861579], ![-1472246600, -31563595, 0]], ![![76172270, 40526916, 1634137], ![-494870986, -10609565, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {100} * I13N1 =  Ideal.span {B.equivFun.symm ![1480181, 446927, 73337]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 500 ![![17, 0, 0], ![-2, 1, 0]]
  ![-2653, -801, -131] ![![500, 0, 0], ![-142, 1, 0]] where
    su := ![![8500, 0, 0], ![-1000, 500, 0]]
    hsu := by decide
    w := ![![-1326500, -400500, -65500], ![344500, 104000, 17000]]
    hw := by decide
    g := ![![![-1696922765, -3228503273745, 45794542183], ![-5975080167, -11448635545764, 0]], ![![249542050, 474769494804, -6734344002], ![878669194, 1683586000505, 0]]]
    h := ![![![-161, -1246, 2395], ![-42, -20423, 0]], ![![43, 323, -622], ![21, 5304, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {500} * I17N1 =  Ideal.span {B.equivFun.symm ![-2653, -801, -131]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E17RS1 


noncomputable def E23RS0 : RelationCertificate Table 100 ![![23, 0, 0], ![-10, 1, 0]]
  ![228293, 68931, 11311] ![![100, 0, 0], ![-54, -4, 2]] where
    su := ![![2300, 0, 0], ![-1000, 100, 0]]
    hsu := by decide
    w := ![![22829300, 6893100, 1131100], ![7673700, 2317000, 380200]]
    hw := by decide
    g := ![![![7402, 590, -76], ![-3963, -1972, 0]], ![![-3071, -249, 31], ![1724, 833, 0]]]
    h := ![![![102872141, -10292770, 2613], ![236583095, -24394, 0]], ![![34578809, -3459747, 878], ![79523587, -8196, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {100} * I23N0 =  Ideal.span {B.equivFun.symm ![228293, 68931, 11311]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E23RS0 


noncomputable def E29RS0 : RelationCertificate Table 2 ![![29, 0, 0], ![14, 1, 0]]
  ![219230125, 66194514, 10861969] ![![2, 0, 0], ![-31, -1, 1]] where
    su := ![![58, 0, 0], ![28, 2, 0]]
    hsu := by decide
    w := ![![438460250, 132389028, 21723938], ![5479650008, 1654529774, 271494570]]
    hw := by decide
    g := ![![![742, -15034, 3047], ![-2021, 0, 0]], ![![299, -3824, 1063], ![-2094, 0, 0]]]
    h := ![![![-75563185, 6051192321, 807687497], ![172183035, -11706037722, 0]], ![![-944349658, 75624679892, 10094061661], ![2151854649, -146296020442, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {2} * I29N0 =  Ideal.span {B.equivFun.symm ![219230125, 66194514, 10861969]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 500 ![![29, 0, 0], ![-8, 1, 0]]
  ![108743, -3669, -939] ![![500, 0, 0], ![-142, 1, 0]] where
    su := ![![14500, 0, 0], ![-4000, 500, 0]]
    hsu := by decide
    w := ![![54371500, -1834500, -469500], ![-15672500, 581000, 126000]]
    hw := by decide
    g := ![![![-963410, -1809349422, 25663902], ![-3344949, -6416142030, 0]], ![![181499, 348579506, -4944513], ![645918, 1236104199, 0]]]
    h := ![![![121512139, -15190927, 611], ![440467911, -9329, 0]], ![![-35032125, 4379574, -178], ![-126987535, 2707, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {500} * I29N1 =  Ideal.span {B.equivFun.symm ![108743, -3669, -939]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 10 ![![29, 0, 0], ![-7, 1, 0]]
  ![-15471538, -357511, 290819] ![![10, 0, 0], ![-4, 2, 0]] where
    su := ![![290, 0, 0], ![-70, 10, 0]]
    hsu := by decide
    w := ![![-154715380, -3575110, 2908190], ![204969100, -2309430, -2593320]]
    hw := by decide
    g := ![![![-572308863666, -231391641090, -31975331049], ![182645217251, 138, 0]], ![![-102390168434, -41397627428, -5720616483], ![32676541890, -32, 0]]]
    h := ![![![-1004316, -63595387, 21226801], ![-1950518, -307643205, 0]], ![![1336069, 84955846, -28360178], ![2607013, 411092915, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {10} * I29N2 =  Ideal.span {B.equivFun.symm ![-15471538, -357511, 290819]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E29RS2 
