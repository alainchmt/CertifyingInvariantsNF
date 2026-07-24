import IdealArithmetic.Examples.NF3_1_462051_1.PrimesBelow3_1_462051_1F0
import IdealArithmetic.Examples.NF3_1_462051_1.ClassGroupData3_1_462051_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![-23, -3, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-23, -3, 1]] where
    su := ![![2, 0, 0], ![-23, -3, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-23, -3, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 0]]
  ![-41, -15, -2] ![![2, 0, 0], ![-23, -3, 1]] where
    su := ![![4, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-82, -30, -4], ![-452, -166, -22]]
    hw := by decide
    g := ![![![2, -1, 0], ![1, 0, 0]], ![![11, 0, 0], ![-2, 0, 0]]]
    h := ![![![-28, -17, -3], ![15, 4, 0]], ![![-152, -92, -17], ![78, 23, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![-41, -15, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 361 ![![3, 0, 0], ![1, 1, 0]]
  ![-4024, -1468, -195] ![![361, 0, 0], ![-39, 1, 0]] where
    su := ![![1083, 0, 0], ![361, 361, 0]]
    hsu := by decide
    w := ![![-1452664, -529948, -70395], ![126711, 46208, 6137]]
    hw := by decide
    g := ![![![26, -3940, 101], ![242, -36465, 0]], ![![1, -6863, 176], ![15, -63525, 0]]]
    h := ![![![-1098, -1098, -917], ![-730, 2556, 0]], ![![95, 95, 80], ![66, -223, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {361} * I3N0 =  Ideal.span {B.equivFun.symm ![-4024, -1468, -195]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 6859 ![![5, 0, 0], ![0, 1, 0]]
  ![1740, -9, -28] ![![6859, 0, 0], ![-2205, 1, 0]] where
    su := ![![34295, 0, 0], ![0, 6859, 0]]
    hsu := by decide
    w := ![![11934660, -61731, -192052], ![-3841040, 20577, 61731]]
    hw := by decide
    g := ![![![2133, -46305, 21], ![6635, -144036, 0]], ![![642, -8819, 4], ![1997, -27432, 0]]]
    h := ![![![348, -4, -6], ![11, 2, 0]], ![![-112, 0, 1], ![3, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {6859} * I5N0 =  Ideal.span {B.equivFun.symm ![1740, -9, -28]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 260642 ![![5, 0, 0], ![1, 1, 0]]
  ![1116367, 407646, 54189] ![![260642, 0, 0], ![-129559, -3, 1]] where
    su := ![![1303210, 0, 0], ![260642, 260642, 0]]
    hsu := by decide
    w := ![![290972127614, 106249668732, 14123929338], ![-144597404908, -52800335076, -7018828418]]
    hw := by decide
    g := ![![![-2245673, 2427653544, 56224], ![1326751, 4885220934, 0]], ![![-593514, 738032239, 17092], ![582784, 1485158598, 0]]]
    h := ![![![206734, 206734, 152582], ![82697, -708721, 0]], ![![-102736, -102736, -75825], ![-41094, 352196, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {260642} * I5N1 =  Ideal.span {B.equivFun.symm ![1116367, 407646, 54189]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 4952198 ![![5, 0, 0], ![-1, 1, 0]]
  ![-44219, -3118, 207] ![![4952198, 0, 0], ![-1172127, -3, 1]] where
    su := ![![24760990, 0, 0], ![-4952198, 4952198, 0]]
    hsu := by decide
    w := ![![-218981243362, -15440953364, 1025104986], ![51829704268, 3654722124, -242657702]]
    hw := by decide
    g := ![![![1491989271425176, -11901381890646287951, -30461853044755], ![-345926552895761, -50284491217027505748, 0]], ![![2848988785396718, -22725970082515378071, -58167628542124], ![-660554933932144, -96019424761994440236, 0]]]
    h := ![![![-19652, 10537, -311], ![-54041, 1762, 0]], ![![4652, -2494, 73], ![12794, -414, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {4952198} * I5N2 =  Ideal.span {B.equivFun.symm ![-44219, -3118, 207]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 4952198 ![![7, 0, 0], ![-25, -2, 1]]
  ![3112229, 498481, -121242] ![![4952198, 0, 0], ![-1172127, -3, 1]] where
    su := ![![34665386, 0, 0], ![-123804950, -9904396, 4952198]]
    hsu := by decide
    w := ![![15412374229342, 2468576611238, -600414389916], ![-3647793998998, -584280128832, 142108273808]]
    hw := by decide
    g := ![![![20688257, -163108476974, -417480], ![-3724654, -689149113373, 0]], ![![-72853395, 587198094041, 1502946], ![20275730, 2480968821408, 0]]]
    h := ![![![29497, 38003, -716], ![-116230, 0, 0]], ![![-6968, -8994, 169], ![27513, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {4952198} * I7N0 =  Ideal.span {B.equivFun.symm ![3112229, 498481, -121242]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 38 ![![7, 0, 0], ![2, 1, 0]]
  ![-79, 18, -1] ![![38, 0, 0], ![-17, -3, 1]] where
    su := ![![266, 0, 0], ![76, 38, 0]]
    hsu := by decide
    w := ![![-3002, 684, -38], ![4598, 532, -152]]
    hw := by decide
    g := ![![![-2107, -236, 23], ![984, 623, 0]], ![![-915, -103, 9], ![462, 273, 0]]]
    h := ![![![-4087, -2257, -111], ![14265, 776, 0]], ![![6489, 3573, 167], ![-22651, -1173, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {38} * I7N1 =  Ideal.span {B.equivFun.symm ![-79, 18, -1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 38 ![![13, 0, 0], ![-19, -2, 1]]
  ![804, 21, -17] ![![38, 0, 0], ![-17, -3, 1]] where
    su := ![![494, 0, 0], ![-722, -76, 38]]
    hsu := by decide
    w := ![![30552, 798, -646], ![-2508, -2812, 418]]
    hw := by decide
    g := ![![![242, 26, -4], ![-70, -69, 0]], ![![-328, -39, 2], ![192, 98, 0]]]
    h := ![![![37, -1, 0], ![-17, 0, 0]], ![![11, -4, 0], ![11, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {38} * I13N0 =  Ideal.span {B.equivFun.symm ![804, 21, -17]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 4952198 ![![13, 0, 0], ![2, 1, 0]]
  ![-1795436, -36503, 36571] ![![4952198, 0, 0], ![-1172127, -3, 1]] where
    su := ![![64378574, 0, 0], ![9904396, 4952198, 0]]
    hsu := by decide
    w := ![![-8891354568328, -180770083594, 181106833058], ![2104456348892, 42791942918, -42866225888]]
    hw := by decide
    g := ![![![-94589813167323793, 754529212366179867721, 1931234389103774], ![21931208779273775, 3187959003486570225546, 0]], ![![-17575689685172883, 140198725960494720316, 358841773712590], ![4075027817401236, 592353196374586059877, 0]]]
    h := ![![![-14929433766848, -7669115753689, -102199465443], ![97041318586794, 1328593087330, 0]], ![![3533583549082, 1815170061215, 24189150511], ![-22968292856556, -314458965299, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {4952198} * I13N1 =  Ideal.span {B.equivFun.symm ![-1795436, -36503, 36571]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E13RS1 


noncomputable def E19RS1 : RelationCertificate Table 1 ![![19, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![19, 0, 0], ![-1, 1, 0]] where
    su := ![![19, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![19, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![4, -3, 0], ![57, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![4, -3, 0], ![57, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {1} * I19N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 130321 ![![23, 0, 0], ![-8, 1, 0]]
  ![-303512, 20917, 2582] ![![130321, 0, 0], ![-36500, 1, 0]] where
    su := ![![2997383, 0, 0], ![-1042568, 130321, 0]]
    hsu := by decide
    w := ![![-39553987352, 2725924357, 336488822], ![11078588210, -763681060, -94222083]]
    hw := by decide
    g := ![![![528844599586, 265375857734984716, -7270571445191], ![1888207042808, 947508141308743840, 0]], ![![-175540534091, -88086789920848714, 2413336710292], ![-626756655980, -314508453421963888, 0]]]
    h := ![![![-498232, 65709, -409], ![-1394478, 11989, 0]], ![![139566, -18402, 114], ![390626, -3345, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {130321} * I23N1 =  Ideal.span {B.equivFun.symm ![-303512, 20917, 2582]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E23RS1 


noncomputable def E31RS0 : RelationCertificate Table 6859 ![![31, 0, 0], ![0, 1, 0]]
  ![2418, 768, 103] ![![6859, 0, 0], ![-2205, 1, 0]] where
    su := ![![212629, 0, 0], ![0, 6859, 0]]
    hsu := by decide
    w := ![![16585062, 5267712, 706477], ![-5315725, -1687314, -226347]]
    hw := by decide
    g := ![![![2205147, 51875631618, -23526364], ![6859457, 161367330670, 0]], ![![1838265, 43224651651, -19603017], ![5718213, 134457093602, 0]]]
    h := ![![![78, 24, 0], ![24, 103, 0]], ![![-25, -8, 0], ![2, -33, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {6859} * I31N0 =  Ideal.span {B.equivFun.symm ![2418, 768, 103]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 722 ![![31, 0, 0], ![6, 1, 0]]
  ![-353, -10, 9] ![![722, 0, 0], ![-321, -3, 1]] where
    su := ![![22382, 0, 0], ![4332, 722, 0]]
    hsu := by decide
    w := ![![-254866, -7220, 6498], ![107578, 4332, -2888]]
    hw := by decide
    g := ![![![-9063573763, 19908476402, 203923215], ![3947210668, 50393257299, 0]], ![![-1925482645, 4229394137, 43321831], ![838552844, 10705638275, 0]]]
    h := ![![![-1051433, -184431, -1532], ![5432345, 47501, 0]], ![![443885, 77857, 646], ![-2293381, -20030, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {722} * I31N1 =  Ideal.span {B.equivFun.symm ![-353, -10, 9]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 38 ![![31, 0, 0], ![-6, 1, 0]]
  ![179, 66, 9] ![![38, 0, 0], ![-17, -3, 1]] where
    su := ![![1178, 0, 0], ![-228, 38, 0]]
    hsu := by decide
    w := ![![6802, 2508, 342], ![3002, 1140, 152]]
    hw := by decide
    g := ![![![696, 78, -8], ![-317, -204, 0]], ![![-42, -4, 0], ![48, 15, 0]]]
    h := ![![![42911, -7393, 41], ![221677, -1262, 0]], ![![18943, -3263, 18], ![97859, -554, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {38} * I31N2 =  Ideal.span {B.equivFun.symm ![179, 66, 9]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E31RS2 
