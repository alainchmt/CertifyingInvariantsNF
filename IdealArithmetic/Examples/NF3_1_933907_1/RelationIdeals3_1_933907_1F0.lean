import IdealArithmetic.Examples.NF3_1_933907_1.PrimesBelow3_1_933907_1F0
import IdealArithmetic.Examples.NF3_1_933907_1.ClassGroupData3_1_933907_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 81 ![![2, 0, 0], ![0, 1, 0]]
  ![-6958266, 1399001, -160690] ![![81, 0, 0], ![-89, 37, 1]] where
    su := ![![162, 0, 0], ![0, 81, 0]]
    hsu := by decide
    w := ![![-563619546, 113319081, -13015890], ![3986788410, -801567657, 92068488]]
    hw := by decide
    g := ![![![-339, -215, -2], ![436, 0, 0]], ![![-638, -484, -23], ![580, 0, 0]]]
    h := ![![![-3479133, 559600, -80345], ![279801, 0, 0]], ![![24609805, -3958359, 568324], ![-1979179, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {81} * I2N0 =  Ideal.span {B.equivFun.symm ![-6958266, 1399001, -160690]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 9 ![![2, 0, 0], ![1, 1, 0]]
  ![130120267, -26161458, 3004919] ![![9, 0, 0], ![-80, 1, 1]] where
    su := ![![18, 0, 0], ![9, 9, 0]]
    hsu := by decide
    w := ![![1171082403, -235453122, 27044271], ![8183263509, -1645294077, 188979354]]
    hw := by decide
    g := ![![![884, -2952, 7], ![-7643, 0, 0]], ![![4302, -14315, 123], ![-39108, 0, 0]]]
    h := ![![![860634739089, -296475152811, -1326892203], ![282079793139, 0, 2656789325]], ![![6013924243860, -2071702463556, -9272027756], ![1971110890153, 0, 18565053218]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {9} * I2N1 =  Ideal.span {B.equivFun.symm ![130120267, -26161458, 3004919]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![-80, 4, 1]]
  ![1, 0, 0] ![![3, 0, 0], ![-80, 4, 1]] where
    su := ![![3, 0, 0], ![-80, 4, 1]]
    hsu := by decide
    w := ![![3, 0, 0], ![-80, 4, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 243 ![![3, 0, 0], ![1, 1, 0]]
  ![-359, 7, 3] ![![243, 0, 0], ![-89, 37, 1]] where
    su := ![![729, 0, 0], ![243, 243, 0]]
    hsu := by decide
    w := ![![-87237, 1701, 729], ![-55890, -972, 243]]
    hw := by decide
    g := ![![![55, -19, 0], ![101, 0, 0]], ![![-34, -7, -3], ![176, 0, 0]]]
    h := ![![![32078, 32170, -29], ![-96593, 45, 0]], ![![19802, 19858, -19], ![-59636, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {243} * I3N1 =  Ideal.span {B.equivFun.symm ![-359, 7, 3]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0, 0], ![-81, 7, 1]]
  ![6548, -296, -73] ![![3, 0, 0], ![-80, 4, 1]] where
    su := ![![15, 0, 0], ![-243, 21, 3]]
    hsu := by decide
    w := ![![19644, -888, -219], ![-108009, 7413, 1479]]
    hw := by decide
    g := ![![![-89, -3543, 837], ![-884, 0, 0]], ![![1186, 30154, -7134], ![7545, 0, 0]]]
    h := ![![![46, 50, 1], ![-78, 0, 0]], ![![-24, -126, 10], ![443, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![6548, -296, -73]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 243 ![![5, 0, 0], ![1, 1, 0]]
  ![478, -96, 11] ![![243, 0, 0], ![-89, 37, 1]] where
    su := ![![1215, 0, 0], ![243, 243, 0]]
    hsu := by decide
    w := ![![116154, -23328, 2673], ![-272889, 54918, -6318]]
    hw := by decide
    g := ![![![-2, -10, 0], ![73, 0, 0]], ![![-6, -17, 0], ![123, 0, 0]]]
    h := ![![![-20446, -20548, 15], ![102708, -32, 0]], ![![48048, 48285, -38], ![-241363, 82, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {243} * I5N1 =  Ideal.span {B.equivFun.symm ![478, -96, 11]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 27 ![![7, 0, 0], ![-82, 4, 1]]
  ![-1916695, 385363, -44263] ![![27, 0, 0], ![-89, 10, 1]] where
    su := ![![189, 0, 0], ![-2214, 108, 27]]
    hsu := by decide
    w := ![![-51750765, 10404801, -1195101], ![197078022, -39623715, 4551201]]
    hw := by decide
    g := ![![![-95, -58, 8], ![577, 0, 0]], ![![-400, -347, -6], ![1229, 0, 0]]]
    h := ![![![-39, 41697, -9662], ![23371, 0, 0]], ![![310, -158799, 36793], ![-88988, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {27} * I7N0 =  Ideal.span {B.equivFun.symm ![-1916695, 385363, -44263]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 27 ![![7, 0, 0], ![-1, 1, 0]]
  ![242909, -23298, -4046] ![![27, 0, 0], ![-89, 10, 1]] where
    su := ![![189, 0, 0], ![-27, 27, 0]]
    hsu := by decide
    w := ![![6558543, -629046, -109242], ![24929289, -1664712, -336339]]
    hw := by decide
    g := ![![![-7042435, 9160770, -3160224], ![26489906, 0, 0]], ![![18524156, -24096007, 8312481], ![-69677581, 0, 0]]]
    h := ![![![67912, -36539, -536], ![232475, -147, 0]], ![![258284, -135191, -1647], ![884681, -464, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {27} * I7N1 =  Ideal.span {B.equivFun.symm ![242909, -23298, -4046]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 81 ![![13, 0, 0], ![0, 1, 0]]
  ![4992, -146, -47] ![![81, 0, 0], ![-89, 37, 1]] where
    su := ![![1053, 0, 0], ![0, 81, 0]]
    hsu := by decide
    w := ![![404352, -11826, -3807], ![959283, -10530, -7128]]
    hw := by decide
    g := ![![![-2861, -181, -187], ![3206, 0, 0]], ![![3963, 188, 249], ![-4175, 0, 0]]]
    h := ![![![384, 3751, 7567], ![300, -49209, 0]], ![![911, 7035, 14168], ![551, -92136, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {81} * I13N0 =  Ideal.span {B.equivFun.symm ![4992, -146, -47]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 81 ![![13, 0, 0], ![-1, 1, 0]]
  ![10609, -2133, 245] ![![81, 0, 0], ![-89, 37, 1]] where
    su := ![![1053, 0, 0], ![-81, 81, 0]]
    hsu := by decide
    w := ![![859329, -172773, 19845], ![-6078564, 1222128, -140373]]
    hw := by decide
    g := ![![![144, 34, -1], ![-86, 0, 0]], ![![132, -13, -1], ![28, 0, 0]]]
    h := ![![![1622, -970, 17], ![10477, 12, 0]], ![![-11464, 6852, -131], ![-73988, -15, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {81} * I13N1 =  Ideal.span {B.equivFun.symm ![10609, -2133, 245]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 9 ![![17, 0, 0], ![7, 1, 0]]
  ![558394, -30064, -6749] ![![9, 0, 0], ![-80, 1, 1]] where
    su := ![![153, 0, 0], ![63, 9, 0]]
    hsu := by decide
    w := ![![5025546, -270576, -60741], ![-19458891, 1170702, 248553]]
    hw := by decide
    g := ![![![-2253273, 40085537, -7533397], ![23646328, 0, 0]], ![![1380187, -24552207, 4614170], ![-14483259, 0, 0]]]
    h := ![![![-7108438, -992176, 7047], ![17343120, -63274, 0]], ![![27563904, 3848075, -27237], ![-67249781, 245323, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {9} * I17N1 =  Ideal.span {B.equivFun.symm ![558394, -30064, -6749]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS1 


noncomputable def E29RS0 : RelationCertificate Table 81 ![![29, 0, 0], ![0, 1, 0]]
  ![53824, 2014, -117] ![![81, 0, 0], ![-89, 37, 1]] where
    su := ![![2349, 0, 0], ![0, 81, 0]]
    hsu := by decide
    w := ![![4359744, 163134, -9477], ![-3088935, 1660014, 199584]]
    hw := by decide
    g := ![![![3198521, 167245, 203447], ![-3435382, 0, 0]], ![![-1920424, -100443, -122156], ![2062754, 0, 0]]]
    h := ![![![1856, 9478, 18837], ![347, -273195, 0]], ![![-1315, -197454, -396704], ![-6780, 5753440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {81} * I29N0 =  Ideal.span {B.equivFun.symm ![53824, 2014, -117]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 81 ![![29, 0, 0], ![1, 1, 0]]
  ![109565, -7563, -1505] ![![81, 0, 0], ![-89, 37, 1]] where
    su := ![![2349, 0, 0], ![81, 81, 0]]
    hsu := by decide
    w := ![![8874765, -612603, -121905], ![37370322, -2385450, -492237]]
    hw := by decide
    g := ![![![-711771, -37259, -45280], ![764657, 0, 0]], ![![402914, 21049, 25625], ![-432672, 0, 0]]]
    h := ![![![-37202, -41222, -33], ![1188423, -274, 0]], ![![-155734, -172578, -129], ![4977648, -1168, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {81} * I29N1 =  Ideal.span {B.equivFun.symm ![109565, -7563, -1505]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 81 ![![29, 0, 0], ![-2, 1, 0]]
  ![1262974730, -253928624, 29166377] ![![81, 0, 0], ![-89, 37, 1]] where
    su := ![![2349, 0, 0], ![-162, 81, 0]]
    hsu := by decide
    w := ![![102300953130, -20568218544, 2362476537], ![-723630429891, 145490226354, -16711084890]]
    hw := by decide
    g := ![![![-130098, -41202, 1820], ![124277, 0, 0]], ![![-33558, -10859, 446], ![32094, 0, 0]]]
    h := ![![![44786338, 609094196, -1235930459], ![17914536, 17935574844, 0]], ![![-316798191, -4308455410, 8742410134], ![-126719264, -126868101788, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {81} * I29N2 =  Ideal.span {B.equivFun.symm ![1262974730, -253928624, 29166377]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E29RS2 


noncomputable def E31RS1 : RelationCertificate Table 27 ![![31, 0, 0], ![-4, 1, 0]]
  ![7232, -1454, 167] ![![27, 0, 0], ![-89, 10, 1]] where
    su := ![![837, 0, 0], ![-108, 27, 0]]
    hsu := by decide
    w := ![![195264, -39258, 4509], ![-743553, 149499, -17172]]
    hw := by decide
    g := ![![![-16, -65, 0], ![293, 0, 0]], ![![-12, -9, 0], ![38, 0, 0]]]
    h := ![![![117544, -29389, 15], ![909158, -149, 0]], ![![-447565, 111913, -64], ![-3461744, 674, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {27} * I31N1 =  Ideal.span {B.equivFun.symm ![7232, -1454, 167]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E31RS1 
