import IdealArithmetic.Examples.NF3_1_866700_5.PrimesBelow3_1_866700_5F0
import IdealArithmetic.Examples.NF3_1_866700_5.ClassGroupData3_1_866700_5

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 637 ![![2, 0, 0], ![0, 1, 0]]
  ![-56, 21, -26] ![![637, 0, 0], ![-155, 1, 0]] where
    su := ![![1274, 0, 0], ![0, 637, 0]]
    hsu := by decide
    w := ![![-35672, 13377, -16562], ![3822, -3185, 4459]]
    hw := by decide
    g := ![![![-6760527, -176158131, 15369319], ![1368555, -753096382, 20]], ![![-1689911, -44034754, 3841913], ![342246, -188253666, 5]]]
    h := ![![![99266, -79427, -215150], ![-39713, 33098, 0]], ![![-26730, 21384, 57925], ![10693, -8911, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {637} * I2N0 =  Ideal.span {B.equivFun.symm ![-56, 21, -26]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 1183 ![![3, 0, 0], ![1, 1, 0]]
  ![-37345, -4662, -3029] ![![1183, 0, 0], ![-64, 1, 0]] where
    su := ![![3549, 0, 0], ![1183, 1183, 0]]
    hsu := by decide
    w := ![![-44179135, -5515146, -3583307], ![1866774, 233051, 151424]]
    hw := by decide
    g := ![![![-74347317571857, -720478575203885, 161485930480663], ![3413144336599, -14695219677963092, -784227]], ![![-65600574315607, -635716389764498, 142487585691048], ![3011597943217, -12966370301611343, -691965]]]
    h := ![![![-235443662, 267057463, 502489221], ![10537937, -115959284, 0]], ![![9948526, -11284349, -21232372], ![-445272, 4899788, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1183} * I3N0 =  Ideal.span {B.equivFun.symm ![-37345, -4662, -3029]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 13 ![![5, 0, 0], ![0, 1, 0]]
  ![159, 20, 13] ![![13, 0, 0], ![1, 1, 0]] where
    su := ![![65, 0, 0], ![0, 13, 0]]
    hsu := by decide
    w := ![![2067, 260, 169], ![2405, 299, 195]]
    hw := by decide
    g := ![![![5174, -31, -143], ![405, 0, -372]], ![![86, -1, -2], ![8, 0, -6]]]
    h := ![![![12243, -11738, -26455], ![-2346, 10176, 0]], ![![14245, -13658, -30781], ![-2727, 11840, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {13} * I5N0 =  Ideal.span {B.equivFun.symm ![159, 20, 13]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 49 ![![7, 0, 0], ![0, 0, 1]]
  ![-315, 14, 13] ![![49, 0, 0], ![-8, 1, 0]] where
    su := ![![343, 0, 0], ![0, 0, 49]]
    hsu := by decide
    w := ![![-15435, 686, 637], ![4802, -343, 0]]
    hw := by decide
    g := ![![![-5, -3, 13], ![27, -50, 0]], ![![4, -1, -3], ![43, 10, 0]]]
    h := ![![![-19, 2, 2], ![-7, -1, 0]], ![![-12, -1, 0], ![6, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {49} * I7N0 =  Ideal.span {B.equivFun.symm ![-315, 14, 13]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![7, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![36, -29, -78], ![-7, 42, 0]], ![![-5, 4, 13], ![8, -7, 0]]]
    h := ![![![36, -29, -78], ![-7, 42, 0]], ![![-5, 4, 13], ![8, -7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 1 ![![13, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![13, 0, 0], ![1, 1, 0]] where
    su := ![![13, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![13, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, 1, 2], ![1, -2, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, 1, 2], ![1, -2, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {1} * I13N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 13 ![![13, 0, 0], ![-1, 0, 1]]
  ![-7, 1, 0] ![![13, 0, 0], ![1, 1, 0]] where
    su := ![![169, 0, 0], ![-13, 0, 13]]
    hsu := by decide
    w := ![![-91, 13, 0], ![-13, 0, 13]]
    hw := by decide
    g := ![![![-5125435, 30149, 141637], ![-391936, 0, 368256]], ![![396611, -2333, -10960], ![30330, 0, -28496]]]
    h := ![![![14, 0, -1], ![7, -1, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {13} * I13N1 =  Ideal.span {B.equivFun.symm ![-7, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 13 ![![13, 0, 0], ![-5, 0, 1]]
  ![-27, 2, 0] ![![13, 0, 0], ![1, 1, 0]] where
    su := ![![169, 0, 0], ![-65, 0, 13]]
    hsu := by decide
    w := ![![-351, 26, 0], ![-39, -13, 26]]
    hw := by decide
    g := ![![![152615, -898, -4217], ![11680, 0, -10965]], ![![-61044, 359, 1687], ![-4665, 0, 4386]]]
    h := ![![![3998, -126, -33], ![-1539, -328, 0]], ![![-1997, 63, 16], ![778, 164, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {13} * I13N2 =  Ideal.span {B.equivFun.symm ![-27, 2, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS2 


noncomputable def E17RS1 : RelationCertificate Table 8281 ![![17, 0, 0], ![2, 1, 0]]
  ![-1869, -175, -117] ![![8281, 0, 0], ![1119, 1, 0]] where
    su := ![![140777, 0, 0], ![16562, 8281, 0]]
    hsu := by decide
    w := ![![-15477189, -1449175, -968877], ![-2111655, -198744, -132496]]
    hw := by decide
    g := ![![![2545447554967752, -484503911583367307, -5598711479922050], ![285454884969401, 3566379205659537511, 82354455]], ![![395958508514870, -75367275128547076, -870910674577773], ![44404093219222, 554770098609248993, 12810693]]]
    h := ![![![-17655, 23530, 38181], ![-681, -49938, 0]], ![![-2409, 3210, 5209], ![-90, -6813, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {8281} * I17N1 =  Ideal.span {B.equivFun.symm ![-1869, -175, -117]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E17RS1 


noncomputable def E31RS1 : RelationCertificate Table 1183 ![![31, 0, 0], ![-6, 1, 0]]
  ![-35, -21, 13] ![![1183, 0, 0], ![-64, 1, 0]] where
    su := ![![36673, 0, 0], ![-7098, 1183, 0]]
    hsu := by decide
    w := ![![-41405, -24843, 15379], ![4732, 1183, -1183]]
    hw := by decide
    g := ![![![292336050351229323, 2832944988140525161, -634967885634072888], ![-13420593604680692, 57782077592700630772, -378]], ![![-54137950040015312, -524635377846133821, 117590217245428605], ![2485370604154918, -10700709769334002678, 70]]]
    h := ![![![1053637, 6570, -2368301], ![-203691, 5647488, 0]], ![![-129992, -811, 292193], ![25142, -696768, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {1183} * I31N1 =  Ideal.span {B.equivFun.symm ![-35, -21, 13]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E31RS1 
