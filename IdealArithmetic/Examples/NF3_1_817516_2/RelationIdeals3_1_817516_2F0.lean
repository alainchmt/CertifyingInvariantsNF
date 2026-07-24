import IdealArithmetic.Examples.NF3_1_817516_2.PrimesBelow3_1_817516_2F0
import IdealArithmetic.Examples.NF3_1_817516_2.ClassGroupData3_1_817516_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1476225 ![![2, 0, 0], ![1, 1, 0]]
  ![142043, -7544, 7447] ![![1476225, 0, 0], ![-45584, 1, 0]] where
    su := ![![2952450, 0, 0], ![1476225, 1476225, 0]]
    hsu := by decide
    w := ![![209687427675, -11136641400, 10993447575], ![-6476199075, 343960425, -339531750]]
    hw := by decide
    g := ![![![2352448, -35243378967, 5412423], ![1063454, -1141422020458, 0]], ![![2243676, -33892384173, 5204947], ![420497, -1097667555020, 0]]]
    h := ![![![196934, 196934, 527278], ![196936, -149587, 0]], ![![-6083, -6083, -16285], ![-6081, 4620, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1476225} * I2N0 =  Ideal.span {B.equivFun.symm ![142043, -7544, 7447]} * (J0 ^ 6*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_2 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 6561 ![![3, 0, 0], ![5, 1, 1]]
  ![-1330, 82, 133] ![![6561, 0, 0], ![343, 1, 0]] where
    su := ![![19683, 0, 0], ![32805, 6561, 6561]]
    hsu := by decide
    w := ![![-8726130, 538002, 872613], ![-478953, 26244, 45927]]
    hw := by decide
    g := ![![![-541290764767, -62657064844203, -1267628596213], ![-37847857478, 1188130174250501, 0]], ![![-866085733256, -100253677809548, -2028253784037], ![-60558000810, 1901053296723830, 0]]]
    h := ![![![-150, 86, 103], ![-176, 0, 0]], ![![-11, 4, 5], ![-8, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {6561} * I3N0 =  Ideal.span {B.equivFun.symm ![-1330, 82, 133]} * (J0 ^ 8*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_0 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![3, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![3, 3, 7], ![3, -3, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![3, 3, 7], ![3, -3, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 6561 ![![5, 0, 0], ![0, 1, 0]]
  ![200, 37, -20] ![![6561, 0, 0], ![343, 1, 0]] where
    su := ![![32805, 0, 0], ![0, 6561, 0]]
    hsu := by decide
    w := ![![1312200, 242757, -131220], ![72171, 13122, -6561]]
    hw := by decide
    g := ![![![-289, 1482, 30], ![5774, -28119, 0]], ![![-283, 98, 2], ![5430, -1874, 0]]]
    h := ![![![-200, -224, -564], ![-43, 400, 0]], ![![-11, -13, -31], ![1, 22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {6561} * I5N0 =  Ideal.span {B.equivFun.symm ![200, 37, -20]} * (J0 ^ 8*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 19683 ![![5, 0, 0], ![1, 1, 0]]
  ![-1330, 82, 133] ![![98415, 0, 0], ![-45584, 1, 0]] where
    su := ![![98415, 0, 0], ![19683, 19683, 0]]
    hsu := by decide
    w := ![![-130891950, 8070030, 13089195], ![60603957, -3739770, -6062364]]
    hw := by decide
    g := ![![![478797667572014546361, -9515838139403334146902565, 1461373532798197505109], ![-318461118914860920295, -20545868032904943923614595, 0]], ![![76607626811806531463, -1522534102310181675830542, 233819765248579012377], ![-50953779026566752594, -3287338885276986214726082, 0]]]
    h := ![![![-5154, -5154, -9751], ![-2060, 7060, 0]], ![![2386, 2386, 4515], ![956, -3269, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {19683} * I5N1 =  Ideal.span {B.equivFun.symm ![-1330, 82, 133]} * (J0 ^ 7*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_1 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 54675 ![![5, 0, 0], ![-2, 1, 0]]
  ![6157, -31, -397] ![![54675, 0, 0], ![9091, 1, 0]] where
    su := ![![273375, 0, 0], ![-109350, 54675, 0]]
    hsu := by decide
    w := ![![336633975, -1694925, -21705975], ![56041875, -273375, -3608550]]
    hw := by decide
    g := ![![![1940461628495348, 6101053485541815731, 4696214477060422], ![434234845042250, -36680789504754081827, 0]], ![![-788312536588202, -2478552978501125627, -1907837131305614], ![-176407905725973, 14901570736304920759, 0]]]
    h := ![![![645, -110, -1191], ![-275, 794, 0]], ![![109, -19, -198], ![-42, 132, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {54675} * I5N2 =  Ideal.span {B.equivFun.symm ![6157, -31, -397]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 1476225 ![![7, 0, 0], ![6, 0, 1]]
  ![-11087, 3821, 3077] ![![1476225, 0, 0], ![-45584, 1, 0]] where
    su := ![![10333575, 0, 0], ![8857350, 0, 1476225]]
    hsu := by decide
    w := ![![-16366906575, 5640655725, 4542344325], ![504868950, -174194550, -140241375]]
    hw := by decide
    g := ![![![19161, -13172909, 2023], ![592446, -426629012, 0]], ![![19972, -11291064, 1734], ![622721, -365681980, 0]]]
    h := ![![![-116042, 38210, 12750], ![-97636, 0, 11463]], ![![3582, -1180, -394], ![3017, 0, -354]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {1476225} * I7N0 =  Ideal.span {B.equivFun.symm ![-11087, 3821, 3077]} * (J0 ^ 6*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_2 E7RS0 


noncomputable def E13RS0 : RelationCertificate Table 729 ![![13, 0, 0], ![-2, 2, 1]]
  ![-6646, 367, -356] ![![729, 0, 0], ![343, 1, 0]] where
    su := ![![9477, 0, 0], ![-1458, 1458, 729]]
    hsu := by decide
    w := ![![-4844934, 267543, -259524], ![-2216889, 122472, -118827]]
    hw := by decide
    g := ![![![2333, 402444, 8142], ![2458, -847931, 0]], ![![-584, -68311, -1382], ![-18, 143927, 0]]]
    h := ![![![-498, 15, -34], ![86, 0, 0]], ![![-227, 6, -16], ![45, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {729} * I13N0 =  Ideal.span {B.equivFun.symm ![-6646, 367, -356]} * (J0 ^ 6*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_0 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 27 ![![13, 0, 0], ![1, 1, 0]]
  ![-34, 1, -2] ![![27, 0, 0], ![-8, 1, 0]] where
    su := ![![351, 0, 0], ![27, 27, 0]]
    hsu := by decide
    w := ![![-918, 27, -54], ![621, -27, 27]]
    hw := by decide
    g := ![![![-30382, 55691, -78541], ![11065, 302944, 0]], ![![-4742, 8701, -12272], ![1748, 47335, 0]]]
    h := ![![![-11, -11, -19], ![4, 35, 0]], ![![7, 7, 13], ![4, -24, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {27} * I13N1 =  Ideal.span {B.equivFun.symm ![-34, 1, -2]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 18225 ![![17, 0, 0], ![-2, 1, 0]]
  ![-10787, 596, -598] ![![18225, 0, 0], ![9091, 1, 0]] where
    su := ![![309825, 0, 0], ![-36450, 18225, 0]]
    hsu := by decide
    w := ![![-196593075, 10862100, -10898550], ![-97959375, 5412825, -5431050]]
    hw := by decide
    g := ![![![107059517061, 441951803759576, 340187228518], ![77653233656, -885701748534364, 0]], ![![-1821672930, -7520030118097, -5788455172], ![-1321304626, 15070656501388, 0]]]
    h := ![![![-4696911071, -1610523162, -11085139598], ![457841126, 26921053224, 0]], ![![-2340401401, -802499901, -5523561308], ![228135480, 13414363134, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {18225} * I17N1 =  Ideal.span {B.equivFun.symm ![-10787, 596, -598]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E17RS1 


noncomputable def E23RS1 : RelationCertificate Table 1476225 ![![23, 0, 0], ![2, 1, 0]]
  ![-77576, -1492, 3821] ![![1476225, 0, 0], ![-45584, 1, 0]] where
    su := ![![33953175, 0, 0], ![2952450, 1476225, 0]]
    hsu := by decide
    w := ![![-114519630600, -2202527700, 5640655725], ![3535558875, 67906350, -174194550]]
    hw := by decide
    g := ![![![962630731861406, -14644490409840918246, 2248994819531700], ![-39645074069921, -474288911066169118970, 0]], ![![189890928521603, -2888808542045549451, 443642302590025], ![-7820484396954, -93559408305851379362, 0]]]
    h := ![![![-4059573057410, -6831901741033, -9604230427733], ![-650045558933, 31556757120240, 0]], ![![125331270371, 210921422561, 296511574846], ![20068867983, -974252317368, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {1476225} * I23N1 =  Ideal.span {B.equivFun.symm ![-77576, -1492, 3821]} * (J0 ^ 6*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_2 E23RS1 
