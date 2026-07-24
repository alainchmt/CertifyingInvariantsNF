import IdealArithmetic.Examples.NF3_1_551980_3.PrimesBelow3_1_551980_3F0
import IdealArithmetic.Examples.NF3_1_551980_3.ClassGroupData3_1_551980_3

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 9 ![![3, 0, 0], ![-16, 1, 1]]
  ![76, -13, -4] ![![9, 0, 0], ![-2, 1, 0]] where
    su := ![![27, 0, 0], ![-144, 9, 9]]
    hsu := by decide
    w := ![![684, -117, -36], ![468, 18, -9]]
    hw := by decide
    g := ![![![-2785, -117655, 59521], ![-12446, -535696, 0]], ![![14777, 632448, -319934], ![66991, 2879366, 0]]]
    h := ![![![4, -3, 0], ![-4, 0, 0]], ![![12, 1, 0], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![76, -13, -4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![3, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0, 0], ![0, 1, 0]]
  ![-3335, -142, 62] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![15, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![-10005, -426, 186], ![-12945, -2175, -18]]
    hw := by decide
    g := ![![![352780, -135279, 15270], ![72503, -8, 0]], ![![-442944, 169853, -19172], ![-91030, 8, 0]]]
    h := ![![![-667, -28, 0], ![-2, 62, 0]], ![![-863, -140, 0], ![-25, -6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![-3335, -142, 62]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 3 ![![5, 0, 0], ![2, 1, 0]]
  ![-1716491, -1861612, -252982] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![15, 0, 0], ![6, 3, 0]]
    hsu := by decide
    w := ![![-5149473, -5584836, -758946], ![37495719, -8890725, -2367576]]
    hw := by decide
    g := ![![![-5541332140518, 2124931152098, -239812722281], ![-1138800329471, -11, 0]], ![![4741043852148, -1818045105294, 205178575085], ![974332915620, -5, 0]]]
    h := ![![![-6848281, -4166849, -321614], ![16262457, 1355088, 0]], ![![38852955, 22006294, 2053356], ![-90883101, -11055972, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {3} * I5N1 =  Ideal.span {B.equivFun.symm ![-1716491, -1861612, -252982]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 3 ![![7, 0, 0], ![-16, 3, 1]]
  ![3117971713096, -919093917934, 126285735575] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![21, 0, 0], ![-48, 9, 3]]
    hsu := by decide
    w := ![![9353915139288, -2757281753802, 378857206725], ![-16456317301029, 4850878242237, -666522446784]]
    hw := by decide
    g := ![![![746451, 21554, -4074], ![256003, -17, 0]], ![![-3594535, 786225, 174644], ![-936103, 39, 0]]]
    h := ![![![64337594008, -59845330552, 41858752895], ![-166725534690, 0, 0]], ![![-113188953025, 105285726230, -73641989393], ![293319776823, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {3} * I7N0 =  Ideal.span {B.equivFun.symm ![3117971713096, -919093917934, 126285735575]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 9 ![![7, 0, 0], ![3, 1, 0]]
  ![118733017, -12741223, -5042155] ![![9, 0, 0], ![-2, 1, 0]] where
    su := ![![63, 0, 0], ![27, 9, 0]]
    hsu := by decide
    w := ![![1068597153, -114671007, -45379395], ![544067991, 38330208, -7699068]]
    hw := by decide
    g := ![![![-84071360058474, 23809283433091, -3597066570348], ![21328000394450, -24, 0]], ![![39368117253676, -11149179236170, 1684399281902], ![-9987268193721, -19, 0]]]
    h := ![![![1503803290, 651939454, 51994965], ![-3469296671, -369006910, 0]], ![![794063008, 342689533, 26635164], ![-1832663019, -187301600, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {9} * I7N1 =  Ideal.span {B.equivFun.symm ![118733017, -12741223, -5042155]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 9 ![![11, 0, 0], ![5, 1, 0]]
  ![5464, -3430, -685] ![![9, 0, 0], ![-2, 1, 0]] where
    su := ![![99, 0, 0], ![45, 9, 0]]
    hsu := by decide
    w := ![![49176, -30870, -6165], ![95247, -2061, -2745]]
    hw := by decide
    g := ![![![-2309678, 641949, -92699], ![584591, -54994, 0]], ![![268155, -81630, 14337], ![-68655, -25723, 0]]]
    h := ![![![83474, 24530, 1587], ![-182550, -18142, 0]], ![![180878, 51836, 3147], ![-395815, -34922, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {9} * I11N0 =  Ideal.span {B.equivFun.symm ![5464, -3430, -685]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 9 ![![11, 0, 0], ![-3, 1, 0]]
  ![26, -8, 1] ![![9, 0, 0], ![-2, 1, 0]] where
    su := ![![99, 0, 0], ![-27, 9, 0]]
    hsu := by decide
    w := ![![234, -72, 9], ![-207, 63, -9]]
    hw := by decide
    g := ![![![-232, -9763, 4939], ![-1031, -44450, 0]], ![![41, 1757, -889], ![188, 8001, 0]]]
    h := ![![![40, -13, 0], ![138, 1, 0]], ![![-31, 13, -1], ![-106, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {9} * I11N1 =  Ideal.span {B.equivFun.symm ![26, -8, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 3 ![![13, 0, 0], ![3, 1, 0]]
  ![-98, 29, -4] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![39, 0, 0], ![9, 3, 0]]
    hsu := by decide
    w := ![![-294, 87, -12], ![522, -153, 21]]
    hw := by decide
    g := ![![![11, -61, -69], ![-16, 208, 0]], ![![-2, -11, -13], ![-2, 40, 0]]]
    h := ![![![-554, -194, -5], ![2368, 61, 0]], ![![978, 340, 8], ![-4180, -97, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {3} * I13N0 =  Ideal.span {B.equivFun.symm ![-98, 29, -4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 3 ![![13, 0, 0], ![-2, 1, 0]]
  ![52, 2, -1] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![39, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![156, 6, -3], ![207, 33, 0]]
    hw := by decide
    g := ![![![-18, 986, 1125], ![326, -3364, 0]], ![![-40, -120, -157], ![-53, 464, 0]]]
    h := ![![![304, -152, 1], ![1950, -14, 0]], ![![403, -202, 2], ![2585, -26, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {3} * I13N1 =  Ideal.span {B.equivFun.symm ![52, 2, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![-4, 1, 0]]
  ![-4578025123787, 1349478261701, -185421589237] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![51, 0, 0], ![-12, 3, 0]]
    hsu := by decide
    w := ![![-13734075371361, 4048434785103, -556264767711], ![24162321207948, -7122400236063, 978635083227]]
    hw := by decide
    g := ![![![2848084, -807786, -170577], ![680100, -1, 0]], ![![746451, 21549, -4079], ![256003, -2, 0]]]
    h := ![![![-56551177783415, 14807356725872, -175283428478], ![-239197999298567, 2794396694889, 0]], ![![99490332282588, -26050542157155, 308375655935], ![420820385433670, -4916174456486, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![-4578025123787, 1349478261701, -185421589237]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 3 ![![19, 0, 0], ![-6, 1, 0]]
  ![-95599, 28180, -3872] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![57, 0, 0], ![-18, 3, 0]]
    hsu := by decide
    w := ![![-286797, 84540, -11616], ![504561, -148731, 20436]]
    hw := by decide
    g := ![![![-385, -63, -15], ![-148, 29, 0]], ![![163, -11, -1], ![53, -9, 0]]]
    h := ![![![-1796233, 324456, -4277], ![-5672138, 77391, 0]], ![![3160117, -570813, 7524], ![9979006, -136144, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {3} * I19N1 =  Ideal.span {B.equivFun.symm ![-95599, 28180, -3872]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 3 ![![23, 0, 0], ![8, 1, 0]]
  ![83, 76, 10] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![69, 0, 0], ![24, 3, 0]]
    hsu := by decide
    w := ![![249, 228, 30], ![-1467, 369, 96]]
    hw := by decide
    g := ![![![-9257, 3536, -416], ![-1906, 46, 0]], ![![-693, 261, -35], ![-143, 15, 0]]]
    h := ![![![77, 9, 0], ![-211, 10, 0]], ![![-487, -64, 0], ![1339, 32, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {3} * I23N1 =  Ideal.span {B.equivFun.symm ![83, 76, 10]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 9 ![![29, 0, 0], ![1, 1, 0]]
  ![4053086, -2761280, -542681] ![![9, 0, 0], ![-2, 1, 0]] where
    su := ![![261, 0, 0], ![9, 9, 0]]
    hsu := by decide
    w := ![![36477774, -24851520, -4884129], ![76009383, -1820655, -2218599]]
    hw := by decide
    g := ![![![1482587579726, -419873683826, 63433827003], ![-376116538136, -201842, 0]], ![![-269825407641, 76415430501, -11544713126], ![68451805096, -23470, 0]]]
    h := ![![![278860, 44182, -18413], ![-4033854, -8704, 0]], ![![581064, 283228, -8137], ![-8405369, -10538, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {9} * I29N0 =  Ideal.span {B.equivFun.symm ![4053086, -2761280, -542681]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E29RS0 


noncomputable def E29RS2 : RelationCertificate Table 3 ![![29, 0, 0], ![-8, 1, 0]]
  ![-197864891714, 58325230400, -8014028251] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![87, 0, 0], ![-24, 3, 0]]
    hsu := by decide
    w := ![![-593594675142, 174975691200, -24042084753], ![1044309487191, -307834254585, 42297173898]]
    hw := by decide
    g := ![![![-1240305, 34647, 13075], ![-401883, 21320, 0]], ![![247083, -29675, -6231], ![72472, -5460, 0]]]
    h := ![![![-800227887210, 106344022808, -920994299], ![-2876092979672, 18694806420, 0]], ![![1407838731593, -187090748232, 1620302748], ![5059902506725, -32889721726, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {3} * I29N2 =  Ideal.span {B.equivFun.symm ![-197864891714, 58325230400, -8014028251]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS2 


noncomputable def E31RS0 : RelationCertificate Table 9 ![![31, 0, 0], ![0, 1, 0]]
  ![16616, -4898, 673] ![![9, 0, 0], ![-2, 1, 0]] where
    su := ![![279, 0, 0], ![0, 9, 0]]
    hsu := by decide
    w := ![![149544, -44082, 6057], ![-137547, 40545, -5571]]
    hw := by decide
    g := ![![![-86, 85, -53], ![31, 474, 0]], ![![5, 118, -62], ![15, 553, 0]]]
    h := ![![![536, -158, 0], ![0, 673, 0]], ![![-493, 145, 0], ![10, -619, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {9} * I31N0 =  Ideal.span {B.equivFun.symm ![16616, -4898, 673]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS0 
