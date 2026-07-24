import IdealArithmetic.Examples.NF3_1_780300_1.PrimesBelow3_1_780300_1F0
import IdealArithmetic.Examples.NF3_1_780300_1.ClassGroupData3_1_780300_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 242 ![![2, 0, 0], ![0, 1, 0]]
  ![81, 9, 5] ![![484, 0, 0], ![224, 2, 0]] where
    su := ![![484, 0, 0], ![0, 242, 0]]
    hsu := by decide
    w := ![![39204, 4356, 2420], ![19844, 2178, 1210]]
    hw := by decide
    g := ![![![-1, 0, 0], ![2, 0, 0]], ![![-56, 5935, 265], ![121, -12825, 0]]]
    h := ![![![81, 14, 0], ![-10, 2, 0]], ![![41, 6, 0], ![-3, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {242} * I2N0 =  Ideal.span {B.equivFun.symm ![81, 9, 5]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 1452 ![![3, 0, 0], ![-1, 1, 0]]
  ![81, 9, 5] ![![4356, 0, 0], ![-1560, 12, 0]] where
    su := ![![4356, 0, 0], ![-1452, 1452, 0]]
    hsu := by decide
    w := ![![352836, 39204, 21780], ![-116160, -13068, -7260]]
    hw := by decide
    g := ![![![131, 3379, -130], ![366, 9438, 0]], ![![953, 966673, -37180], ![2661, 2699269, 0]]]
    h := ![![![178, -89, 10], ![291, -3, 0]], ![![-58, 29, -5], ![-94, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1452} * I3N0 =  Ideal.span {B.equivFun.symm ![81, 9, 5]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 2108304 ![![5, 0, 0], ![0, 0, 1]]
  ![3380, 26, 1] ![![2108304, 0, 0], ![-3120, 24, 0]] where
    su := ![![10541520, 0, 0], ![0, 0, 2108304]]
    hsu := by decide
    w := ![![7126067520, 54815904, 2108304], ![-10541520, 0, 0]]
    hw := by decide
    g := ![![![0, 0, 0], ![-1, 0, 0]], ![![1, -26, 1], ![676, -17564, 0]]]
    h := ![![![-4, 182, 0], ![1, 20, -26]], ![![-1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {2108304} * I5N0 =  Ideal.span {B.equivFun.symm ![3380, 26, 1]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E5RS0 


noncomputable def E11RS0 : RelationCertificate Table 5324 ![![11, 0, 0], ![3, 4, 1]]
  ![-1121, 104, 4] ![![5324, 0, 0], ![-520, 4, 0]] where
    su := ![![58564, 0, 0], ![15972, 21296, 5324]]
    hsu := by decide
    w := ![![-5968204, 553696, 21296], ![585640, -58564, 0]]
    hw := by decide
    g := ![![![119, 91883, -3534], ![1219, 940750, 0]], ![![67, 16457, -633], ![689, 168500, 0]]]
    h := ![![![-97, 16, 2], ![-18, 0, 0]], ![![7, -5, -1], ![11, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {5324} * I11N0 =  Ideal.span {B.equivFun.symm ![-1121, 104, 4]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 484 ![![11, 0, 0], ![2, 1, 0]]
  ![81, 9, 5] ![![5324, 0, 0], ![-520, 4, 0]] where
    su := ![![5324, 0, 0], ![968, 484, 0]]
    hsu := by decide
    w := ![![431244, 47916, 26620], ![-38720, -4356, -2420]]
    hw := by decide
    g := ![![![23374521, 321571528836, -12368142640], ![239319135, 3292399570768, 0]], ![![3541602, 48722959667, -1873961035], ![36260556, 498848427518, 0]]]
    h := ![![![700663, 361788, 28725], ![-3853201, -63184, 0]], ![![-62916, -32487, -2580], ![345998, 5675, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {484} * I11N1 =  Ideal.span {B.equivFun.symm ![81, 9, 5]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 7730448 ![![13, 0, 0], ![2, 1, 0]]
  ![8612, -159, 557] ![![7730448, 0, 0], ![-2137424, 16, 8]] where
    su := ![![100495824, 0, 0], ![15460896, 7730448, 0]]
    hsu := by decide
    w := ![![66574618176, -1229141232, 4305859536], ![-18406196688, 340139712, -1190488992]]
    hw := by decide
    g := ![![![-10418806, 18051881708, -675654], ![3859915, 65288465418, 0]], ![![-1984823, 3488332647, -130563], ![848962, 12616296134, 0]]]
    h := ![![![111666404180, 57178143445, 3362354289], ![-725831622864, -8742121040, 0]], ![![-30872919685, -15808302084, -929605853], ![200673976762, 2416975187, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {7730448} * I13N0 =  Ideal.span {B.equivFun.symm ![8612, -159, 557]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 484 ![![13, 0, 0], ![5, 1, 0]]
  ![-72, -8, 9] ![![484, 0, 0], ![224, 2, 0]] where
    su := ![![6292, 0, 0], ![2420, 484, 0]]
    hsu := by decide
    w := ![![-34848, -3872, 4356], ![-13068, -1936, 1936]]
    hw := by decide
    g := ![![![-1260948, 800514610, 35737762], ![2724549, -1729707680, 0]], ![![63340763632, -40214598428044, -1795319820115], ![-136861292847, 86893479293567, 0]]]
    h := ![![![-103674, -24712, -3977], ![269538, 10342, 0]], ![![-39004, -9293, -1492], ![101405, 3880, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {484} * I13N1 =  Ideal.span {B.equivFun.symm ![-72, -8, 9]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 23191344 ![![13, 0, 0], ![6, 1, 0]]
  ![26023, 3241, 1814] ![![23191344, 0, 0], ![-10547760, 48, 0]] where
    su := ![![301487472, 0, 0], ![139148064, 23191344, 0]]
    hsu := by decide
    w := ![![603508344912, 75163145904, 42069098016], ![-274469556240, -34184041056, -19132858800]]
    hw := by decide
    g := ![![![219901, 123499898277, -2810073], ![483496, 271539040036, 0]], ![![100192, 63439546471, -1443481], ![220292, 139484435124, 0]]]
    h := ![![![1327036165519, 315634869207, 78718479338], ![-2875245020954, -204668045916, 0]], ![![-603522976815, -143547614740, -35800376710], ![1307633114460, 93080979281, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {23191344} * I13N2 =  Ideal.span {B.equivFun.symm ![26023, 3241, 1814]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E13RS2 


noncomputable def E17RS0 : RelationCertificate Table 4356 ![![17, 0, 0], ![0, 1, 0]]
  ![17, -25, 13] ![![4356, 0, 0], ![-1560, 12, 0]] where
    su := ![![74052, 0, 0], ![0, 4356, 0]]
    hsu := by decide
    w := ![![74052, -108900, 56628], ![0, 39204, -21780]]
    hw := by decide
    g := ![![![43498243571, 49744925913181, -1913279250579], ![121460480124, 138904073592037, 0]], ![![-21749092250, -24872429266290, 956638329500], ![-60730157591, -69451942721699, 0]]]
    h := ![![![1, -4, -1], ![43, 6, 0]], ![![0, 0, -5], ![9, 16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {4356} * I17N0 =  Ideal.span {B.equivFun.symm ![17, -25, 13]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E17RS0 


noncomputable def E23RS1 : RelationCertificate Table 31944 ![![23, 0, 0], ![1, 1, 0]]
  ![7846, 818, 441] ![![31944, 0, 0], ![2656, 9748, 1316]] where
    su := ![![734712, 0, 0], ![31944, 31944, 0]]
    hsu := by decide
    w := ![![250632624, 26130192, 14087304], ![934649496, 98387520, 51365952]]
    hw := by decide
    g := ![![![140988466, -2082526, 30430915], ![12349393, -20277738, 0]], ![![107179391038464698, -1581302309303016, 23133711908779361], ![9381977603275827, -15415059001640519, 0]]]
    h := ![![![339, 339, 1547], ![49, -7028, 0]], ![![1267, 1267, 5761], ![118, -26179, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {31944} * I23N1 =  Ideal.span {B.equivFun.symm ![7846, 818, 441]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 2108304 ![![29, 0, 0], ![-5, 1, 0]]
  ![3346, -650, -25] ![![2108304, 0, 0], ![-3120, 24, 0]] where
    su := ![![61140816, 0, 0], ![-10541520, 2108304, 0]]
    hsu := by decide
    w := ![![7054385184, -1370397600, -52707600], ![-10541520, 2108304, 0]]
    hw := by decide
    g := ![![![-122331, -7264760026649, 279413847215], ![-82663761, -4909077764489783, 0]], ![![25350, 1503053489665, -57809749610], ![17129971, 1015671052848012, 0]]]
    h := ![![![4504, -916, 15], ![25454, -92, 0]], ![![-5, 6, -5], ![-28, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {2108304} * I29N1 =  Ideal.span {B.equivFun.symm ![3346, -650, -25]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E29RS1 
