import IdealArithmetic.Examples.NF3_1_865755_1.PrimesBelow3_1_865755_1F1
import IdealArithmetic.Examples.NF3_1_865755_1.ClassGroupData3_1_865755_1

set_option linter.all false

noncomputable section


noncomputable def E43RS1 : RelationCertificate Table 64 ![![43, 0, 0], ![9, 1, 0]]
  ![-229, -48, -13] ![![64, 0, 0], ![17, 1, 0]] where
    su := ![![2752, 0, 0], ![576, 64, 0]]
    hsu := by decide
    w := ![![-14656, -3072, -832], ![-7616, -1600, -448]]
    hw := by decide
    g := ![![![-7329004, -73304921, -20375899], ![-3092137, 260811505, 0]], ![![-1558853, -15591527, -4333834], ![-657620, 55473075, 0]]]
    h := ![![![4019, 21506, 10769], ![1354, -92616, 0]], ![![2085, 11175, 5596], ![720, -48127, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {64} * I43N1 =  Ideal.span {B.equivFun.symm ![-229, -48, -13]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E43RS1 


noncomputable def E53RS0 : RelationCertificate Table 8 ![![53, 0, 0], ![15, 1, 0]]
  ![-385, -24, 15] ![![8, 0, 0], ![1, 1, 0]] where
    su := ![![424, 0, 0], ![120, 8, 0]]
    hsu := by decide
    w := ![![-3080, -192, 120], ![3752, 152, -120]]
    hw := by decide
    g := ![![![-138771, -138898, -358165], ![-34707, 573079, 0]], ![![-45120, -45196, -116560], ![-11282, 186505, 0]]]
    h := ![![![-13612, -122685, -38375], ![-6167, 406778, 0]], ![![16583, 149523, 46770], ![7540, -495765, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {8} * I53N0 =  Ideal.span {B.equivFun.symm ![-385, -24, 15]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 8 ![![53, 0, 0], ![23, 1, 0]]
  ![1951519, 406616, 114399] ![![8, 0, 0], ![1, 1, 0]] where
    su := ![![424, 0, 0], ![184, 8, 0]]
    hsu := by decide
    w := ![![15612152, 3252928, 915192], ![34682072, 7226312, 2033080]]
    hw := by decide
    g := ![![![2591, 424, 278], ![383, -675, 0]], ![![394, 146, 162], ![74, -309, 0]]]
    h := ![![![-664299935, -10495319074, -2188435827], ![-486305966, 23197442646, 0]], ![![-1475728520, -23315133738, -4861564820], ![-1080318653, 51532637919, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {8} * I53N1 =  Ideal.span {B.equivFun.symm ![1951519, 406616, 114399]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 32 ![![59, 0, 0], ![7, 1, 0]]
  ![-2211, 16, 37] ![![32, 0, 0], ![-15, 1, 0]] where
    su := ![![1888, 0, 0], ![224, 32, 0]]
    hsu := by decide
    w := ![![-70752, 512, 1184], ![43520, -992, -512]]
    hw := by decide
    g := ![![![-62, 4433, -1522], ![177, 9919, 0]], ![![111, 570, -178], ![-10, 1211, 0]]]
    h := ![![![31129, 127368, 79668], ![5904, -940075, 0]], ![![-19173, -78418, -49049], ![-3569, 578775, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {32} * I59N1 =  Ideal.span {B.equivFun.symm ![-2211, 16, 37]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 256 ![![61, 0, 0], ![-7, 1, 0]]
  ![-5315, -400, 229] ![![256, 0, 0], ![-111, 1, 0]] where
    su := ![![15616, 0, 0], ![-1792, 256, 0]]
    hsu := by decide
    w := ![![-1360640, -102400, 58624], ![653056, 47616, -27648]]
    hw := by decide
    g := ![![![-150694902, 10857436834, -493538991], ![107752323, 25269196218, 0]], ![![-38518435545453, 2775219838608521, -126151246580112], ![27542055406929, 6458943824901715, 0]]]
    h := ![![![88595, -270830, 225889], ![-14570, -2755800, 0]], ![![-42520, 129999, -108428], ![7047, 1322800, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {256} * I61N1 =  Ideal.span {B.equivFun.symm ![-5315, -400, 229]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E61RS1 


noncomputable def E67RS0 : RelationCertificate Table 128 ![![67, 0, 0], ![-33, 1, 0]]
  ![-3751, -80, 97] ![![128, 0, 0], ![17, 1, 0]] where
    su := ![![8576, 0, 0], ![-4224, 128, 0]]
    hsu := by decide
    w := ![![-480128, -10240, 12416], ![-36864, -1408, 1152]]
    hw := by decide
    g := ![![![108, 608, 169], ![36, -4257, 0]], ![![-46, -281, -78], ![29, 1980, 0]]]
    h := ![![![1347272, -30337769, 4742881], ![-1116309, -63554586, 0]], ![![102569, -2309464, 361052], ![-84963, -4838095, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {128} * I67N0 =  Ideal.span {B.equivFun.symm ![-3751, -80, 97]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 32 ![![67, 0, 0], ![-18, 1, 0]]
  ![3235, -6288, 1947] ![![32, 0, 0], ![-15, 1, 0]] where
    su := ![![2144, 0, 0], ![-576, 32, 0]]
    hsu := by decide
    w := ![![103520, -201216, 62304], ![482112, 167200, -62592]]
    hw := by decide
    g := ![![![932219, 250314, 66184], ![-429143, 1673, 0]], ![![-17063, -4771, -1148], ![7865, -448, 0]]]
    h := ![![![80287, -756519, 222651], ![-32793, -2983134, 0]], ![![343218, -3233967, 951777], ![-140437, -12754203, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {32} * I67N1 =  Ideal.span {B.equivFun.symm ![3235, -6288, 1947]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 64 ![![67, 0, 0], ![-16, 1, 0]]
  ![-1453, -48, 43] ![![64, 0, 0], ![17, 1, 0]] where
    su := ![![4288, 0, 0], ![-1024, 64, 0]]
    hsu := by decide
    w := ![![-92992, -3072, 2752], ![-12800, -640, 448]]
    hw := by decide
    g := ![![![10247922, 102500255, 28491059], ![4323679, -364685574, 0]], ![![38341642376, 383494195989, 106596376471], ![16176595622, -1364433618829, 0]]]
    h := ![![![-9187, 74714, -24921], ![3364, 333950, 0]], ![![-1260, 10280, -3429], ![480, 45950, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {64} * I67N2 =  Ideal.span {B.equivFun.symm ![-1453, -48, 43]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E67RS2 


noncomputable def E79RS1 : RelationCertificate Table 16 ![![79, 0, 0], ![26, 1, 0]]
  ![1691, 352, 99] ![![16, 0, 0], ![1, 1, 0]] where
    su := ![![1264, 0, 0], ![416, 16, 0]]
    hsu := by decide
    w := ![![27056, 5632, 1584], ![30016, 6256, 1760]]
    hw := by decide
    g := ![![![2630425, 2630400, 6627386], ![328811, -21207633, 0]], ![![882661, 882651, 2223870], ![110343, -7116384, 0]]]
    h := ![![![33157, 525416, 97341], ![17624, -1537968, 0]], ![![36786, 582896, 107990], ![19547, -1706220, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {16} * I79N1 =  Ideal.span {B.equivFun.symm ![1691, 352, 99]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E79RS1 
