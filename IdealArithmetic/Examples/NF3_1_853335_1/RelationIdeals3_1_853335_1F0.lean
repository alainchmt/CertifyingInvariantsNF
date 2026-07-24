import IdealArithmetic.Examples.NF3_1_853335_1.PrimesBelow3_1_853335_1F0
import IdealArithmetic.Examples.NF3_1_853335_1.ClassGroupData3_1_853335_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![0, 1, 0]]
  ![221021748, 16565154, 17267213] ![![2, 0, 0], ![-3, 0, 1]] where
    su := ![![4, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![442043496, 33130308, 34534426], ![3907246072, 292840562, 305251636]]
    hw := by decide
    g := ![![![-4930, 444, -2630], ![6083, -7, 0]], ![![14058, -7201, 11029], ![-15569, 0, 0]]]
    h := ![![![4000039668, 179017368, -1458901367], ![638355690, 257539572, -51801639]], ![![35356564300, 1582344076, -12895307066], ![5642460023, 2276406026, -457877454]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![221021748, 16565154, 17267213]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![-3, 0, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-3, 0, 1]] where
    su := ![![2, 0, 0], ![-3, 0, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-3, 0, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E2RS2 : RelationCertificate Table 16 ![![2, 0, 0], ![-3, 1, 1]]
  ![-20, 0, 1] ![![16, 0, 0], ![-1, 0, 1]] where
    su := ![![32, 0, 0], ![-48, 16, 16]]
    hsu := by decide
    w := ![![-320, 0, 16], ![112, 16, -16]]
    hw := by decide
    g := ![![![4417, -2, -4542], ![72640, 11, 0]], ![![-7607, 0, 7564], ![-121023, 5, 0]]]
    h := ![![![-25066, -11178, -16711], ![23658, 651, 0]], ![![9551, 4258, 6365], ![-9011, -248, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {16} * I2N2 =  Ideal.span {B.equivFun.symm ![-20, 0, 1]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E2RS2 


noncomputable def E3RS0 : RelationCertificate Table 4 ![![3, 0, 0], ![-4, 0, 1]]
  ![320, 24, 25] ![![4, 0, 0], ![-1, 0, 1]] where
    su := ![![12, 0, 0], ![-16, 0, 4]]
    hsu := by decide
    w := ![![1280, 96, 100], ![6300, 472, 492]]
    hw := by decide
    g := ![![![248, 4, 19], ![-55, -6, 0]], ![![-336, -2, -29], ![80, 8, 0]]]
    h := ![![![3172, 1416, 1354], ![-3773, 0, -264]], ![![15585, 6962, 6660], ![-18559, 0, -1298]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {4} * I3N0 =  Ideal.span {B.equivFun.symm ![320, 24, 25]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 40 ![![5, 0, 0], ![1, 1, 0]]
  ![-30836, -752, 2019] ![![40, 0, 0], ![-17, 0, 1]] where
    su := ![![200, 0, 0], ![40, 40, 0]]
    hsu := by decide
    w := ![![-1233440, -30080, 80760], ![574600, 42080, -57320]]
    hw := by decide
    g := ![![![-3965091900, 337949415, -120075686], ![1682162189, 1039924844, 0]], ![![-595637495, 50615185, -18101088], ![252693417, 155988745, 0]]]
    h := ![![![-6977399, 2559229, -14295513], ![-883633, 5956632, 0]], ![![3087824, -1132397, 6326051], ![391089, -2635974, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {40} * I5N0 =  Ideal.span {B.equivFun.symm ![-30836, -752, 2019]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![5, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![21, -18, 48], ![-10, -20, 0]], ![![-10, 9, -24], ![6, 10, 0]]]
    h := ![![![21, -18, 48], ![-10, -20, 0]], ![![-10, 9, -24], ![6, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 25 ![![7, 0, 0], ![0, 1, 0]]
  ![-2211291, -165732, -172756] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![175, 0, 0], ![0, 25, 0]]
    hsu := by decide
    w := ![![-55282275, -4143300, -4318900], ![-49780800, -3730975, -3889100]]
    hw := by decide
    g := ![![![195, -14, -20], ![62, 28, 0]], ![![-164, 32, -12], ![-29, -2, 0]]]
    h := ![![![329482359, -161624349, 659571836], ![-23089191, -384764634, 0]], ![![296693568, -145540129, 593933836], ![-20791440, -346474368, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {25} * I7N0 =  Ideal.span {B.equivFun.symm ![-2211291, -165732, -172756]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 25 ![![11, 0, 0], ![2, 1, 0]]
  ![143, -64, 38] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![275, 0, 0], ![50, 25, 0]]
    hsu := by decide
    w := ![![3575, -1600, 950], ![7600, -25, -350]]
    hw := by decide
    g := ![![![-433, -29, -34], ![-136, -7, 0]], ![![-652, -42, -46], ![-190, -21, 0]]]
    h := ![![![132823, -24795, 273586], ![21897, -250784, 0]], ![![262910, -49068, 541526], ![43347, -496400, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {25} * I11N0 =  Ideal.span {B.equivFun.symm ![143, -64, 38]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 200 ![![11, 0, 0], ![3, 1, 0]]
  ![-710188, 326624, -194883] ![![200, 0, 0], ![-57, 0, 1]] where
    su := ![![2200, 0, 0], ![600, 200, 0]]
    hsu := by decide
    w := ![![-142037600, 65324800, -38976600], ![81343800, -20429200, 10403600]]
    hw := by decide
    g := ![![![244878523293985, -77957627001186, 4761544749327], ![-69766571414835, -294179779555262, 0]], ![![55654455428121, -17717622601236, 1082190353175], ![-15856108845063, -66859040808497, 0]]]
    h := ![![![-8105636, 228768, -17294313], ![-2189824, 15836880, 0]], ![![4426194, -118051, 9435758], ![1196415, -8645110, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {200} * I11N1 =  Ideal.span {B.equivFun.symm ![-710188, 326624, -194883]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 200 ![![11, 0, 0], ![-5, 1, 0]]
  ![292, -16, -3] ![![200, 0, 0], ![-57, 0, 1]] where
    su := ![![2200, 0, 0], ![-1000, 200, 0]]
    hsu := by decide
    w := ![![58400, -3200, -600], ![-19800, 800, 400]]
    hw := by decide
    g := ![![![7986389, -2542479, 155290], ![-2275241, -9594260, 0]], ![![-3811397, 1213379, -74112], ![1086015, 4578789, 0]]]
    h := ![![![563637, -926869, 1436727], ![-340457, -1317000, 0]], ![![-189754, 312045, -483698], ![114629, 443390, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {200} * I11N2 =  Ideal.span {B.equivFun.symm ![292, -16, -3]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 160 ![![13, 0, 0], ![-9, 4, 1]]
  ![-61628, 304, 2767] ![![160, 0, 0], ![-17, 0, 1]] where
    su := ![![2080, 0, 0], ![-1440, 640, 160]]
    hsu := by decide
    w := ![![-9860480, 48640, 442720], ![1356960, 40320, -93920]]
    hw := by decide
    g := ![![![-34059983, 2486803, -597009], ![3615257, 30611988, 0]], ![![23660261, -1732501, 412628], ![-2511217, -21295296, 0]]]
    h := ![![![-3284, -624, 51], ![2104, 0, 0]], ![![462, 104, -24], ![-275, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {160} * I13N0 =  Ideal.span {B.equivFun.symm ![-61628, 304, 2767]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 50 ![![13, 0, 0], ![1, 1, 0]]
  ![-174486, -11272, 16349] ![![50, 0, 0], ![-7, 0, 1]] where
    su := ![![650, 0, 0], ![50, 50, 0]]
    hsu := by decide
    w := ![![-8724300, -563600, 817450], ![696550, 295400, -241000]]
    hw := by decide
    g := ![![![-11980560, -829578, -929770], ![1658695, 259984, 0]], ![![-8719868324523, 148170345410, -172519028845], ![1217331184897, 2469522565127, 0]]]
    h := ![![![361840, -127802, 754553], ![18014, -816070, 0]], ![![-17380, 6689, -37400], ![-819, 40115, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {50} * I13N1 =  Ideal.span {B.equivFun.symm ![-174486, -11272, 16349]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 10 ![![17, 0, 0], ![0, 1, 0]]
  ![-14116814, -1058028, -1102869] ![![10, 0, 0], ![-7, 0, 1]] where
    su := ![![170, 0, 0], ![0, 10, 0]]
    hsu := by decide
    w := ![![-141168140, -10580280, -11028690], ![-193091290, -14471820, -15085160]]
    hw := by decide
    g := ![![![-817, 171, -252], ![561, 140, 0]], ![![-545953768149, 13498115242, -51202850427], ![377047352670, 44993717413, 0]]]
    h := ![![![14116814, -7509859, 29829555], ![-441751, -42350442, 0]], ![![19309129, -10272065, 40801184], ![-604238, -57927387, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {10} * I17N1 =  Ideal.span {B.equivFun.symm ![-14116814, -1058028, -1102869]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 800 ![![19, 0, 0], ![-1, 1, 0]]
  ![-42908, -3216, -3353] ![![800, 0, 0], ![143, 0, 1]] where
    su := ![![15200, 0, 0], ![-800, 800, 0]]
    hsu := by decide
    w := ![![-34326400, -2572800, -2682400], ![-7023200, -526400, -548800]]
    hw := by decide
    g := ![![![-2450313881623614, -2065035201841612, -41596018546084], ![-438045601363161, 11238286812743466, 0]], ![![130228240354591, 109751612894574, 2210727507867], ![23281061372855, -597287689222171, 0]]]
    h := ![![![-3672690266, 2442811686, -7379257091], ![321868542, 11683823448, 0]], ![![-751434392, 499800577, -1509799946], ![65854475, 2390516524, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {800} * I19N1 =  Ideal.span {B.equivFun.symm ![-42908, -3216, -3353]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 40 ![![23, 0, 0], ![2, 1, 0]]
  ![44404, 3328, 3469] ![![40, 0, 0], ![-17, 0, 1]] where
    su := ![![920, 0, 0], ![80, 40, 0]]
    hsu := by decide
    w := ![![1776160, 133120, 138760], ![163320, 12240, 12760]]
    hw := by decide
    g := ![![![17377, -1483, 527], ![-7351, -4554, 0]], ![![1497, -125, 43], ![-606, -387, 0]]]
    h := ![![![125390974, -21475991, 252512123], ![9969841, -483981280, 0]], ![![11529849, -1974744, 23218793], ![916758, -44502660, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {40} * I23N1 =  Ideal.span {B.equivFun.symm ![44404, 3328, 3469]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 20 ![![29, 0, 0], ![-1, 1, 0]]
  ![88328, -6504, 293] ![![20, 0, 0], ![3, 0, 1]] where
    su := ![![580, 0, 0], ![-20, 20, 0]]
    hsu := by decide
    w := ![![1766560, -130080, 5860], ![-878780, -40840, 71160]]
    hw := by decide
    g := ![![![171290309934, 6811101857, 1629600473], ![25775026521, -19463511438, 0]], ![![-8867453313, -352881847, -84839438], ![-1334359957, 1006733345, 0]]]
    h := ![![![289808957, -193012797, 580760041], ![-16649023, -1403503408, 0]], ![![-143549457, 95603768, -287664498], ![8246686, 695189500, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {20} * I29N1 =  Ideal.span {B.equivFun.symm ![88328, -6504, 293]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E29RS1 
