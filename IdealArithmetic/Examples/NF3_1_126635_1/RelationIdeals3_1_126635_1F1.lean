import IdealArithmetic.Examples.NF3_1_126635_1.PrimesBelow3_1_126635_1F1
import IdealArithmetic.Examples.NF3_1_126635_1.ClassGroupData3_1_126635_1

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 32 ![![41, 0, 0], ![2, 1, 0]]
  ![-19, 8, -3] ![![32, 0, 0], ![8, 1, 0]] where
    su := ![![1312, 0, 0], ![64, 32, 0]]
    hsu := by decide
    w := ![![-608, 256, -96], ![64, 32, 0]]
    hw := by decide
    g := ![![![-1, 63, 21], ![11, -225, 0]], ![![0, 9, 3], ![1, -32, 0]]]
    h := ![![![-1, -417, -417], ![11, 5698, 0]], ![![-2, 41, 42], ![42, -574, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {32} * I41N1 =  Ideal.span {B.equivFun.symm ![-19, 8, -3]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E41RS1 


noncomputable def E43RS0 : RelationCertificate Table 65536 ![![43, 0, 0], ![-20, 1, 0]]
  ![13123, -2376, 1107] ![![65536, 0, 0], ![-1592, 1, 0]] where
    su := ![![2818048, 0, 0], ![-1310720, 65536, 0]]
    hsu := by decide
    w := ![![860028928, -155713536, 72548352], ![-20971520, 3801088, -1769472]]
    hw := by decide
    g := ![![![-2121757799, -5727549945772236, 10799905619934], ![-87343919043, -235927538235998226, 0]], ![![12122184335518092, 32723058113650302392071, -61702812296539421349], ![499019769228965878, 1347918502222002505842697, 0]]]
    h := ![![![21610549621, -1220441325, 22091679], ![46462681029, -316647030, 0]], ![![-526967440, 29760142, -538701], ![-1132979980, 7721372, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {65536} * I43N0 =  Ideal.span {B.equivFun.symm ![13123, -2376, 1107]} * (J0 ^ 16) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_16 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 512 ![![43, 0, 0], ![-12, 1, 0]]
  ![985, 168, 9] ![![512, 0, 0], ![-56, 1, 0]] where
    su := ![![22016, 0, 0], ![-6144, 512, 0]]
    hsu := by decide
    w := ![![504320, 86016, 4608], ![-55808, -8192, 0]]
    hw := by decide
    g := ![![![626280, 2966600601, -161815188], ![5725961, 27616458800, 0]], ![![194040, 919040758, -50129685], ![1774092, 8555466219, 0]]]
    h := ![![![5275, -455, 6], ![18820, -83, 0]], ![![-583, 59, -3], ![-2080, 43, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {512} * I43N1 =  Ideal.span {B.equivFun.symm ![985, 168, 9]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 128 ![![47, 0, 0], ![1, 1, 0]]
  ![581, -120, 53] ![![128, 0, 0], ![-56, 1, 0]] where
    su := ![![6016, 0, 0], ![128, 128, 0]]
    hsu := by decide
    w := ![![74368, -15360, 6784], ![-36352, 7552, -3328]]
    hw := by decide
    g := ![![![-3099049, -1080241204, 58925266], ![-7083545, -2514144685, 0]], ![![-130003, -45327120, 2472515], ![-297150, -105493973, 0]]]
    h := ![![![-138, -153, 1], ![7067, 2, 0]], ![![66, 73, -1], ![-3386, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {128} * I47N1 =  Ideal.span {B.equivFun.symm ![581, -120, 53]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 512 ![![53, 0, 0], ![26, 1, 0]]
  ![415, 24, -17] ![![512, 0, 0], ![-56, 1, 0]] where
    su := ![![27136, 0, 0], ![13312, 512, 0]]
    hsu := by decide
    w := ![![212480, 12288, -8704], ![-22016, -1024, 1024]]
    hw := by decide
    g := ![![![50, 72122, -3934], ![459, 671398, 0]], ![![43634, 206668009, -11272843], ![398940, 1923898537, 0]]]
    h := ![![![-157, 21534, 2393], ![336, -42282, 0]], ![![9, -2232, -248], ![-20, 4382, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {512} * I53N1 =  Ideal.span {B.equivFun.symm ![415, 24, -17]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 8 ![![59, 0, 0], ![-25, 1, 0]]
  ![-23, 0, 1] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![472, 0, 0], ![-200, 8, 0]]
    hsu := by decide
    w := ![![-184, 0, 8], ![-72, -16, 0]]
    hw := by decide
    g := ![![![-4, -10, -31], ![1, 82, 0]], ![![2, -34, -100], ![3, 267, 0]]]
    h := ![![![-1897, 84, -1], ![-4476, 20, 0]], ![![-701, 52, -3], ![-1654, 59, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {8} * I59N1 =  Ideal.span {B.equivFun.symm ![-23, 0, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E59RS1 


noncomputable def E67RS0 : RelationCertificate Table 8192 ![![67, 0, 0], ![11, 1, 0]]
  ![21601, -4632, 2065] ![![8192, 0, 0], ![-1592, 1, 0]] where
    su := ![![548864, 0, 0], ![90112, 8192, 0]]
    hsu := by decide
    w := ![![176955392, -37945344, 16916480], ![-34537472, 7405568, -3301376]]
    hw := by decide
    g := ![![![779, -23007986, 43384], ![4009, -118467264, 0]], ![![669971, 29247042863, -55148416], ![3447489, 150591941283, 0]]]
    h := ![![![-15513, 6629692, 1657831], ![96452, -37024204, 0]], ![![3022, -1293958, -323569], ![-18790, 7226240, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {8192} * I67N0 =  Ideal.span {B.equivFun.symm ![21601, -4632, 2065]} * (J0 ^ 13) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_13 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 8 ![![67, 0, 0], ![21, 1, 0]]
  ![-85, 16, 11] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![536, 0, 0], ![168, 8, 0]]
    hsu := by decide
    w := ![![-680, 128, 88], ![-792, 8, 48]]
    hw := by decide
    g := ![![![113, -182057, -554620], ![-22752, 1479015, 0]], ![![24, -60155, -183267], ![-7519, 488718, 0]]]
    h := ![![![1601, 68, -1], ![-5112, 26, 0]], ![![1839, 65, -3], ![-5872, 69, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {8} * I67N1 =  Ideal.span {B.equivFun.symm ![-85, 16, 11]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 2 ![![67, 0, 0], ![-33, 1, 0]]
  ![-17, 0, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![134, 0, 0], ![-66, 2, 0]]
    hsu := by decide
    w := ![![-34, 0, 2], ![-72, -10, 0]]
    hw := by decide
    g := ![![![25, 20, 97], ![11, -63, 0]], ![![-15, -10, -48], ![-4, 31, 0]]]
    h := ![![![-1073, 54, -2], ![-2178, 45, 0]], ![![-2346, 103, -3], ![-4762, 67, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {2} * I67N2 =  Ideal.span {B.equivFun.symm ![-17, 0, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E67RS2 


noncomputable def E73RS1 : RelationCertificate Table 2 ![![73, 0, 0], ![-13, 1, 0]]
  ![-5, 2, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![146, 0, 0], ![-26, 2, 0]]
    hsu := by decide
    w := ![![-10, 4, 2], ![-72, 4, 6]]
    hw := by decide
    g := ![![![-17, 2, -2], ![3, 0, 0]], ![![5, -2, -4], ![-1, 3, 0]]]
    h := ![![![-103, 16, -2], ![-578, 49, 0]], ![![-856, 78, -3], ![-4804, 74, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {2} * I73N1 =  Ideal.span {B.equivFun.symm ![-5, 2, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 
