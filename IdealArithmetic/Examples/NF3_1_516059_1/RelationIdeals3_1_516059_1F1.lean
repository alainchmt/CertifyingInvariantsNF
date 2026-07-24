import IdealArithmetic.Examples.NF3_1_516059_1.PrimesBelow3_1_516059_1F1
import IdealArithmetic.Examples.NF3_1_516059_1.ClassGroupData3_1_516059_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 2 ![![37, 0, 0], ![11, 1, 0]]
  ![24, 0, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![74, 0, 0], ![22, 2, 0]]
    hsu := by decide
    w := ![![48, 0, 2], ![74, -2, 4]]
    hw := by decide
    g := ![![![-118, -66, 389], ![-92, -111, 0]], ![![-32, -19, 105], ![-23, -30, 0]]]
    h := ![![![3400, -9688, -8459], ![760, 44712, 0]], ![![5243, -14951, -13054], ![1186, 69000, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {2} * I37N1 =  Ideal.span {B.equivFun.symm ![24, 0, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E43RS1 : RelationCertificate Table 32768 ![![43, 0, 0], ![8, 1, 0]]
  ![34, 316, 185] ![![32768, 0, 0], ![11321, 1, 0]] where
    su := ![![1409024, 0, 0], ![262144, 32768, 0]]
    hsu := by decide
    w := ![![1114112, 10354688, 6062080], ![393216, 3571712, 2097152]]
    hw := by decide
    g := ![![![900632915321, -3657858835931726, -2262326542578], ![199530239087, 10590273735313709, 0]], ![![167559650458, -680532066197294, -420898078764], ![37121939649, 1970284034991252, 0]]]
    h := ![![![17704744, -30370441, -42434375], ![2587629, 260668330, 0]], ![![6124884, -10506531, -14680000], ![895182, 90177152, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {32768} * I43N1 =  Ideal.span {B.equivFun.symm ![34, 316, 185]} * (J0 ^ 15) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_15 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 128 ![![53, 0, 0], ![8, 1, 0]]
  ![-1026, 4, -41] ![![128, 0, 0], ![57, 1, 0]] where
    su := ![![6784, 0, 0], ![1024, 128, 0]]
    hsu := by decide
    w := ![![-131328, 512, -5248], ![-60544, 256, -2432]]
    hw := by decide
    g := ![![![1058887106, -21495876709, -2786195072], ![303599149, 50947567030, 0]], ![![158404913, -3215690453, -416802767], ![45417194, 7621536311, 0]]]
    h := ![![![-25130, 42653, 59635], ![-2965, -451528, 0]], ![![-11585, 19664, 27493], ![-1370, -208164, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {128} * I53N1 =  Ideal.span {B.equivFun.symm ![-1026, 4, -41]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 2048 ![![59, 0, 0], ![-12, 1, 0]]
  ![-22, -84, 61] ![![2048, 0, 0], ![-967, 1, 0]] where
    su := ![![120832, 0, 0], ![-24576, 2048, 0]]
    hsu := by decide
    w := ![![-45056, -172032, 124928], ![24576, 79872, -59392]]
    hw := by decide
    g := ![![![23459852479667097, 8632915256379468430, -62299364269669368], ![-6861700239967659, 18227014003468980801, 0]], ![![-4771495710952185, -1755847278005579754, 12671057913321044], ![1395600134027769, -3707189515211642586, 0]]]
    h := ![![![-110, -563, 263], ![13, -2208, 0]], ![![66, 310, -145], ![19, 1218, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {2048} * I59N1 =  Ideal.span {B.equivFun.symm ![-22, -84, 61]} * (J0 ^ 11) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11 E59RS1 


noncomputable def E67RS1 : RelationCertificate Table 524288 ![![67, 0, 0], ![1, 1, 0]]
  ![-41910, 1772, -1555] ![![524288, 0, 0], ![-86983, 1, 0]] where
    su := ![![35127296, 0, 0], ![524288, 524288, 0]]
    hsu := by decide
    w := ![![-21972910080, 929038336, -815267840], ![3645374464, -154140672, 135266304]]
    hw := by decide
    g := ![![![-15123360923458607733, -446480225326771456060554, 35929478045493188475], ![1657476573712651043, -2691056312216504685597258, 0]], ![![-112862614619020453, -3331992528719018049288, 268134500964154885], ![12369415814987727, -20082814463070690906699, 0]]]
    h := ![![![1329, 1329, -4587], ![93, 43682, 0]], ![![-221, -221, 761], ![19, -7247, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {524288} * I67N1 =  Ideal.span {B.equivFun.symm ![-41910, 1772, -1555]} * (J0 ^ 19) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_19 E67RS1 


noncomputable def E73RS1 : RelationCertificate Table 4 ![![73, 0, 0], ![-36, 1, 0]]
  ![18, 0, 1] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![292, 0, 0], ![-144, 4, 0]]
    hsu := by decide
    w := ![![72, 0, 4], ![68, -8, 4]]
    hw := by decide
    g := ![![![-97, -64, 256], ![-37, -146, 0]], ![![48, 31, -128], ![22, 73, 0]]]
    h := ![![![54, 596, -107], ![16, 1116, 0]], ![![53, 596, -107], ![14, 1116, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {4} * I73N1 =  Ideal.span {B.equivFun.symm ![18, 0, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 64 ![![79, 0, 0], ![24, 1, 0]]
  ![-610, 4, -25] ![![64, 0, 0], ![-7, 1, 0]] where
    su := ![![5056, 0, 0], ![1536, 64, 0]]
    hsu := by decide
    w := ![![-39040, 256, -1600], ![3008, 0, 128]]
    hw := by decide
    g := ![![![-15404390, -51681558, 36167494], ![877389, -330674232, 0]], ![![4952543630, 16615721771, -11627920167], ![-282063792, 106312412955, 0]]]
    h := ![![![-34174, 254374, 84761], ![-7110, -956592, 0]], ![![2609, -19598, -6530], ![626, 73696, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {64} * I79N1 =  Ideal.span {B.equivFun.symm ![-610, 4, -25]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E79RS1 
