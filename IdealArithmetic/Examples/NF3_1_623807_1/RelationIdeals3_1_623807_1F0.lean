import IdealArithmetic.Examples.NF3_1_623807_1.PrimesBelow3_1_623807_1F0
import IdealArithmetic.Examples.NF3_1_623807_1.ClassGroupData3_1_623807_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 8 ![![2, 0, 0], ![0, 1, 0]]
  ![24, 4, 1] ![![8, 0, 0], ![3, 0, 1]] where
    su := ![![16, 0, 0], ![0, 8, 0]]
    hsu := by decide
    w := ![![192, 32, 8], ![528, 88, 24]]
    hw := by decide
    g := ![![![50, 1, -3], ![21, -3, 0]], ![![-19, 0, 0], ![0, 1, 0]]]
    h := ![![![88, 1, 0], ![2, 0, -1]], ![![261, 4, 0], ![3, 0, -3]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {8} * I2N0 =  Ideal.span {B.equivFun.symm ![24, 4, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 1]]
  ![6, 2, -1] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![4, 0, 0], ![2, 2, 2]]
    hsu := by decide
    w := ![![12, 4, -2], ![462, -74, 2]]
    hw := by decide
    g := ![![![-528, -21, 104], ![-210, 7, 0]], ![![-1141, -239, 178], ![-479, 0, 0]]]
    h := ![![![1366, -211, -223], ![466, -21, 0]], ![![44902, -6982, -7308], ![15307, -690, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![6, 2, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E2RS2 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 0, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![2, 0, 0], ![1, 0, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![1, 0, 1]]
    hw := by decide
    g := ![![![0, 0, -1], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, 0, -1], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {1} * I2N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS2 


noncomputable def E5RS0 : RelationCertificate Table 4 ![![5, 0, 0], ![-1, 2, 1]]
  ![14569652, -5166924, 1044753] ![![4, 0, 0], ![-1, 0, 1]] where
    su := ![![20, 0, 0], ![-4, 8, 4]]
    hsu := by decide
    w := ![![58278608, -20667696, 4179012], ![-958744556, 84568152, 19736576]]
    hw := by decide
    g := ![![![-13006848655163, -2379127734339, -1341212724840], ![2916408982581, -1422, 0]], ![![-83505527665789, -15274285207012, -8610746464806], ![18723695300247, 316, 0]]]
    h := ![![![2760003, -725530, 362878], ![-769637, 0, 0]], ![![-46086231, 526414, -864168], ![9254984, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {4} * I5N0 =  Ideal.span {B.equivFun.symm ![14569652, -5166924, 1044753]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 8 ![![5, 0, 0], ![2, 1, 0]]
  ![-6311059286416, -1093103508340, -281237573903] ![![8, 0, 0], ![3, 0, 1]] where
    su := ![![40, 0, 0], ![16, 8, 0]]
    hsu := by decide
    w := ![![-50488474291328, -8744828066720, -2249900591224], ![-142336799893672, -24653366141648, -6342906073688]]
    hw := by decide
    g := ![![![-19658962582965932389, -441595638310144769, 1052270687684793743], ![-7240577132651625425, 1177588368826900458, 0]], ![![-5897688774890294920, -132478691492897216, 315681206305441583], ![-2172173139795680394, 353276510648070169, 0]]]
    h := ![![![347863718538, -20821672134847, -14328306995507], ![-4025188939553, 35680148701816, 0]], ![![980695281265, -58700331545143, -40394276005779], ![-11347788196517, 100589258384842, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {8} * I5N1 =  Ideal.span {B.equivFun.symm ![-6311059286416, -1093103508340, -281237573903]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![-3, 2, 1]]
  ![662850331102, 114808622380, 29538372327] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![14, 0, 0], ![-6, 4, 2]]
    hsu := by decide
    w := ![![1325700662204, 229617244760, 59076744654], ![13623928339158, 2359724919232, 607118453376]]
    hw := by decide
    g := ![![![403578, -45018, -87676], ![157953, -108, 0]], ![![-1153763, 48074, 273484], ![-440139, 54, 0]]]
    h := ![![![82928310049, 24244294698, 8141298940], ![-27450720253, 0, 0]], ![![852235640808, 249153178414, 83666303047], ![-282104894641, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![662850331102, 114808622380, 29538372327]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 16 ![![7, 0, 0], ![-3, 1, 0]]
  ![3514408, -2734732, 767603] ![![16, 0, 0], ![3, 0, 1]] where
    su := ![![112, 0, 0], ![-48, 16, 0]]
    hsu := by decide
    w := ![![56230528, -43755712, 12281648], ![-521811696, 50133632, 9319552]]
    hw := by decide
    g := ![![![1393148696726, 249879701468, 47777349910], ![264201465015, -3576, 0]], ![![401008348038, 127554543370, 32215040404], ![77202505293, 38129700769, 0]]]
    h := ![![![196910236, -69700494, 3950083], ![458285748, -13441489, 0]], ![![-1757173329, 620557948, -35855684], ![-4089200024, 125786130, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {16} * I7N1 =  Ideal.span {B.equivFun.symm ![3514408, -2734732, 767603]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E7RS1 


noncomputable def E19RS0 : RelationCertificate Table 8 ![![19, 0, 0], ![0, 1, 0]]
  ![107920, -19492, 1233] ![![8, 0, 0], ![3, 0, 1]] where
    su := ![![152, 0, 0], ![0, 8, 0]]
    hsu := by decide
    w := ![![863360, -155936, 9864], ![-2826440, 35232, 132344]]
    hw := by decide
    g := ![![![-207425301, -40985786, -809264], ![-77885643, 0, 0]], ![![-2542225148, -70055951, 131829166], ![-936855776, 147851911, 0]]]
    h := ![![![5680, -10278, -18495], ![-529, 176319, 0]], ![![-18595, -123933, -248145], ![-6518, 2365649, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {8} * I19N0 =  Ideal.span {B.equivFun.symm ![107920, -19492, 1233]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![1, 1, 0]]
  ![22, 4, 1] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![38, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![44, 8, 2], ![478, 80, 20]]
    hw := by decide
    g := ![![![-8, 0, 2], ![-3, 0, 0]], ![![193, 1, -40], ![77, -3, 0]]]
    h := ![![![2, 0, -1], ![-16, 10, 0]], ![![20, 9, 0], ![-141, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![22, 4, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 2 ![![19, 0, 0], ![-1, 1, 0]]
  ![1583770, 274316, 70577] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![38, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![3167540, 548632, 141154], ![32552098, 5638168, 1450608]]
    hw := by decide
    g := ![![![88290, 377, -18247], ![35023, -1350, 0]], ![![-5296, 131, 1069], ![-2113, 75, 0]]]
    h := ![![![166334, -68540, 3673], ![1576576, 395, 0]], ![![1709368, -704361, 37754], ![16201943, 3989, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {2} * I19N2 =  Ideal.span {B.equivFun.symm ![1583770, 274316, 70577]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS2 


noncomputable def E23RS1 : RelationCertificate Table 4 ![![23, 0, 0], ![-5, 1, 0]]
  ![3164, 548, 141] ![![4, 0, 0], ![-1, 0, 1]] where
    su := ![![92, 0, 0], ![-20, 4, 0]]
    hsu := by decide
    w := ![![12656, 2192, 564], ![58700, 10168, 2616]]
    hw := by decide
    g := ![![![1663, -4, 83], ![-391, -46, 0]], ![![-417, 2, -21], ![101, 11, 0]]]
    h := ![![![398, 29114, -14565], ![1198, 167568, 0]], ![![1830, 135037, -67554], ![5483, 777198, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {4} * I23N1 =  Ideal.span {B.equivFun.symm ![3164, 548, 141]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 8 ![![29, 0, 0], ![11, 1, 0]]
  ![-4900193296, 80660964, 222662075] ![![8, 0, 0], ![3, 0, 1]] where
    su := ![![232, 0, 0], ![88, 8, 0]]
    hsu := by decide
    w := ![![-39201546368, 645287712, 1781296600], ![-36284748760, 17164300592, -4090205960]]
    hw := by decide
    g := ![![![309380770224157427, 64446086279532619, 2293949897817697], ![116304532571286249, 1133717480854426, 0]], ![![194360323965215644, 39604357017654696, 1151827431361950], ![73029099915876119, 410483915482669, 0]]]
    h := ![![![66699387936, 5884310956, -25224045], ![-176289313040, 477079690, 0]], ![![66041799025, 5899481262, -49717009], ![-174522524120, 465258758, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {8} * I29N1 =  Ideal.span {B.equivFun.symm ![-4900193296, 80660964, 222662075]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 16 ![![31, 0, 0], ![2, 1, 0]]
  ![-593329304, 214881156, -44092929] ![![16, 0, 0], ![3, 0, 1]] where
    su := ![![496, 0, 0], ![32, 16, 0]]
    hsu := by decide
    w := ![![-9493268864, 3438098496, -705486864], ![37584073008, -2706419136, -984582176]]
    hw := by decide
    g := ![![![7206527483592145, 1292586339641229, 247144327615642], ![1366670423649509, 325212, 0]], ![![2843640053326774, 382248093975748, 55106510976872], ![536626666934838, -87596336004409, 0]]]
    h := ![![![-16540690368, -8338966313, -58170757], ![256084036052, 879600269, 0]], ![![65617623979, 33102314468, 222579048], ![-1015898669393, -3480743437, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {16} * I31N1 =  Ideal.span {B.equivFun.symm ![-593329304, 214881156, -44092929]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E31RS1 
