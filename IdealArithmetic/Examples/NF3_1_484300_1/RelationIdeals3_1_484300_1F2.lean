import IdealArithmetic.Examples.NF3_1_484300_1.PrimesBelow3_1_484300_1F2
import IdealArithmetic.Examples.NF3_1_484300_1.ClassGroupData3_1_484300_1

set_option linter.all false

noncomputable section


noncomputable def E97RS1 : RelationCertificate Table 3 ![![97, 0, 0], ![-38, 1, 0]]
  ![19160629, -1468180, 751458] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![291, 0, 0], ![-114, 3, 0]]
    hsu := by decide
    w := ![![57481887, -4404540, 2254374], ![-73985427, 5669121, -2901624]]
    hw := by decide
    g := ![![![-141, -868, -504], ![-336, 0, 73]], ![![581, 328, 150], ![303, 0, -28]]]
    h := ![![![2985653473, -154549503736, 12203531886], ![-2762931252, -394580613828, 0]], ![![-3842860023, 198921984355, -15707269970], ![3556192444, 507868073294, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {3} * I97N1 =  Ideal.span {B.equivFun.symm ![19160629, -1468180, 751458]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E97RS1 


noncomputable def E103RS1 : RelationCertificate Table 9 ![![103, 0, 0], ![30, 1, 0]]
  ![-16010, -1189, 1356] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![927, 0, 0], ![270, 9, 0]]
    hsu := by decide
    w := ![![-144090, -10701, 12204], ![-230661, -42462, 3213]]
    hw := by decide
    g := ![![![-50319240, -208083178, -161488429], ![-45484459, 482474702, -276]], ![![-14065313, -61165441, -47360549], ![-13047403, 141595838, -81]]]
    h := ![![![9376432, 333385497, 33344358], ![5967800, -1144822506, 0]], ![![14989023, 532944868, 53303757], ![9540018, -1830095538, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {9} * I103N1 =  Ideal.span {B.equivFun.symm ![-16010, -1189, 1356]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS1 


noncomputable def E109RS1 : RelationCertificate Table 3 ![![109, 0, 0], ![-42, 1, 0]]
  ![457280, -35039, 17934] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![327, 0, 0], ![-126, 3, 0]]
    hsu := by decide
    w := ![![1371840, -105117, 53802], ![-1765707, 135297, -69249]]
    hw := by decide
    g := ![![![5327090, 167989, -97423], ![1831694, 0, 146020]], ![![-1966294, -62009, 35956], ![-676099, 0, -53900]]]
    h := ![![![4486529, -253893083, 18138021], ![-4057962, -659008785, 0]], ![![-5774600, 326787958, -23345602], ![5223167, 848215845, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {3} * I109N1 =  Ideal.span {B.equivFun.symm ![457280, -35039, 17934]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS1 


noncomputable def E127RS1 : RelationCertificate Table 9 ![![127, 0, 0], ![57, 1, 0]]
  ![302, -23, 12] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![1143, 0, 0], ![513, 9, 0]]
    hsu := by decide
    w := ![![2718, -207, 108], ![-279, 18, -9]]
    hw := by decide
    g := ![![![377305645468, 2195150327606, 1680660073177], ![411596989947, -5041982356318, 1282072]], ![![171502565561, 997795600200, 763936394405], ![187089540277, -2291810154482, 582760]]]
    h := ![![![-140359, -12031290, -633291], ![-157604, 26809323, 0]], ![![14360, 1234815, 64997], ![16277, -2751540, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {9} * I127N1 =  Ideal.span {B.equivFun.symm ![302, -23, 12]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E127RS1 


noncomputable def E131RS0 : RelationCertificate Table 3 ![![131, 0, 0], ![-62, 1, 0]]
  ![-7, -2, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![393, 0, 0], ![-186, 3, 0]]
    hsu := by decide
    w := ![![-21, -6, 0], ![-9, -9, -6]]
    hw := by decide
    g := ![![![-9534, -307, 176], ![-3277, 0, -262]], ![![4547, 146, -84], ![1565, 0, 125]]]
    h := ![![![54, -3410, 165], ![-2, -7205, 0]], ![![43, -1406, 68], ![43, -2970, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N0 : Ideal.span {3} * I131N0 =  Ideal.span {B.equivFun.symm ![-7, -2, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E131RS0 


noncomputable def E131RS1 : RelationCertificate Table 3 ![![131, 0, 0], ![-39, 1, 0]]
  ![41937044, -3213419, 1644723] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![393, 0, 0], ![-117, 3, 0]]
    hsu := by decide
    w := ![![125811132, -9640257, 4934169], ![-161932581, 12408057, -6350811]]
    hw := by decide
    g := ![![![64438, 1051, -1442], ![21830, 0, 2096]], ![![-19449, -413, 369], ![-6620, 0, -632]]]
    h := ![![![-403444043, 18806127624, -1446769359], ![263667613, 63176143584, 0]], ![![519276336, -24205527258, 1862149181], ![-339368607, -81314553216, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {3} * I131N1 =  Ideal.span {B.equivFun.symm ![41937044, -3213419, 1644723]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E131RS1 


noncomputable def E131RS2 : RelationCertificate Table 3 ![![131, 0, 0], ![-31, 1, 0]]
  ![44137, -3382, 1731] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![393, 0, 0], ![-93, 3, 0]]
    hsu := by decide
    w := ![![132411, -10146, 5193], ![-170427, 13059, -6684]]
    hw := by decide
    g := ![![![14269343, 450406, -260713], ![4906586, 0, 391096]], ![![-3352451, -105817, 61254], ![-1152756, 0, -91884]]]
    h := ![![![-217567, 7555372, -731235], ![109218, 31931172, 0]], ![![280060, -9724566, 941177], ![-140456, -41098805, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N2 : Ideal.span {3} * I131N2 =  Ideal.span {B.equivFun.symm ![44137, -3382, 1731]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E131RS2 
