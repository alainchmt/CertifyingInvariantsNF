import IdealArithmetic.Examples.NF3_1_344763_1.PrimesBelow3_1_344763_1F2
import IdealArithmetic.Examples.NF3_1_344763_1.ClassGroupData3_1_344763_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 5 ![![83, 0, 0], ![19, 1, 0]]
  ![-136640, -28263, -5846] ![![5, 0, 0], ![-1, 2, 1]] where
    su := ![![415, 0, 0], ![95, 5, 0]]
    hsu := by decide
    w := ![![-683200, -141315, -29230], ![-4378275, -905615, -187320]]
    hw := by decide
    g := ![![![-1604, -40, -7], ![306, 0, 0]], ![![-297, -22, 3], ![52, 0, 0]]]
    h := ![![![-896636, -50306, -221], ![3909692, 12497, 0]], ![![-5746040, -322340, -1414], ![25055035, 79898, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {5} * I83N1 =  Ideal.span {B.equivFun.symm ![-136640, -28263, -5846]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 5 ![![89, 0, 0], ![31, 1, 0]]
  ![82347, -13610, -708] ![![5, 0, 0], ![-1, 2, 1]] where
    su := ![![445, 0, 0], ![155, 5, 0]]
    hsu := by decide
    w := ![![411735, -68050, -3540], ![-1780285, 98300, 55835]]
    hw := by decide
    g := ![![![-1118474347, -275397994, -68667202], ![99802234, 0, 0]], ![![-450337837, -110885099, -27647876], ![40183958, 0, 0]]]
    h := ![![![553758, 19973, 66], ![-1587165, -6582, 0]], ![![-2396620, -86957, -197], ![6869133, 28700, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {5} * I89N1 =  Ideal.span {B.equivFun.symm ![82347, -13610, -708]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E89RS1 


noncomputable def E103RS0 : RelationCertificate Table 10 ![![103, 0, 0], ![33, 1, 0]]
  ![-3313, 1570, -183] ![![10, 0, 0], ![-1, -3, 1]] where
    su := ![![1030, 0, 0], ![330, 10, 0]]
    hsu := by decide
    w := ![![-33130, 15700, -1830], ![242760, -12310, -7840]]
    hw := by decide
    g := ![![![4282452, 713323, 247610], ![-617479, 0, 0]], ![![1573057, 262024, 90953], ![-226810, 0, 0]]]
    h := ![![![-22798, -781, -5], ![71057, 332, 0]], ![![167142, 5594, 9], ![-520950, -1711, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {10} * I103N0 =  Ideal.span {B.equivFun.symm ![-3313, 1570, -183]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 10 ![![103, 0, 0], ![-27, 1, 0]]
  ![981, 203, 42] ![![10, 0, 0], ![-1, -3, 1]] where
    su := ![![1030, 0, 0], ![-270, 10, 0]]
    hsu := by decide
    w := ![![9810, 2030, 420], ![7720, 1600, 330]]
    hw := by decide
    g := ![![![-107, 21, 0], ![7, 0, 0]], ![![29, -6, 0], ![0, 0, 0]]]
    h := ![![![13941, -530, 1], ![53146, -61, 0]], ![![11002, -424, 1], ![41942, -70, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {10} * I103N1 =  Ideal.span {B.equivFun.symm ![981, 203, 42]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 10 ![![107, 0, 0], ![-43, 1, 0]]
  ![-8, -3, 1] ![![10, 0, 0], ![-1, -3, 1]] where
    su := ![![1070, 0, 0], ![-430, 10, 0]]
    hsu := by decide
    w := ![![-80, -30, 10], ![-670, 140, 0]]
    hw := by decide
    g := ![![![40, 8, 2], ![-3, 0, 0]], ![![-14, -2, -1], ![4, 0, 0]]]
    h := ![![![16, 0, 0], ![40, 1, 0]], ![![-210, 48, -1], ![-521, 107, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {10} * I107N1 =  Ideal.span {B.equivFun.symm ![-8, -3, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E107RS1 


noncomputable def E109RS0 : RelationCertificate Table 2 ![![109, 0, 0], ![15, 1, 0]]
  ![1224285503, 253234706, 52379789] ![![2, 0, 0], ![1, 1, 1]] where
    su := ![![218, 0, 0], ![30, 2, 0]]
    hsu := by decide
    w := ![![2448571006, 506469412, 104759578], ![35758723438, 7396436366, 1529899998]]
    hw := by decide
    g := ![![![-255881, 76913, 38820], ![-70071, 0, 0]], ![![-31524, 7681, 5492], ![-9174, 0, 0]]]
    h := ![![![25557537512, 1744818057, 3107733], ![-185636486887, -286363108, 0]], ![![373240111856, 25481175088, 45385073], ![-2711019522039, -4182022958, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {2} * I109N0 =  Ideal.span {B.equivFun.symm ![1224285503, 253234706, 52379789]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 10 ![![109, 0, 0], ![21, 1, 0]]
  ![-238377949, -49306775, -10198754] ![![10, 0, 0], ![-1, -3, 1]] where
    su := ![![1090, 0, 0], ![210, 10, 0]]
    hsu := by decide
    w := ![![-2383779490, -493067750, -101987540], ![-1875910020, -388018580, -80258870]]
    hw := by decide
    g := ![![![24261, 5715, -2074], ![-4339, 0, 0]], ![![2092, 1381, -353], ![-658, 0, 0]]]
    h := ![![![-1091134537, -54325532, -189687], ![5652156504, 10477129, 0]], ![![-858665928, -42751363, -149274], ![4447952150, 8244979, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {10} * I109N1 =  Ideal.span {B.equivFun.symm ![-238377949, -49306775, -10198754]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 5 ![![109, 0, 0], ![-36, 1, 0]]
  ![-34, 7, 0] ![![5, 0, 0], ![-1, 2, 1]] where
    su := ![![545, 0, 0], ![-180, 5, 0]]
    hsu := by decide
    w := ![![-170, 35, 0], ![825, -75, -20]]
    hw := by decide
    g := ![![![-227, -56, -14], ![21, 0, 0]], ![![66, 14, 3], ![-1, 0, 0]]]
    h := ![![![-6154, 207, -1], ![-18632, 109, 0]], ![![30081, -909, 2], ![91074, -222, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {5} * I109N2 =  Ideal.span {B.equivFun.symm ![-34, 7, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E109RS2 


noncomputable def E131RS1 : RelationCertificate Table 2 ![![131, 0, 0], ![32, 1, 0]]
  ![-35866591, -7418748, -1534515] ![![2, 0, 0], ![1, 1, 1]] where
    su := ![![262, 0, 0], ![64, 2, 0]]
    hsu := by decide
    w := ![![-71733182, -14837496, -3069030], ![-1047585310, -216685534, -44819854]]
    hw := by decide
    g := ![![![-46503, 15029, 6638], ![-12415, 0, 0]], ![![-10994, 3263, 1683], ![-3021, 0, 0]]]
    h := ![![![-1327429973, -44872411, -116156], ![5433045621, 13681921, 0]], ![![-19385674213, -655312728, -1696328], ![79343735289, 199809041, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {2} * I131N1 =  Ideal.span {B.equivFun.symm ![-35866591, -7418748, -1534515]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 2 ![![137, 0, 0], ![58, 1, 0]]
  ![643, -133, 0] ![![2, 0, 0], ![1, 1, 1]] where
    su := ![![274, 0, 0], ![116, 2, 0]]
    hsu := by decide
    w := ![![1286, -266, 0], ![-14386, 510, 510]]
    hw := by decide
    g := ![![![-169821, -5856, 28059], ![-73807, 0, 0]], ![![-77888, -2686, 12869], ![-33851, 0, 0]]]
    h := ![![![6035, 103, 0], ![-14244, 0, 0]], ![![-68429, -1401, -2], ![161510, 529, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {2} * I137N1 =  Ideal.span {B.equivFun.symm ![643, -133, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E137RS1 
