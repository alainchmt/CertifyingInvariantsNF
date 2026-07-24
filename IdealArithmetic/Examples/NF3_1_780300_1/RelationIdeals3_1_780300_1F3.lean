import IdealArithmetic.Examples.NF3_1_780300_1.PrimesBelow3_1_780300_1F3
import IdealArithmetic.Examples.NF3_1_780300_1.ClassGroupData3_1_780300_1

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 66 ![![149, 0, 0], ![-44, 1, 0]]
  ![3, 4, 1] ![![66, 0, 0], ![-20, 4, 2]] where
    su := ![![9834, 0, 0], ![-2904, 66, 0]]
    hsu := by decide
    w := ![![198, 264, 66], ![1980, 0, 66]]
    hw := by decide
    g := ![![![306695743, -14057714, 22522040], ![-93107583, -65011973, 0]], ![![-89304078, 4093343, -6557999], ![27111215, 18930275, 0]]]
    h := ![![![10071, -220, -1], ![34104, 30, 0]], ![![100710, -2412, 14], ![341040, -417, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {66} * I149N1 =  Ideal.span {B.equivFun.symm ![3, 4, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E149RS1 


noncomputable def E157RS0 : RelationCertificate Table 18 ![![157, 0, 0], ![-69, 1, 0]]
  ![-4, -1, 1] ![![18, 0, 0], ![-6, 0, 3]] where
    su := ![![2826, 0, 0], ![-1242, 18, 0]]
    hsu := by decide
    w := ![![-72, -18, 18], ![-486, 108, -18]]
    hw := by decide
    g := ![![![-4005, 54, -216], ![1299, 157, 0]], ![![1787, -24, 96], ![-577, -70, 0]]]
    h := ![![![-160, 30, -2], ![-364, 63, 0]], ![![-1011, 56, -3], ![-2300, 94, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N0 : Ideal.span {18} * I157N0 =  Ideal.span {B.equivFun.symm ![-4, -1, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E157RS0 


noncomputable def E157RS1 : RelationCertificate Table 66 ![![157, 0, 0], ![-45, 1, 0]]
  ![-371, -40, -21] ![![66, 0, 0], ![-20, 4, 2]] where
    su := ![![10362, 0, 0], ![-2970, 66, 0]]
    hsu := by decide
    w := ![![-24486, -2640, -1386], ![-20460, -2112, -1122]]
    hw := by decide
    g := ![![![-7387, 338, -545], ![2266, 1570, 0]], ![![2135, -99, 156], ![-623, -452, 0]]]
    h := ![![![-1058, 49, -3], ![-3683, 90, 0]], ![![-910, 28, -1], ![-3168, 28, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {66} * I157N1 =  Ideal.span {B.equivFun.symm ![-371, -40, -21]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E157RS1 


noncomputable def E157RS2 : RelationCertificate Table 2576816 ![![157, 0, 0], ![-43, 1, 0]]
  ![29368, -5180, 927] ![![2576816, 0, 0], ![-469552, 8, 0]] where
    su := ![![404560112, 0, 0], ![-110803088, 2576816, 0]]
    hsu := by decide
    w := ![![75675932288, -13347906880, 2388708432], ![-13788542416, 2432514304, -435481904]]
    hw := by decide
    g := ![![![143053651084475, 261263347605353767676, -22256393124321996], ![785052426510573, 1433765747626072711052, 0]], ![![143076570978066970394117, 261305206997657727481470683816, -22259959024780675787664601], ![785178206719210265067739, 1433995464359981046511668662275, 0]]]
    h := ![![![4026862625442, -98923569349, 613442016], ![14702730980582, -19262079117, 0]], ![![-733715056586, 18024382472, -111772282], ![-2678913113457, 3509649621, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N2 : Ideal.span {2576816} * I157N2 =  Ideal.span {B.equivFun.symm ![29368, -5180, 927]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E157RS2 


noncomputable def E167RS1 : RelationCertificate Table 7730448 ![![167, 0, 0], ![-43, 1, 0]]
  ![-28568, -445, 546] ![![7730448, 0, 0], ![-2137424, 16, 8]] where
    su := ![![1290984816, 0, 0], ![-332409264, 7730448, 0]]
    hsu := by decide
    w := ![![-220843438464, -3440049360, 4220824608], ![61062808752, 950845104, -1167297648]]
    hw := by decide
    g := ![![![-2137783, 3992133437, -149420], ![1455117, 14438398730, 0]], ![![768528, -1002678653, 37528], ![472139, -3626400368, 0]]]
    h := ![![![-11308301810906, 276703465289, -1595314212], ![-43918288427738, 53283494790, 0]], ![![3126724907255, -76508005392, 441101472], ![12143326965202, -14732789195, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {7730448} * I167N1 =  Ideal.span {B.equivFun.symm ![-28568, -445, 546]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E167RS1 


noncomputable def E173RS1 : RelationCertificate Table 22 ![![173, 0, 0], ![-81, 1, 0]]
  ![6, -3, 2] ![![22, 0, 0], ![8, 0, 1]] where
    su := ![![3806, 0, 0], ![-1782, 22, 0]]
    hsu := by decide
    w := ![![132, -66, 44], ![-462, 44, 22]]
    hw := by decide
    g := ![![![106599599, 5678417, -1758344], ![38683571, -15615645, 0]], ![![-49727429, -2648913, 820246], ![-18045413, 7284510, 0]]]
    h := ![![![354, 12, -1], ![756, 35, 0]], ![![-672, 57, -3], ![-1435, 104, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {22} * I173N1 =  Ideal.span {B.equivFun.symm ![6, -3, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E173RS1 


noncomputable def E179RS1 : RelationCertificate Table 7730448 ![![179, 0, 0], ![29, 1, 0]]
  ![105286, -5497, -3027] ![![7730448, 0, 0], ![-2137424, 16, 8]] where
    su := ![![1383750192, 0, 0], ![224182992, 7730448, 0]]
    hsu := by decide
    w := ![![813907948128, -42494272656, -23400066096], ![-225056532624, 11750280960, 6470384976]]
    hw := by decide
    g := ![![![-51826550, 88088003973, -3296994], ![15270047, 318588981120, 0]], ![![-9884665, 17022323364, -637119], ![3422487, 61564848930, 0]]]
    h := ![![![17689377362904, 630779470710, 3586369122], ![-109186156822570, -128392015173, 0]], ![![-4891351584736, -174419036947, -991679467], ![30191445987539, 35502125086, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {7730448} * I179N1 =  Ideal.span {B.equivFun.symm ![105286, -5497, -3027]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E179RS1 


noncomputable def E191RS1 : RelationCertificate Table 31944 ![![191, 0, 0], ![-50, 1, 0]]
  ![-3318, -46, 203] ![![31944, 0, 0], ![2656, 9748, 1316]] where
    su := ![![6101304, 0, 0], ![-1597200, 31944, 0]]
    hsu := by decide
    w := ![![-105990192, -1469424, 6484632], ![317299752, -23383008, -6069360]]
    hw := by decide
    g := ![![![-6445293558108764, 95092512549255, -1391158905608134], ![-564190552139527, 926993328833850, 0]], ![![65327489481416378646280, -963828110768529092460, 14100353685015202526740], ![5718459838728721725530, -9395715865036779386643, 0]]]
    h := ![![![-5870260598, 124198392, -679317], ![-22424395418, 25949950, 0]], ![![17577191963, -371880252, 2033640], ![67144873100, -77685086, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {31944} * I191N1 =  Ideal.span {B.equivFun.symm ![-3318, -46, 203]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E191RS1 
