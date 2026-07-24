import IdealArithmetic.Examples.NF3_1_808623_1.PrimesBelow3_1_808623_1F2
import IdealArithmetic.Examples.NF3_1_808623_1.ClassGroupData3_1_808623_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 25 ![![83, 0, 0], ![-40, 1, 0]]
  ![12111, 2208, 815] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![2075, 0, 0], ![-1000, 25, 0]]
    hsu := by decide
    w := ![![302775, 55200, 20375], ![151950, 27700, 10225]]
    hw := by decide
    g := ![![![-380710010442, 570306632573, 951016645035], ![7583864901, -4755083225228, -317]], ![![177744737776, -266263035056, -444007773769], ![-3540731878, 2220038868870, 148]]]
    h := ![![![-29912979, -630838275, 82994245], ![6815481, -1377704304, 0]], ![![-15012054, -316591214, 41651323], ![3420430, -691411880, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {25} * I83N1 =  Ideal.span {B.equivFun.symm ![12111, 2208, 815]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS1 


noncomputable def E97RS0 : RelationCertificate Table 25 ![![97, 0, 0], ![23, 1, 0]]
  ![-56917, -10376, -3830] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![2425, 0, 0], ![575, 25, 0]]
    hsu := by decide
    w := ![![-1422925, -259400, -95750], ![-714075, -130175, -48050]]
    hw := by decide
    g := ![![![58467158193, -87597357440, -146072357400], ![-1165207954, 730362024658, 1188152]], ![![14318487731, -21452414067, -35772822222], ![-285357044, 178864169308, 290976]]]
    h := ![![![-1039816, 13315267, 2662810], ![-109275, -51659280, 0]], ![![-521834, 6682080, 1336294], ![-54767, -25924488, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {25} * I97N0 =  Ideal.span {B.equivFun.symm ![-56917, -10376, -3830]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E97RS0 


noncomputable def E97RS1 : RelationCertificate Table 25 ![![97, 0, 0], ![26, 1, 0]]
  ![-22442, -1351, 1695] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![2425, 0, 0], ![650, 25, 0]]
    hsu := by decide
    w := ![![-561050, -33775, 42375], ![280275, -7850, -8450]]
    hw := by decide
    g := ![![![39221347907, -58754881961, -97976753273], ![-781341349, 489883568688, 483]], ![![10637604602, -15935599147, -26573405974], ![-211919757, 132866953344, 131]]]
    h := ![![![-225996, 3261717, 582420], ![-26848, -11298609, 0]], ![![113039, -1631986, -291404], ![13568, 5653170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {25} * I97N1 =  Ideal.span {B.equivFun.symm ![-22442, -1351, 1695]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E97RS1 


noncomputable def E97RS2 : RelationCertificate Table 25 ![![97, 0, 0], ![48, 1, 0]]
  ![4171629, 760487, 280710] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![2425, 0, 0], ![1200, 25, 0]]
    hsu := by decide
    w := ![![104290725, 19012175, 7017750], ![52336325, 9540900, 3521725]]
    hw := by decide
    g := ![![![-565402374452018, 846977262134971, 1412379636591721], ![11262995507326, -7061898182958430, -768]], ![![-282701187230739, 423488631074757, 706189818307979], ![5631497753772, -3530949091539838, -384]]]
    h := ![![![17772969117, -490594967745, -49055641890], ![3737191352, 951679508808, 0]], ![![8919027905, -246195792338, -24617644733], ![1875438722, 477582335994, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N2 : Ideal.span {25} * I97N2 =  Ideal.span {B.equivFun.symm ![4171629, 760487, 280710]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E97RS2 


noncomputable def E103RS0 : RelationCertificate Table 5 ![![103, 0, 0], ![5, 1, 0]]
  ![-90917466, -16574233, -6117860] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![515, 0, 0], ![25, 5, 0]]
    hsu := by decide
    w := ![![-454587330, -82871165, -30589300], ![-1140630220, -207936625, -76753305]]
    hw := by decide
    g := ![![![-41219, 1570, 1343], ![-7926, 0, 228]], ![![-92, -194, 65], ![-56, 0, 18]]]
    h := ![![![-1200488238, 4201598800, 3001076295], ![-17483890, -61823395249, 0]], ![![-3012211455, 10542464005, 7530166568], ![-43869809, -155124501433, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {5} * I103N0 =  Ideal.span {B.equivFun.symm ![-90917466, -16574233, -6117860]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 5 ![![103, 0, 0], ![41, 1, 0]]
  ![21, -2, 0] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![515, 0, 0], ![205, 5, 0]]
    hsu := by decide
    w := ![![105, -10, 0], ![25, 15, -10]]
    hw := by decide
    g := ![![![-484, -13, 2], ![-99, 0, 14]], ![![-413, -11, 2], ![-82, 0, 12]]]
    h := ![![![18289, -421432, -49000], ![3294, 1009400, 0]], ![![4314, -99630, -11584], ![803, 238630, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {5} * I103N1 =  Ideal.span {B.equivFun.symm ![21, -2, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 5 ![![103, 0, 0], ![-46, 1, 0]]
  ![2179, 132, -165] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![515, 0, 0], ![-230, 5, 0]]
    hsu := by decide
    w := ![![10895, 660, -825], ![-27290, 760, 825]]
    hw := by decide
    g := ![![![150182, 19695, 9272], ![33976, 0, -500]], ![![-52031, -6631, -3091], ![-11731, 0, 220]]]
    h := ![![![-870561, -20974367, 2383245], ![185213, -49094880, 0]], ![![2184760, 52635963, -5980845], ![-464677, 123205440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {5} * I103N2 =  Ideal.span {B.equivFun.symm ![2179, 132, -165]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS2 


noncomputable def E113RS1 : RelationCertificate Table 5 ![![113, 0, 0], ![29, 1, 0]]
  ![83593, 15239, 5625] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![565, 0, 0], ![145, 5, 0]]
    hsu := by decide
    w := ![![417965, 76195, 28125], ![1048740, 191185, 70570]]
    hw := by decide
    g := ![![![13115, 419, -59], ![2709, 0, -416]], ![![3478, 102, -14], ![716, 0, -109]]]
    h := ![![![-1561156, 24927062, 4020265], ![-179983, -90856864, 0]], ![![-3917160, 62545925, 10087478], ![-451708, -227974180, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {5} * I113N1 =  Ideal.span {B.equivFun.symm ![83593, 15239, 5625]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 5 ![![131, 0, 0], ![41, 1, 0]]
  ![-1487, -271, -100] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![655, 0, 0], ![205, 5, 0]]
    hsu := by decide
    w := ![![-7435, -1355, -500], ![-18645, -3400, -1255]]
    hw := by decide
    g := ![![![-68919657, -1636284, 405317], ![-14111187, 0, 2026606]], ![![-21822708, -518113, 128340], ![-4468163, 0, 641704]]]
    h := ![![![2359, -54050, -6285], ![458, 164647, 0]], ![![6001, -135540, -15761], ![876, 412888, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {5} * I131N1 =  Ideal.span {B.equivFun.symm ![-1487, -271, -100]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E131RS1 


noncomputable def E137RS0 : RelationCertificate Table 25 ![![137, 0, 0], ![22, 1, 0]]
  ![6334572, 1154791, 426255] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![3425, 0, 0], ![550, 25, 0]]
    hsu := by decide
    w := ![![158364300, 28869775, 10656375], ![79472125, 14487750, 5347700]]
    hw := by decide
    g := ![![![-3612698824645303, 5411851626323509, 9024550451304561], ![71966112067129, -45122752256533280, -50553]], ![![-571351395625192, 855888943335743, 1427240339013936], ![11381501908445, -7136201695071340, -7995]]]
    h := ![![![25201406898, -305924981941, -63731611500], ![1813912284, 1746246240351, 0]], ![![12646848809, -153522658863, -31982502341], ![910277541, 876320606925, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {25} * I137N0 =  Ideal.span {B.equivFun.symm ![6334572, 1154791, 426255]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 25 ![![137, 0, 0], ![56, 1, 0]]
  ![-841, 102, -15] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![3425, 0, 0], ![1400, 25, 0]]
    hsu := by decide
    w := ![![-21025, 2550, -375], ![-3700, -700, 525]]
    hw := by decide
    g := ![![![-174483489224055, 261377648300102, 435861132213198], ![3475766363047, -2179305660904680, 804828]], ![![-89097951575193, 133469436877035, 222567385740233], ![1774859412089, -1112836928618800, 410976]]]
    h := ![![![-4442265, 138382109, 11928985], ![-805695, -326854192, 0]], ![![-779644, 24286941, 2093613], ![-141409, -57364992, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {25} * I137N1 =  Ideal.span {B.equivFun.symm ![-841, 102, -15]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 25 ![![137, 0, 0], ![59, 1, 0]]
  ![62, 11, 5] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![3425, 0, 0], ![1475, 25, 0]]
    hsu := by decide
    w := ![![1550, 275, 125], ![925, 150, 50]]
    hw := by decide
    g := ![![![-199385, 307739, 512552], ![4354, -2562926, -822]], ![![-85382, 131781, 219487], ![1869, -1097506, -352]]]
    h := ![![![93, -3966, -325], ![87, 8906, 0]], ![![15, -2368, -194], ![146, 5316, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {25} * I137N2 =  Ideal.span {B.equivFun.symm ![62, 11, 5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E137RS2 
